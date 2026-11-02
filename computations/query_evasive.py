"""Routes to the evasiveness of G_t for every t, and where each one stops.

c_t is the center after t steps of Rule 30 (new x_j = x_{j-1} xor (x_j or x_{j+1})) as a Boolean function of the
2t + 1 cells x_{-t} .. x_t of an arbitrary row, and G_t is c_t with x_{-t} and x_{t-1} white, a function of the 2t - 1
cells x_{-t+1} .. x_{t-2}, x_t (`query_adversary.reduced_table`, variable 0 is u = x_{-t+1}). CornerOr proves that
D(c_t) = 2t + 1 if and only if every decision tree for G_t reads all its cells on some row. This is a query model for
an arbitrary row; it says nothing about the single black cell's column, where a tree reads nothing.

* Route 1, the derivative along u. Flipping x_{-t+1} changes c_t by t + (the parity of the cells (s, -t + 2 + s),
  s < t) for every row (`diagonal_table`, Lean `center_flip_second`). On G_t this is Q_t, a function of the other
  2t - 2 cells S (variable 0 is L = x_{-t+2}). Q_t flips with L on every row for odd t and ignores L for even t
  (Lean `second_derivative_flip`). `derivative_profile` and `derivative_sums` give the top real coefficient of
  Q'_t = Q_t with L white, on 2t - 3 cells, through the C program `query_evasive_sums.c` for large t. `u_last_games`
  plays the games on S: the tree reads u last (the case CornerOr leaves open), the GF(2) adversary of CornerOr, and an
  adversary that keeps both Q_t and one of the two u-restrictions evasive.
* Route 2, gates after restrictions. `structure` lists the cells with which a function flips on every row and the
  pairs of cells it reads through a gate of two inputs; `restriction_structure` does it for G_t and its restrictions
  to one cell, `merged_structure` for G_t with x_{t-3} black and the pair (x_{t-2}, x_t) merged into its AND (Lean
  `center_second_and`).
* Route 3, other measures. `approximate_degree` (linear programming), `automorphisms` (permutations and negations of
  cells that fix the function, the group of a topological criterion), `monotone_cells` (that criterion also needs a
  monotone function) and `linear_certificate_rank` (the subcube indicators of dimension at least 1 span every
  function with mu = 0, so mu is the only linear certificate).

    python -m computations.query_evasive --max-t 9 --structure 12 --sums 21 --threads 1   # about ten minutes
"""

from __future__ import annotations

import argparse
import functools
import itertools
import os
import shutil
import subprocess
import sys
import tempfile
from collections.abc import Callable
from pathlib import Path

import numpy as np
from scipy.optimize import linprog
from tqdm.auto import tqdm

from computations import query_adversary as qa
from computations import query_depth as qd
from computations.cone_screening import step_slices, variable_slices

HERE = Path(__file__).resolve().parent
LOW = 9  # cells bit-sliced in the C program


def derivative_table(t: int) -> np.ndarray:
    """Q_t = G_t with u = 0 xor G_t with u = 1, on the 2t - 2 cells x_{-t+2} .. x_{t-2}, x_t (variable 0 is L)."""
    g = qa.reduced_table(t)  # (2^(2t-1),), bit 0 of the index is u
    return (g[0::2] ^ g[1::2]).astype(np.uint8)  # (2^(2t-2),)


def diagonal_table(t: int) -> np.ndarray:
    """t + (the parity of the cells (s, -t + 2 + s), s < t) with x_{t-1} = 0, on the cells x_{-t+2} .. x_{t-2}, x_t
    in that order: the left edge of the cone of the cell (t - 1, 1), computed by running the rule on that cone."""
    n = 2 * t - 2
    v = variable_slices(n)  # n x (2^n,)
    cells: list[np.ndarray | np.bool_] = list(v[:-1]) + [np.bool_(False), v[-1]]  # x_{-t+2} .. x_t, 2t - 1 entries
    parity = np.full(1 << n, bool(t % 2))  # (2^n,)
    row = cells
    for _ in range(t):
        parity = parity ^ row[0]  # the left edge of the cone at this time
        row = step_slices(row, 1)  # (len - 2) entries
    return parity.astype(np.uint8)  # (2^n,)


def gf2_degree(table: np.ndarray, n: int) -> int:
    """The degree of the GF(2) normal form (-1 for the zero function)."""
    coef = qa.anf(table, n)  # (2^n,)
    support = np.nonzero(coef)[0]  # (k,)
    return max((int(s).bit_count() for s in support), default=-1)


def derivative_profile(t: int, exact: int = 13) -> dict[str, object]:
    """For Q_t: whether it depends on L and whether it flips with L on every row, its GF(2) degree, and for
    Q'_t = Q_t with L white (2t - 3 cells): mu, the GF(2) degree and the exact depth when 2t - 3 <= exact."""
    q = derivative_table(t)  # (2^(2t-2),)
    n = 2 * t - 2
    reduced = q[0::2]  # (2^(2t-3),)
    return {
        "depends_on_left": bool((q[0::2] != q[1::2]).any()),
        "flips_with_left": bool((q[0::2] != q[1::2]).all()),
        "degree": gf2_degree(q, n),
        "mu_reduced": qd.signed_sum(reduced, n - 1),
        "degree_reduced": gf2_degree(reduced, n - 1),
        "depth_reduced": qd.exact_depth(reduced, n - 1) if n - 1 <= exact else None,
    }


def previous_level_split(t: int) -> bool:
    """Q'_t xor G_{t-1}, with G_{t-1} read on the same cells shifted one to the right (x_{-t+3} .. x_{t-2}, x_t), does
    not depend on x_t (t >= 3): the last cell of the diagonal is the cell (t - 1, 1), a copy of c_{t-1} whose leftmost
    and corner cells are white, and the earlier cells of the diagonal have cones left of x_t."""
    reduced = derivative_table(t)[0::2]  # (2^(2t-3),), Q'_t
    rest = reduced ^ qa.reduced_table(t - 1)  # (2^(2t-3),)
    half = 1 << (2 * t - 4)
    return bool((rest[:half] == rest[half:]).all())  # x_t is the last variable


@functools.cache
def _binary() -> Path:
    """Compile computations/query_evasive_sums.c once per process into a temporary directory."""
    cc = shutil.which("cc") or shutil.which("gcc")
    assert cc, "a C compiler is needed for the sums"
    out = Path(tempfile.mkdtemp(prefix="query_evasive_")) / "query_evasive_sums"
    subprocess.run([cc, "-O3", "-march=native", "-fopenmp", "-w", str(HERE / "query_evasive_sums.c"), "-o", str(out)],
                   check=True)
    return out


def derivative_sums(t: int, threads: int = 1, split: int = 6) -> int:
    """mu(Q'_t) = sum over the 2t - 3 cells y of (-1)^{|y|} Q'_t(y), by the C program for 2t - 3 > LOW and from the
    truth table below."""
    if 2 * t - 3 <= LOW:
        return qd.signed_sum(derivative_table(t)[0::2], 2 * t - 3)
    run = subprocess.run([str(_binary()), str(t), str(split)], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                         text=True, check=True, env={**os.environ, "OMP_NUM_THREADS": str(threads)})
    return int(run.stdout.split()[1])


def subcube_depths(table: np.ndarray, n: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """(depth, low, free) over the 3^n subcubes (axis k is variable n - 1 - k, index 2 meaning free): the least depth
    of a tree for the function on the subcube, its least value there, and the number of free cells. The program of
    `query_depth.exact_depth`, keeping every subcube."""
    cube = table.astype(np.int8).reshape([2] * n)  # (2,)*n
    low, high = cube, cube.copy()
    for axis in range(n):
        l0, l1 = np.take(low, 0, axis=axis), np.take(low, 1, axis=axis)  # (3,)*axis + (2,)*(n-axis-1)
        h0, h1 = np.take(high, 0, axis=axis), np.take(high, 1, axis=axis)
        low = np.stack([l0, l1, np.minimum(l0, l1)], axis=axis)  # (3,)*(axis+1) + (2,)*(n-axis-1)
        high = np.stack([h0, h1, np.maximum(h0, h1)], axis=axis)
    constant = low == high  # (3,)*n
    depth = np.where(constant, 0, n + 1).astype(np.int8)  # (3,)*n
    for _ in range(n):
        new = depth.copy()  # (3,)*n
        for axis in range(n):
            free = [slice(None)] * n
            free[axis] = 2
            candidate = 1 + np.maximum(np.take(depth, 0, axis=axis), np.take(depth, 1, axis=axis))  # (3,)*(n-1)
            new[tuple(free)] = np.minimum(new[tuple(free)], candidate)
        new[constant] = 0
        depth = new
    count = np.zeros([3] * n, dtype=np.int8)  # (3,)*n
    for axis in range(n):
        shape = [1] * n
        shape[axis] = 3
        count += (np.arange(3) == 2).astype(np.int8).reshape(shape)
    return depth, low, count


def subcube_parity(table: np.ndarray, n: int) -> np.ndarray:
    """The parity of the number of 1-rows in each of the 3^n subcubes, the GF(2) coefficient of the product of its
    free cells in the restricted function (same layout as `subcube_depths`)."""
    cube = table.astype(np.uint8).reshape([2] * n)  # (2,)*n
    for axis in range(n):
        a0, a1 = np.take(cube, 0, axis=axis), np.take(cube, 1, axis=axis)
        cube = np.stack([a0, a1, a0 ^ a1], axis=axis)  # (3,)*(axis+1) + (2,)*(n-axis-1)
    return cube  # (3,)*n


def _close(start: np.ndarray, n: int, step: Callable[[np.ndarray, int], np.ndarray]) -> np.ndarray:
    """Iterate W = start and (for every free cell, step(W, axis) on its slice) n times, so every subcube is final."""
    win = start.copy()  # (3,)*n
    for _ in range(n):
        ok = np.ones_like(win)  # (3,)*n
        for axis in range(n):
            free = [slice(None)] * n
            free[axis] = 2
            ok[tuple(free)] &= step(win, axis)
        win = start & ok
    return win


def u_last_games(t: int) -> dict[str, bool]:
    """The games on the 2t - 2 cells S other than u (P_a = G_t with u = a, Q = P_0 xor P_1 = Q_t):
    `u_last`: every tree for G_t that reads u last reads all 2t - 1 cells on some row (the tree must find (P_0, P_1),
      the adversary wins at a full row of S with Q = 1);
    `derivative_evasive`: Q_t needs all of S (this alone wins the u-last game);
    `joint_root`, `joint_game`: Q_t and one of P_0, P_1 need all of S at the start, and an adversary keeps both;
    `gf2_game`: CornerOr's adversary (keep the GF(2) coefficient of the product of the free cells of S in P_0 equal to
      1; it forces each answer) wins against every tree, reading u last or not."""
    g = qa.reduced_table(t)  # (2^(2t-1),)
    n = 2 * t - 2
    p0, p1 = g[0::2], g[1::2]  # (2^n,) each
    q = p0 ^ p1  # (2^n,)
    root = (2,) * n
    d0, _, free = subcube_depths(p0, n)  # (3,)*n each
    d1, _, _ = subcube_depths(p1, n)
    dq, lowq, _ = subcube_depths(q, n)
    ev_p = (d0 == free) | (d1 == free)  # (3,)*n
    ev_q = (dq == free) & ((free > 0) | (lowq == 1))  # (3,)*n, at a full row Q must be 1
    pair_constant = (d0 == 0) & (d1 == 0)  # (3,)*n, (P_0, P_1) fixed on the subcube

    def exists(win: np.ndarray, axis: int) -> np.ndarray:
        return np.take(win, 0, axis=axis) | np.take(win, 1, axis=axis)

    u_last = _close(np.where(free == 0, lowq == 1, ~pair_constant), n, exists)  # (3,)*n
    joint = ev_p & ev_q  # (3,)*n
    joint_game = _close(joint, n, exists)
    par0, parq = subcube_parity(p0, n), subcube_parity(q, n)  # (3,)*n each

    def forced(win: np.ndarray, axis: int) -> np.ndarray:
        top = np.take(parq, 0, axis=axis) == 1  # a Q-top cell: after it Q has full GF(2) degree, a win
        child = np.where(np.take(par0, 0, axis=axis) == 1, np.take(win, 0, axis=axis), np.take(win, 1, axis=axis))
        return top | child

    gf2_game = _close(free > 0, n, forced)  # a full row of S in this state has Q = 0, a loss
    return {"u_last": bool(u_last[root]), "derivative_evasive": bool(ev_q[root]), "joint_root": bool(joint[root]),
            "joint_game": bool(joint_game[root]), "gf2_game": bool(gf2_game[root])}


def structure(table: np.ndarray, n: int) -> tuple[list[int], list[tuple[int, int, tuple[int, ...]]]]:
    """(cells with which the function flips on every row, pairs (i, j) through which it factors by a gate of two
    inputs with the class of each cofactor at (x_i, x_j) = 00, 01, 10, 11, as `query_adversary.pair_gates`)."""
    cube = table.reshape([2] * n)  # (2,)*n, axis a is variable n - 1 - a
    flips = [v for v in range(n)
             if (np.take(cube, 0, axis=n - 1 - v) != np.take(cube, 1, axis=n - 1 - v)).all()]
    gates = []
    for i, j in itertools.combinations(range(n), 2):
        ai, aj = n - 1 - i, n - 1 - j  # aj < ai
        cofactors = [np.take(np.take(cube, a, axis=ai), b, axis=aj) for a in (0, 1) for b in (0, 1)]  # 4 x (2,)*(n-2)
        labels: list[np.ndarray] = []
        classes = []
        for c in cofactors:
            match = next((k for k, d in enumerate(labels) if np.array_equal(c, d)), None)
            if match is None:
                labels.append(c)
                match = len(labels) - 1
            classes.append(match)
            if len(labels) > 2:
                break
        if len(labels) <= 2:
            gates.append((i, j, tuple(classes)))
    return flips, gates


def cell_names(t: int) -> list[int]:
    """The cells of G_t in variable order: x_{-t+1} .. x_{t-2}, x_t."""
    return [-t + 1 + k for k in range(2 * t - 2)] + [t]


def restriction_structure(t: int, progress: bool = False) -> list[tuple[int | None, int | None, list[int],
                                                                        list[tuple[int, int, tuple[int, ...]]]]]:
    """For G_t (cell None) and each restriction of one cell x_k = b: the cells with which it flips on every row and its
    gate pairs, as cell names, for the restrictions where either is nonempty."""
    g = qa.reduced_table(t)  # (2^(2t-1),)
    n = 2 * t - 1
    names = cell_names(t)
    out = []
    flips, gates = structure(g, n)
    if flips or gates:
        out.append((None, None, [names[i] for i in flips], [(names[i], names[j], c) for i, j, c in gates]))
    tasks = [(k, b) for k in range(n) for b in (0, 1)]
    for k, b in tqdm(tasks, desc=f"t={t}", file=sys.stderr, disable=not progress, mininterval=5):
        r = qa.restrict_table(g, n, {k: b})  # (2^(n-1),)
        rest = [c for i, c in enumerate(names) if i != k]
        flips, gates = structure(r, n - 1)
        if flips or gates:
            out.append((names[k], b, [rest[i] for i in flips], [(rest[i], rest[j], c) for i, j, c in gates]))
    return out


def second_corner_holds(t: int) -> bool:
    """On the truth table of G_t (t >= 3): it ignores x_t whenever x_{t-3} != x_{t-2}, and with x_{t-3} black it
    reads (x_{t-2}, x_t) through their AND (the cofactors 00, 01, 10 agree)."""
    g = qa.reduced_table(t)  # (2^(2t-1),)
    n = 2 * t - 1
    names = cell_names(t)
    k3, k2, kt = names.index(t - 3), names.index(t - 2), names.index(t)
    index = np.arange(1 << n)  # (2^n,)
    bit = [(index >> k) & 1 for k in range(n)]  # n x (2^n,)
    shield = (bit[k3] != bit[k2]) & (g != g[index ^ (1 << kt)])  # (2^n,), a flip of x_t that moves G_t
    black = index[(bit[k3] == 1) & (bit[k2] == 0) & (bit[kt] == 0)]  # (2^(n-3),), x_{t-3} = 1 and the pair 00
    pair = [g[black | (a << k2) | (b << kt)] for a, b in ((0, 0), (0, 1), (1, 0))]  # 3 x (2^(n-3),)
    return bool(not shield.any() and (pair[0] == pair[1]).all() and (pair[0] == pair[2]).all())


def merged_structure(t: int, exact: int = 13) -> tuple[int | None, list[tuple[int | None, int | None, list[int],
                                                                                  list[tuple]]]]:
    """F_t = G_t with x_{t-3} black and x_t black, so that x_{t-2} carries the AND of the pair (2t - 3 cells): its exact
    depth (when 2t - 3 <= exact) and the structure of F_t and its one-cell restrictions, as `restriction_structure`."""
    g = qa.reduced_table(t)  # (2^(2t-1),)
    n = 2 * t - 1
    names = cell_names(t)
    f = qa.restrict_table(g, n, {names.index(t - 3): 1, names.index(t): 1})  # (2^(n-2),)
    rest = [c for c in names if c not in (t - 3, t)]
    m = n - 2
    out = []
    flips, gates = structure(f, m)
    if flips or gates:
        out.append((None, None, [rest[i] for i in flips], [(rest[i], rest[j], c) for i, j, c in gates]))
    for k in range(m):
        for b in (0, 1):
            r = qa.restrict_table(f, m, {k: b})  # (2^(m-1),)
            sub = [c for i, c in enumerate(rest) if i != k]
            flips, gates = structure(r, m - 1)
            if flips or gates:
                out.append((rest[k], b, [sub[i] for i in flips], [(sub[i], sub[j], c) for i, j, c in gates]))
    return (qd.exact_depth(f, m) if m <= exact else None), out


def approximate_degree(table: np.ndarray, n: int, eps: float = 1 / 3) -> int:
    """The least d such that a real polynomial of degree d is within eps of the function on every row, by linear
    programming over the characters of at most d cells."""
    index = np.arange(1 << n)  # (2^n,)
    f = table.astype(float)  # (2^n,)
    for d in range(n + 1):
        sets = [s for s in range(1 << n) if s.bit_count() <= d]
        chars = np.array([[(-1) ** (int(x) & s).bit_count() for s in sets] for x in index], dtype=float)  # (2^n, m)
        m = len(sets)
        # variables: m coefficients, then e; minimize e with |chars c - f| <= e
        a_ub = np.vstack([np.hstack([chars, -np.ones((1 << n, 1))]), np.hstack([-chars, -np.ones((1 << n, 1))])])
        b_ub = np.concatenate([f, -f])  # (2^(n+1),)
        cost = np.zeros(m + 1)
        cost[-1] = 1.0
        res = linprog(cost, A_ub=a_ub, b_ub=b_ub, bounds=[(None, None)] * m + [(0, None)], method="highs")
        if res.status == 0 and res.fun <= eps + 1e-9:
            return d
    return n


def automorphisms(table: np.ndarray, n: int) -> int:
    """The number of pairs (perm, neg) with f(x) = f(y), y_{perm[i]} = x_i xor neg[i]: the permutations and negations
    of cells that fix the function. Backtracking on the weights of pairs of cells, then a check of the table."""
    weights = qa.pair_weights(table, n)  # (n, n, 2, 2)
    index = np.arange(1 << n)  # (2^n,)
    perm = [0] * n
    neg = [0] * n
    used = [False] * n
    count = 0

    def fits(i: int) -> bool:
        return all(weights[i, j, a, b] == weights[perm[i], perm[j], a ^ neg[i], b ^ neg[j]]
                   for j in range(i + 1) for a in (0, 1) for b in (0, 1))

    def place(i: int) -> None:
        nonlocal count
        if i == n:
            y = np.zeros(1 << n, dtype=np.int64)  # (2^n,)
            for k in range(n):
                y |= (((index >> k) & 1) ^ neg[k]) << perm[k]
            count += int((table == table[y]).all())
            return
        for p in range(n):
            if used[p]:
                continue
            for s in (0, 1):
                perm[i], neg[i] = p, s
                if fits(i):
                    used[p] = True
                    place(i + 1)
                    used[p] = False

    place(0)
    return count


def monotone_cells(table: np.ndarray, n: int) -> list[int]:
    """The cells in which the function is monotone, increasing or decreasing, on every row."""
    index = np.arange(1 << n)  # (2^n,)
    out = []
    for i in range(n):
        low = index[((index >> i) & 1) == 0]  # (2^(n-1),)
        step = table[low | (1 << i)].astype(np.int8) - table[low].astype(np.int8)  # (2^(n-1),)
        if (step >= 0).all() or (step <= 0).all():
            out.append(i)
    return out


def linear_certificate_rank(n: int) -> int:
    """The rank of the indicator vectors of the subcubes of {0,1}^n with at least one free cell. It is 2^n - 1: they
    span the functions orthogonal to (-1)^{|x|}, so a linear functional that vanishes on every leaf of a tree of depth
    below n is a multiple of mu."""
    rows = []
    index = np.arange(1 << n)  # (2^n,)
    for code in itertools.product((0, 1, 2), repeat=n):
        if 2 not in code:
            continue
        member = np.ones(1 << n, dtype=bool)  # (2^n,)
        for k, c in enumerate(code):
            if c < 2:
                member &= ((index >> k) & 1) == c
        rows.append(member.astype(float))
    return int(np.linalg.matrix_rank(np.array(rows)))  # rows: (3^n - 2^n, 2^n)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-t", type=int, default=8, help="derivative profiles and games for t <= this")
    parser.add_argument("--structure", type=int, default=9, help="restriction structure for t <= this")
    parser.add_argument("--sums", type=int, default=17, help="mu(Q'_t) by the C program for t <= this")
    parser.add_argument("--threads", type=int, default=1, help="OpenMP threads of the C program")
    parser.add_argument("--adeg", type=int, default=5, help="approximate degree and automorphisms for t <= this")
    args = parser.parse_args()

    print("t  Q_t depends on L  flips with L  deg Q_t  mu(Q'_t)  deg Q'_t  D(Q'_t)  2t - 3  split by G_{t-1}")
    for t in range(2, args.max_t + 1):
        p = derivative_profile(t)
        print(t, p["depends_on_left"], p["flips_with_left"], p["degree"], p["mu_reduced"], p["degree_reduced"],
              p["depth_reduced"], 2 * t - 3, previous_level_split(t) if t >= 3 else None, flush=True)
    print("t  mu(Q'_t) by the C program")
    for t in tqdm(range(3, args.sums + 1), desc="sums", file=sys.stderr):
        print(t, derivative_sums(t, args.threads), flush=True)
    print("t  u-last game  Q_t evasive  joint at the start  joint game  GF(2) game")
    for t in tqdm(range(2, args.max_t + 1), desc="games", file=sys.stderr):
        r = u_last_games(t)
        print(t, r["u_last"], r["derivative_evasive"], r["joint_root"], r["joint_game"], r["gf2_game"], flush=True)
    print("t  second corner  restrictions of G_t with a flip cell or a gate: (cell, value, flip cells, gates)")
    for t in range(3, args.structure + 1):
        print(t, second_corner_holds(t), restriction_structure(t, progress=t >= 10), flush=True)
    print("t  D(F_t) of 2t - 3  structure of F_t and its one-cell restrictions")
    for t in range(3, min(args.structure, 9) + 1):
        depth, found = merged_structure(t)
        print(t, depth, 2 * t - 3, found, flush=True)
    print("t  cells of G_t in which it is monotone")
    for t in range(2, min(args.max_t, 8) + 1):
        print(t, [cell_names(t)[i] for i in monotone_cells(qa.reduced_table(t), 2 * t - 1)], flush=True)
    print("t  approximate degree of G_t (eps 1/3) of 2t - 1  automorphisms of G_t")
    for t in tqdm(range(2, args.adeg + 1), desc="approximate degree", file=sys.stderr):
        g = qa.reduced_table(t)
        print(t, approximate_degree(g, 2 * t - 1), 2 * t - 1, automorphisms(g, 2 * t - 1), flush=True)
    print("n  rank of the subcube indicators with a free cell, 2^n - 1")
    for n in range(1, 6):
        print(n, linear_certificate_rank(n), (1 << n) - 1)


if __name__ == "__main__":
    main()
