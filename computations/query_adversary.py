"""Adversaries for the decision-tree depth of the center as a function of its cone: where each route stops.

c_t is the center after t steps of Rule 30 (new x_j = x_{j-1} xor (x_j or x_{j+1})) as a Boolean function of the
2t + 1 cells x_{-t} .. x_t of an arbitrary row; g_t is c_t with x_{-t} = 0, a function of the 2t cells
x_{-t+1} .. x_t (variable k is x_{-t+1+k}). QueryDepth proves D(c_t) = D(g_t) + 1 and D(c_t) >= 2t, and computes
D(c_t) = 2t + 1 for t <= 17 from the top real coefficient mu(c_t) = 2 nu(g_t), nu(g) = sum_y (-1)^{|y|} g(y).

* `kernel_sums` computes nu and the restricted sums R[k, b] (the top coefficient of g with variable k also fixed to b,
  up to sign) of g_t on any subcube with the C program `query_adversary_sums.c` (bit-sliced over 512 rows, Gray code
  over the rest, OpenMP), the same quantities as `query_depth.subcube_sums` in the same convention. `certificate`
  repeats the certificate of `query_depth` on it, for t <= 21 (each t costs about four times the last).
* `corner_or_holds` checks on the truth table that c_t depends on x_{t-1}, x_t only through x_{t-1} or x_t (proved in
  Lean, `CornerOr`), and `corner_restrictions` that the corner restrictions have top coefficients 0 (black) and nu
  (white), its consequence for the certificates.
* `restriction_isomorphisms` is route (i): the restrictions of c_{t+1} to two fixed cells that equal c_t up to a
  permutation of the cells, negations of cells and negation of the value, and the number of those restrictions that
  need all their cells.
* `pair_gates` lists the pairs of cells through which a function factors by a gate of two inputs: for c_t only the
  corner, and none for G_t (`reduced_table`, c_t with x_{-t} and x_{t-1} white), so the corner step does not repeat.
* `covering_pairs` is route (iii): nu(g_t) = 2 P (mod 4), with P the number of unordered pairs of monomials of the
  GF(2) normal form of g_t whose union is all 2t cells.

    python -m computations.query_adversary --max-t 21 --threads 3   # mu(c_t) and certificates, about 25 minutes
    python -m computations.query_adversary --routes 5 --pairs 10 --max-t 20   # every route, about 20 minutes
"""

from __future__ import annotations

import argparse
import functools
import itertools
import os
import subprocess
import sys
from pathlib import Path

import numpy as np
from tqdm.auto import tqdm

from computations import query_depth as qd
from computations.cone_screening import cone_table

LOW = 9  # cells bit-sliced in the C program


def _binary() -> Path:
    """computations/query_adversary_sums.c, compiled once and kept for later processes (`seed_onsets.compiled`)."""
    from computations.seed_onsets import compiled
    return compiled("query_adversary_sums", ("-O3", "-march=native", "-fopenmp", "-w"))


def kernel_sums(t: int, fixed: dict[int, int], threads: int = 1, split: int = 8,
                progress: bool = False) -> tuple[int, np.ndarray]:
    """nu = sum over the free y of (-1)^{|y|} g_t(y) on the subcube where variable k equals fixed[k], and R[k, b], the
    same sum with free variable k also fixed to b and the sign (-1)^{|y| - b} (0 for fixed k), as in
    `query_depth.subcube_sums`. Uses the C program for 2t > LOW and `subcube_sums` below. Results are kept for the
    arguments asked again, as read-only arrays."""
    return _sums(t, tuple(sorted(fixed.items())), threads, split, progress)


@functools.lru_cache(maxsize=256)
def _sums(t: int, fixed: tuple[tuple[int, int], ...], threads: int, split: int,
          progress: bool) -> tuple[int, np.ndarray]:
    """`kernel_sums` with the fixed cells as a sorted tuple."""
    if 2 * t <= LOW:
        nu, sums = qd.subcube_sums(t, dict(fixed))
    else:
        args = [str(_binary()), str(t), str(split)] + [f"{k}:{b}" for k, b in fixed]
        run = subprocess.run(args, stdout=subprocess.PIPE, stderr=None if progress else subprocess.DEVNULL,
                             text=True, check=True, env={**os.environ, "OMP_NUM_THREADS": str(threads)})
        lines = run.stdout.split("\n")
        nu = int(lines[0].split()[1])
        sums = np.zeros((2 * t, 2), dtype=np.int64)  # (2t, 2)
        for line in lines[1:]:
            if line.strip():
                k, s0, s1 = (int(v) for v in line.split())
                sums[k, 0], sums[k, 1] = s0, -s1
    sums.setflags(write=False)
    return nu, sums


def evasive(t: int, fixed: dict[int, int], level: int, threads: int = 1) -> bool:
    """`query_depth.evasive` on the C sums: g_t restricted to `fixed` has a nonzero top coefficient (level 0), or for
    every free variable k some fixing of k leaves a function with a certificate of level - 1."""
    nu, sums = kernel_sums(t, fixed, threads)
    if nu != 0:
        return True
    if level == 0:
        return False
    for k in range(2 * t):
        if k in fixed or sums[k, 0] != 0 or sums[k, 1] != 0:
            continue
        if not any(evasive(t, {**fixed, k: b}, level - 1, threads) for b in (0, 1)):
            return False
    return True


def certificate(t: int, max_level: int = 3, threads: int = 1, progress: bool = False) -> tuple[int, int, list[int]]:
    """(mu(c_t), level, hard cells) as in `query_depth.certificate`: level 0 if mu(c_t) != 0, level L if g_t has a
    certificate of level L, -1 if none up to `max_level`. The hard cells are the variables k of g_t with both
    restricted sums 0. `progress` shows the tasks of the C program for the sum over all rows."""
    nu, sums = kernel_sums(t, {}, threads, progress=progress)
    if nu != 0:
        return 2 * nu, 0, []
    hard = [k for k in range(2 * t) if sums[k, 0] == 0 and sums[k, 1] == 0]
    for level in range(1, max_level + 1):
        if all(any(evasive(t, {k: b}, level - 1, threads) for b in (0, 1)) for k in hard):
            return 0, level, hard
    return 0, -1, hard


def corner_or_holds(t: int) -> bool:
    """c_t(x) depends on (x_{t-1}, x_t) only through x_{t-1} or x_t: the rows with the pair 01, 10 and 11 give the
    same center (t >= 1)."""
    table = cone_table(t).reshape(4, -1)  # (4, 2^(2t-1)); row 2 x_t + x_{t-1}, the two highest bits of the index
    return bool((table[1] == table[3]).all() and (table[2] == table[3]).all())


def corner_restrictions(t: int, threads: int = 1,
                        progress: bool = False) -> tuple[int, tuple[int, int], tuple[int, int]]:
    """(nu, (R[x_{t-1}, 0], R[x_{t-1}, 1]), (R[x_t, 0], R[x_t, 1])) for g_t: by the OR of the corner, a black corner
    cell leaves a function that ignores the other corner cell (top coefficient 0) and a white one leaves nu."""
    nu, sums = kernel_sums(t, {}, threads, progress=progress)
    return nu, (int(sums[2 * t - 2, 0]), int(sums[2 * t - 2, 1])), (int(sums[2 * t - 1, 0]), int(sums[2 * t - 1, 1]))


def restrict_table(table: np.ndarray, n: int, fixed: dict[int, int]) -> np.ndarray:
    """The truth table of a function on n variables with the variables of `fixed` fixed, on the others in order."""
    index = np.arange(1 << n)  # (2^n,)
    sel = np.ones(1 << n, dtype=bool)  # (2^n,)
    for k, b in fixed.items():
        sel &= ((index >> k) & 1) == b
    free = [k for k in range(n) if k not in fixed]
    packed = sum(((index >> k) & 1) << pos for pos, k in enumerate(free))  # (2^n,)
    out = np.zeros(1 << len(free), dtype=np.uint8)  # (2^(n - |fixed|),)
    out[packed[sel]] = table[sel]
    return out


def pair_weights(table: np.ndarray, n: int) -> np.ndarray:
    """W[i, j, a, b] = the number of 1-rows with x_i = a and x_j = b."""
    index = np.arange(1 << n)  # (2^n,)
    bits = [(index >> i) & 1 for i in range(n)]  # n x (2^n,)
    weights = np.zeros((n, n, 2, 2), dtype=np.int64)  # (n, n, 2, 2)
    ones = table.astype(bool)  # (2^n,)
    for i in range(n):
        for j in range(n):
            for a in (0, 1):
                for b in (0, 1):
                    weights[i, j, a, b] = int((ones & (bits[i] == a) & (bits[j] == b)).sum())
    return weights


def npn_equivalent(f: np.ndarray, g: np.ndarray, n: int) -> tuple[list[int], list[int], int] | None:
    """(perm, neg, out) with f(x) = g(y) xor out, y_{perm[i]} = x_i xor neg[i], or None: a backtracking search that
    matches the pair weights of each new variable with those of the ones placed, then checks the whole table."""
    wg = pair_weights(g, n)
    for out in (0, 1):
        ff = f ^ np.uint8(out)  # (2^n,)
        if int(ff.sum()) == int(g.sum()):
            found = _place(ff, g, n, pair_weights(ff, n), wg)
            if found is not None:
                return found[0], found[1], out
    return None


def _place(f: np.ndarray, g: np.ndarray, n: int, wf: np.ndarray,
           wg: np.ndarray) -> tuple[list[int], list[int]] | None:
    """The backtracking of `npn_equivalent` for a fixed value negation: (perm, neg) with f(x) = g(y)."""
    index = np.arange(1 << n)  # (2^n,)
    perm: list[int] = [0] * n
    neg: list[int] = [0] * n
    used = [False] * n

    def fits(i: int) -> bool:
        return all(wf[i, j, a, b] == wg[perm[i], perm[j], a ^ neg[i], b ^ neg[j]]
                   for j in range(i + 1) for a in (0, 1) for b in (0, 1))

    def place(i: int) -> bool:
        if i == n:
            y = np.zeros(1 << n, dtype=np.int64)  # (2^n,)
            for k in range(n):
                y |= (((index >> k) & 1) ^ neg[k]) << perm[k]
            return bool((f == g[y]).all())
        for p in range(n):
            if used[p]:
                continue
            for s in (0, 1):
                perm[i], neg[i] = p, s
                if fits(i):
                    used[p] = True
                    if place(i + 1):
                        return True
                    used[p] = False
        return False

    return (list(perm), list(neg)) if place(0) else None


def restriction_isomorphisms(t: int) -> tuple[int, int, list[tuple[int, int, int, int]]]:
    """Route (i) at t: over the restrictions of c_{t+1} that fix two of its 2t + 3 cells, (number of restrictions,
    number that need all their 2t + 1 cells, the restrictions (i, a, j, b), cells x_i = a and x_j = b, that equal c_t
    up to permutation and negation of cells and negation of the value)."""
    n = 2 * t + 3
    big, small = cone_table(t + 1), cone_table(t)  # (2^(2t+3),), (2^(2t+1),)
    total = evasive_count = 0
    found = []
    for i, j in itertools.combinations(range(n), 2):
        for a, b in itertools.product((0, 1), repeat=2):
            r = restrict_table(big, n, {i: a, j: b})  # (2^(2t+1),)
            total += 1
            evasive_count += int(qd.exact_depth(r, n - 2) == n - 2)
            if npn_equivalent(r, small, n - 2) is not None:
                found.append((i - t - 1, a, j - t - 1, b))
    return total, evasive_count, found


def pair_gates(table: np.ndarray, n: int) -> list[tuple[int, int, tuple[int, ...]]]:
    """The pairs of variables (i, j) through which the function factors by a gate of two inputs: the four cofactors
    at (x_i, x_j) = 00, 01, 10, 11 are at most two distinct functions. Each pair comes with the class of each cofactor
    in that order: (0, 1, 1, 1) is an OR, (0, 1, 1, 0) an XOR."""
    index = np.arange(1 << n)  # (2^n,)
    out = []
    for i, j in itertools.combinations(range(n), 2):
        base = index[(((index >> i) & 1) == 0) & (((index >> j) & 1) == 0)]  # (2^(n-2),)
        labels: dict[bytes, int] = {}
        classes = []
        for a, b in ((0, 0), (0, 1), (1, 0), (1, 1)):
            key = table[base | (a << i) | (b << j)].tobytes()
            classes.append(labels.setdefault(key, len(labels)))
        if len(labels) <= 2:
            out.append((i, j, tuple(classes)))
    return out


def reduced_table(t: int) -> np.ndarray:
    """G_t: c_t with x_{-t} and x_{t-1} white, on the cells x_{-t+1} .. x_{t-2}, x_t in order."""
    n = 2 * t + 1
    return restrict_table(cone_table(t), n, {0: 0, n - 2: 0})


def anf(table: np.ndarray, n: int) -> np.ndarray:
    """The GF(2) normal form: entry S is the coefficient of the monomial of the variables in S (Moebius transform)."""
    coef = table.astype(np.uint8).copy()  # (2^n,)
    for i in range(n):
        view = coef.reshape(-1, 2, 1 << i)  # (2^(n-i-1), 2, 2^i)
        view[:, 1, :] ^= view[:, 0, :]
    return coef


def covering_pairs(t: int) -> int:
    """P = the number of unordered pairs of distinct monomials of the GF(2) normal form of g_t whose union is all 2t
    variables: the count of ordered pairs is the sum over monomials m of the number of monomials containing the
    complement of m (a superset sum)."""
    n = 2 * t
    mono = anf(cone_table(t)[0::2], n).astype(np.int64)  # (2^n,), g_t: x_{-t} = 0
    sup = mono.copy()  # (2^n,), sup[S] = number of monomials containing S
    for i in range(n):
        view = sup.reshape(-1, 2, 1 << i)  # (2^(n-i-1), 2, 2^i)
        view[:, 0, :] += view[:, 1, :]
    full = (1 << n) - 1
    ordered = int((mono * sup[full ^ np.arange(1 << n)]).sum())
    assert mono[full] == 0  # the degree is below 2t, so no monomial pairs with itself
    return ordered // 2


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-t", type=int, default=17, help="mu(c_t) and certificates for t <= this")
    parser.add_argument("--threads", type=int, default=1, help="OpenMP threads of the C program")
    parser.add_argument("--routes", type=int, default=0, help="route (i) and the corner checks for t <= this")
    parser.add_argument("--pairs", type=int, default=8, help="route (iii), covering pairs, for t <= this")
    args = parser.parse_args()

    if args.routes:
        print("t  corner OR  two-cell restrictions of c_{t+1}  needing all cells  equivalent to c_t")
        for t in range(1, args.routes + 1):
            total, ev, found = restriction_isomorphisms(t)
            print(t, corner_or_holds(t), total, ev, found, flush=True)
        print("t  gates of two cells in c_t (cells x_i, x_j)  in G_t (positions among its 2t - 1 cells)")
        for t in range(2, args.routes + 3):
            n = 2 * t + 1
            gates = [(i - t, j - t, c) for i, j, c in pair_gates(cone_table(t), n)]
            print(t, gates, pair_gates(reduced_table(t), n - 2), flush=True)
    print("t  nu(g_t)  P_t  nu mod 4  2 P mod 4")
    for t in range(2, args.pairs + 1):
        nu, _ = qd.subcube_sums(t, {})
        p = covering_pairs(t)
        print(t, nu, p, nu % 4, 2 * p % 4, flush=True)
    print("t  mu(c_t)  level  hard variables k  corner sums (x_{t-1}: white, black) (x_t: white, black)  nu with both white  "
          "cells x_j where white gives 0  where black gives 0")
    for t in tqdm(range(2, args.max_t + 1), desc="certificates", file=sys.stderr):
        show = t >= 19  # the runs that take minutes
        mu, level, hard = certificate(t, threads=args.threads, progress=show)
        nu, left, right = corner_restrictions(t, args.threads, show)
        pair, _ = kernel_sums(t, {2 * t - 2: 0, 2 * t - 1: 0}, args.threads, progress=show)
        _, sums = kernel_sums(t, {}, args.threads, progress=show)
        white = [k - t + 1 for k in range(2 * t) if sums[k, 0] == 0]  # cells x_j whose white fixing gives 0
        black = [k - t + 1 for k in range(2 * t) if sums[k, 1] == 0]
        print(t, mu, level, hard, left, right, pair, white, black, flush=True)


if __name__ == "__main__":
    main()
