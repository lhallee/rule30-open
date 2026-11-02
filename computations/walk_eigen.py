"""The front walk on every pair word of period P: its largest cycle mean (the max-plus eigenvalue), its excess over
slope 5/2, and local potentials for it.

`Rule30Open.Diagonals.FrontWalker` defines a front walk w: from time w_i, diagonal i has a black cell before w_{i+1},
or is eventually white and w_i <= w_{i+1}; the least walk slides from w_i to the first black cell r of D_i and steps to
w_{i+1} = r + 1. Between white diagonals that double the period, the aligned words of D_i and D_{i+1} have a common
period P, the pair (D_i, D_{i+1}) follows the bijection F(A, B) = (B, C) of `settled_words.pair_next`, and the least
walk is a deterministic map on states (A, B, f) with f = w_i mod P:

- A not white: d is the white run of A ahead of f (the least d >= 0 with A(f + d) = 1), the step costs d + 1 and the
  phase becomes f + d + 1. The next pair is F(A, B) if B is not white. If B is white, D_{i+2} accumulates A
  (`D_shift_of_white` of LeftMemory): Y(t + 1) = Y(t) xor A(t), with either integration constant Y(0); when A has even
  weight Y has period P and the next pair is (0, Y), for both constants; when it has odd weight the period doubles and
  the walk leaves period P (an exit).
- A white (the crossing of a white diagonal, FrontWalk's first disjunct): cost 0, w_{i+1} = w_i, next pair F(0, B).

Every step moves one depth. The excess of a state at slope gamma is E(s) = max(0, cost(s) - gamma + max E(s')), the
largest excess of the walk over gamma n along any path from s, and E is an optimal potential:
cost(s) - gamma <= E(s) - E(s') on every edge.

- `walk_step`, `walk_graph`: the step on one state, and the whole graph of 4^P P states (numpy, P <= 10);
- `run_c` (`walk_eigen.c`): for P up to 16, the pair orbits of F (chains from (0, Y) to (X, 0) and cycles of F) walked
  with all phases at once: the largest cycle mean inside cycles of F, the chain summaries, and the excess at slope
  num/den over the chain states (`R_chain`), the chain starts (`R_start`), the starts after a doubling (`R_double`, Y
  anti-periodic) and the cycles of F (`R_cycle`);
- `chain_cycle_mean`: the largest cycle mean of the cycles through white crossings, by Howard's policy iteration on
  the chain summaries (cost and length per chain);
- `max_cycle_mean_graph`, `brute_cycle_mean`, `excess_graph`: the same quantities on the numpy graph, by Howard's
  iteration, by enumerating every simple cycle, and by value iteration (independent checks);
- `replay`: the single cell's least walk on its settled words, checked step by step as edges of the graph;
- `window_codes`, `lookahead_codes`, `feature_graph`, `feature_cycle_mean`, `fit_potential`: local potentials. The
  quotient of the graph by local features (the white run of A ahead of f, a window of h cells of A and B, whether A
  and B are white; or the costs of the next k steps) and its largest cycle mean by Karp's theorem, the least slope that
  any function of those features certifies; and the linear program for Phi(s) = k d(s) + table(window) with
  cost(s) - gamma <= Phi(s) - Phi(s') on every edge that stays in period P.

    python -m computations.walk_eigen --periods 2-14                  # mu_P and the excesses, about 3 min, 0.3 GB
    python -m computations.walk_eigen --periods 15                    # about 10 min
    python -m computations.walk_eigen --replay 87866                  # the single cell's walk, about 30 s
    python -m computations.walk_eigen --features 4-8 --widths 0,1,2,3 # the local potentials, about 15 s
"""

from __future__ import annotations

import argparse
import functools
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

import numpy as np
from tqdm.auto import tqdm

HERE = Path(__file__).resolve().parent
GAMMA = Fraction(5, 2)


# ---------------------------------------------------------------------------------------------------------------------
# One state: words are integers, bit t is the cell at time t mod P


def gap(a: int, f: int, P: int) -> int:
    """The white run of a ahead of phase f: the least d >= 0 with a(f + d) = 1 (a not white)."""
    d = 0
    while not (a >> ((f + d) % P)) & 1:
        d += 1
    return d


def next_word(a: int, b: int, P: int) -> int:
    """For b not white: the P-periodic word c with c(t + 1) = a(t) xor (b(t) or c(t)), computed around the period from
    the black cell r = 0 of b of least index, where c(r + 1) = not a(r)."""
    r = (b & -b).bit_length() - 1
    c = [0] * P  # (P,)
    c[(r + 1) % P] = 1 - ((a >> r) & 1)
    for k in range(1, P):
        t = (r + k) % P
        c[(t + 1) % P] = ((a >> t) & 1) ^ (((b >> t) & 1) | c[t])
    return sum(bit << t for t, bit in enumerate(c))


def integrate(a: int, P: int) -> int:
    """The word Y with Y(0) = 0 and Y(t + 1) = Y(t) xor a(t), t < P - 1 (P-periodic when a has even weight)."""
    y = cur = 0
    for t in range(P - 1):
        cur ^= (a >> t) & 1
        y |= cur << (t + 1)
    return y


@dataclass(frozen=True, slots=True)
class Step:
    cost: int  # w_{i+1} - w_i
    nexts: list[tuple[int, int, int]]  # the successor states (A', B', f'); empty when the period doubles


def walk_step(a: int, b: int, f: int, P: int) -> Step:
    """One step of the least front walk from the state (A, B, f) = (a, b, f) of period P ((a, b) != (0, 0))."""
    m = (1 << P) - 1
    if a == 0:
        return Step(0, [(b, next_word(0, b, P), f)])
    d = gap(a, f, P)
    g = (f + d + 1) % P
    if b:
        return Step(d + 1, [(b, next_word(a, b, P), g)])
    if a.bit_count() % 2:
        return Step(d + 1, [])
    y = integrate(a, P)
    return Step(d + 1, [(0, y, g), (0, (~y) & m, g)])


def state_index(a: int, b: int, f: int, P: int) -> int:
    """The index of (a, b, f) in `walk_graph` and in the C program's dump."""
    return ((a << P) | b) * P + f


# ---------------------------------------------------------------------------------------------------------------------
# The whole graph (numpy)


@dataclass(frozen=True, slots=True)
class WalkGraph:
    P: int
    succ: np.ndarray  # (N, 2) successor state indices, -1 for none; N = 4^P P, index ((A << P) | B) P + f
    cost: np.ndarray  # (N,) cost of the step from each state (-1 for the states (0, 0, f), which are not used)


def gap_table(P: int) -> np.ndarray:
    """gaps[a, f] = the white run of a ahead of f, -1 for a = 0."""
    a = np.arange(1 << P, dtype=np.int64)[:, None]  # (2^P, 1)
    gaps = np.full((1 << P, P), -1, dtype=np.int64)  # (2^P, P)
    for f in range(P):
        for d in range(P - 1, -1, -1):
            hit = ((a[:, 0] >> ((f + d) % P)) & 1) == 1  # (2^P,)
            gaps[hit, f] = d
    return gaps  # (2^P, P)


def walk_graph(P: int) -> WalkGraph:
    """Every state (A, B, f) of period P with its successors and cost."""
    from computations.settled_words import pair_next

    assert P <= 10
    n = 1 << (2 * P)
    m = (1 << P) - 1
    pair = np.arange(n, dtype=np.int64)  # (4^P,)
    a, b = pair >> P, pair & m  # (4^P,), (4^P,)
    c, _ = pair_next(a.astype(np.uint64), b.astype(np.uint64), P)  # (4^P,)
    c = c.astype(np.int64)
    gaps = gap_table(P)  # (2^P, P)
    y = np.array([integrate(x, P) for x in range(1 << P)], dtype=np.int64)  # (2^P,)
    even = np.array([x.bit_count() % 2 == 0 for x in range(1 << P)])  # (2^P,)
    N = n * P
    s = np.arange(N, dtype=np.int64)  # (N,)
    p, f = s // P, s % P  # (N,), (N,)
    A, B = a[p], b[p]  # (N,), (N,)
    d = gaps[A, f]  # (N,)
    cost = np.where(A == 0, 0, d + 1)  # (N,)
    g = np.where(A == 0, f, (f + d + 1) % P)  # (N,)
    succ = np.full((N, 2), -1, dtype=np.int64)  # (N, 2)
    on = B != 0  # (N,)
    succ[on, 0] = ((B[on] << P) | c[p[on]]) * P + g[on]
    cross = (A != 0) & (B == 0) & even[A]  # (N,)
    succ[cross, 0] = y[A[cross]] * P + g[cross]
    succ[cross, 1] = ((~y[A[cross]]) & m) * P + g[cross]
    void = (A == 0) & (B == 0)  # (N,)
    cost[void] = -1
    return WalkGraph(P, succ, cost)


def prune(g: WalkGraph) -> np.ndarray:
    """The states from which the walk can go on forever (every cycle lies among them)."""
    alive = g.cost >= 0  # (N,)
    while True:
        ok = (g.succ >= 0) & alive[np.maximum(g.succ, 0)]  # (N, 2)
        new = alive & ok.any(axis=1)  # (N,)
        if new.sum() == alive.sum():
            return new  # (N,)
        alive = new


def max_cycle_mean_graph(g: WalkGraph) -> Fraction:
    """The largest mean cost of a cycle of the graph, by Howard's iteration of `seed_certificate` (0 if none)."""
    from computations.seed_certificate import Graph, max_cycle_mean

    alive = prune(g)  # (N,)
    if not alive.any():
        return Fraction(0)
    index = np.cumsum(alive) - 1  # (N,)
    ok = (g.succ >= 0) & alive[np.maximum(g.succ, 0)]  # (N, 2)
    succ = np.where(ok, index[np.maximum(g.succ, 0)], -1)[alive]  # (n, 2)
    weight = np.repeat(g.cost[alive][:, None], 2, axis=1)  # (n, 2)
    mu, _ = max_cycle_mean(Graph(np.flatnonzero(alive), succ, weight))
    return mu


def brute_cycle_mean(g: WalkGraph) -> Fraction:
    """The largest mean cost over every simple cycle, by enumeration: cycles of the states with one successor, and the
    simple cycles of the graph on the states with two successors (each edge there a path through one-successor
    states). For small P."""
    N = len(g.cost)
    deg = (g.succ >= 0).sum(axis=1)  # (N,)
    best = Fraction(0)
    # cycles that avoid the branching states
    color = np.zeros(N, dtype=np.int8)  # (N,)
    for s0 in range(N):
        path: list[int] = []
        v = s0
        while v >= 0 and deg[v] == 1 and color[v] == 0:
            color[v] = 1
            path.append(v)
            v = int(g.succ[v, 0])
        if v >= 0 and deg[v] == 1 and color[v] == 1:
            cyc = path[path.index(v):]
            best = max(best, Fraction(int(g.cost[cyc].sum()), len(cyc)))
        for u in path:
            color[u] = 2
    # cycles through branching states
    branch = [int(v) for v in np.flatnonzero(deg == 2)]
    edges: dict[int, list[tuple[int, int, int]]] = {v: [] for v in branch}  # v -> (target, cost, length)
    for v in branch:
        for e in range(2):
            cost, length, u, seen = int(g.cost[v]), 1, int(g.succ[v, e]), set()
            while u >= 0 and deg[u] == 1 and u not in seen:
                seen.add(u)
                cost += int(g.cost[u])
                length += 1
                u = int(g.succ[u, 0])
            if u >= 0 and deg[u] == 2:
                edges[v].append((u, cost, length))
    for start in branch:
        stack = [(start, 0, 0, frozenset([start]))]
        while stack:
            v, cost, length, on = stack.pop()
            for u, c, ln in edges[v]:
                if u == start:
                    best = max(best, Fraction(cost + c, length + ln))
                elif u > start and u not in on:
                    stack.append((u, cost + c, length + ln, on | {u}))
    return best


def excess_graph(g: WalkGraph, gamma: Fraction, rounds: int = 100000) -> np.ndarray:
    """E(s) = max(0, den cost(s) - num + max over successors E(s')) in units of 1/den, by value iteration (an exit
    counts its own step only). Raises if a cycle has a mean above gamma."""
    num, den = gamma.numerator, gamma.denominator
    w = np.where(g.cost >= 0, den * g.cost - num, 0)  # (N,)
    tgt = np.maximum(g.succ, 0)  # (N, 2)
    E = np.zeros(len(w), dtype=np.int64)  # (N,)
    for _ in range(rounds):
        nxt = np.where(g.succ >= 0, E[tgt], 0).max(axis=1)  # (N,)
        new = np.where(g.cost >= 0, np.maximum(0, w + nxt), 0)  # (N,)
        if (new == E).all():
            return E  # (N,)
        E = new
    raise RuntimeError("no fixed point: a cycle has a mean above gamma")


# ---------------------------------------------------------------------------------------------------------------------
# The C program


@functools.lru_cache(maxsize=2)
def _binary(optimize: bool) -> Path:
    """Compile computations/walk_eigen.c once per process into a temporary directory (without optimization for the
    small periods, where compiling takes longer than running)."""
    cc = shutil.which("cc") or shutil.which("gcc")
    assert cc, "a C compiler is needed"
    out = Path(tempfile.mkdtemp(prefix="walk_eigen_")) / "walk_eigen"
    subprocess.run([cc, "-O2" if optimize else "-O0", "-w", str(HERE / "walk_eigen.c"), "-o", str(out)], check=True)
    return out


@dataclass(frozen=True, slots=True)
class CResult:
    P: int
    gamma: Fraction
    values: dict[str, int]  # the program's keys (excesses in units of 1/den)
    mu_f: Fraction  # the largest cycle mean inside cycles of F (0 if none)
    mu_p: Fraction  # the same over the cycles of F whose pairs have least period P
    steps: np.ndarray  # (2^P,) pairs of the chain from (0, Y), Y = 0 .. 2^P - 1 (Y = 0 unused)
    end: np.ndarray  # (2^P,) the chain's last first word X: the chain ends at (X, 0)
    cost: np.ndarray  # (2^P, P) the cost of the chain from (0, Y) at phase f to the start of the next one
    phase: np.ndarray  # (2^P, P) the phase there
    E: np.ndarray | None  # (4^P P,) the excess of every state in units of 1/den (-1 for (0, 0, f)), if asked

    def excess(self, key: str) -> Fraction | None:
        """R_chain, R_start, R_double or R_cycle as a fraction (None if not finite or not defined)."""
        v = self.values[key]
        return None if v < 0 else Fraction(v, self.gamma.denominator)


def run_c(P: int, gamma: Fraction = GAMMA, dump: bool = False, progress: bool = False) -> CResult:
    """Run walk_eigen.c at period P and slope gamma, with the chain summaries and optionally every E."""
    with tempfile.TemporaryDirectory(prefix="walk_eigen_") as tmp:
        summ, dfile = Path(tmp) / "summary.bin", Path(tmp) / "dump.bin"
        run = subprocess.run([str(_binary(P >= 9)), str(P), str(gamma.numerator), str(gamma.denominator), str(summ),
                              str(dfile) if dump else "-"], stdout=subprocess.PIPE,
                             stderr=None if progress else subprocess.DEVNULL, text=True, check=True)
        values: dict[str, int] = {}
        means: dict[str, Fraction] = {}
        for line in run.stdout.splitlines():
            key, *rest = line.split()
            if len(rest) == 2:
                means[key] = Fraction(int(rest[0]), int(rest[1]))
            else:
                values[key] = int(rest[0])
        W = 1 << P
        raw = np.fromfile(summ, dtype=np.int64)  # (2 W + 2 W P,)
        steps, end = raw[:W], raw[W:2 * W]  # (W,), (W,)
        cost = raw[2 * W:2 * W + W * P].reshape(W, P)  # (W, P)
        phase = raw[2 * W + W * P:].reshape(W, P)  # (W, P)
        E = np.fromfile(dfile, dtype=np.int32) if dump else None  # (4^P P,)
    return CResult(P, gamma, values, means["mu_f"], means["mu_p"], steps, end, cost, phase, E)


def chain_cycle_mean(r: CResult, max_rounds: int = 500) -> Fraction:
    """The largest mean cost of a cycle through white crossings: Howard's policy iteration on the chain graph, whose
    node (Y, f) is the start of the chain from (0, Y) at phase f, with an edge of the chain's cost and number of steps
    to (Y0(X), g) and (Y1(X), g) when its end (X, 0) keeps the period (0 if there is no such cycle)."""
    P = r.P
    W = 1 << P
    y0 = np.array([integrate(x, P) for x in range(W)], dtype=np.int64)  # (W,)
    keep = np.array([int(x).bit_count() % 2 == 0 for x in r.end], dtype=bool) & (np.arange(W) > 0)  # (W,)
    node = np.arange(W * P)  # (W P,): node Y P + f
    Y, f = node // P, node % P  # (W P,), (W P,)
    g = r.phase[Y, f]  # (W P,)
    succ = np.full((W * P, 2), -1, dtype=np.int64)  # (W P, 2)
    k = keep[Y]  # (W P,)
    succ[k, 0] = y0[r.end[Y[k]]] * P + g[k]
    succ[k, 1] = ((~y0[r.end[Y[k]]]) & (W - 1)) * P + g[k]
    cost = r.cost[Y, f].astype(np.float64)  # (W P,)
    length = r.steps[Y].astype(np.float64)  # (W P,)
    alive = (succ >= 0).any(axis=1)  # (W P,)
    while True:
        ok = (succ >= 0) & alive[np.maximum(succ, 0)]  # (W P, 2)
        new = alive & ok.any(axis=1)
        if new.sum() == alive.sum():
            break
        alive = new
    if not alive.any():
        return Fraction(0)
    idx = np.flatnonzero(alive)  # (n,)
    index = np.cumsum(alive) - 1  # (W P,)
    ok = ((succ >= 0) & alive[np.maximum(succ, 0)])[idx]  # (n, 2)
    sc = np.where(ok, index[np.maximum(succ[idx], 0)], -1)  # (n, 2)
    c, ln = cost[idx], length[idx]  # (n,), (n,)
    n = len(idx)
    choice = np.argmax(sc >= 0, axis=1)  # (n,)
    for _ in range(max_rounds):
        nxt = sc[np.arange(n), choice]  # (n,)
        rep, tot_c, tot_l, _ = _policy_cycles(nxt, c, ln)
        eta = tot_c[rep] / tot_l[rep]  # (n,)
        x = _policy_bias(nxt, c - eta * ln, rep)  # (n,)
        tgt = np.maximum(sc, 0)  # (n, 2)
        cand_eta = np.where(sc >= 0, eta[tgt], -np.inf)  # (n, 2)
        cand_x = np.where(sc >= 0, (c - eta * ln)[:, None] + x[tgt], -np.inf)  # (n, 2)
        new = choice.copy()  # (n,)
        up = cand_eta.max(axis=1) > eta + 1e-9  # (n,)
        new[up] = np.argmax(cand_eta[up], axis=1)
        same = np.where(np.abs(cand_eta - eta[:, None]) < 1e-9, cand_x, -np.inf)  # (n, 2)
        better = ~up & (same.max(axis=1) > x + 1e-7)  # (n,)
        new[better] = np.argmax(same[better], axis=1)
        if (new == choice).all():
            break
        choice = new
    else:
        raise RuntimeError("policy iteration did not converge")
    best = int(np.argmax(eta))
    r0 = int(rep[best])
    total_c, total_l, v = 0, 0, r0
    while True:  # the exact mean of the best cycle
        total_c += int(c[v])
        total_l += int(ln[v])
        v = int(nxt[v])
        if v == r0:
            break
    return Fraction(total_c, total_l)


def _policy_cycles(nxt: np.ndarray, c: np.ndarray, ln: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray,
                                                                                np.ndarray]:
    """For the functional graph v -> nxt[v]: the least node of the cycle each node reaches, the cost and length sums
    of each cycle (indexed by that node), and which nodes lie on a cycle."""
    n = len(nxt)
    jump = nxt.copy()  # (n,)
    k = 1
    while k < n:
        jump = jump[jump]
        k *= 2
    on = np.zeros(n, dtype=bool)  # (n,)
    on[jump] = True
    rep = np.arange(n)  # (n,)
    hop = nxt.copy()  # (n,)
    k = 1
    while k < n:
        rep = np.minimum(rep, rep[hop])
        hop = hop[hop]
        k *= 2
    tot_c = np.bincount(rep[on], weights=c[on], minlength=n)  # (n,)
    tot_l = np.bincount(rep[on], weights=ln[on], minlength=n)  # (n,)
    return rep[jump], tot_c, tot_l, on


def _policy_bias(nxt: np.ndarray, w: np.ndarray, rep: np.ndarray) -> np.ndarray:
    """x with x(v) = w(v) + x(nxt v) off the representatives and x = 0 on them, by pointer doubling."""
    n = len(nxt)
    idx = np.arange(n)  # (n,)
    is_rep = idx == rep  # (n,)
    acc = np.where(is_rep, 0.0, w)  # (n,)
    hop = np.where(is_rep, idx, nxt)  # (n,)
    k = 1
    while k < n:
        acc = acc + acc[hop]
        hop = hop[hop]
        k *= 2
    return acc  # (n,)


@dataclass(frozen=True, slots=True)
class PeriodRow:
    P: int
    mu: Fraction  # the largest cycle mean of the graph
    mu_f: Fraction  # inside cycles of F
    mu_p: Fraction  # inside cycles of F whose pairs have least period P
    mu_cross: Fraction  # through white crossings
    R_all: Fraction | None  # the largest excess at gamma over every state (None: a cycle above gamma)
    R_chain: Fraction | None  # over the states of chains
    R_start: Fraction | None  # over the chain starts (0, Y)
    R_double: Fraction | None  # over the starts with Y anti-periodic (the start of a regime after a doubling)
    chain_pairs: int  # pairs on chains (the others are on cycles of F)
    longest_chain: int


def period_row(P: int, gamma: Fraction = GAMMA, progress: bool = False) -> PeriodRow:
    """mu_P and the excesses at slope gamma for one period, by the C program and `chain_cycle_mean`."""
    r = run_c(P, gamma, progress=progress)
    mu_x = chain_cycle_mean(r)
    v = r.values
    parts = [x for x in (r.excess("R_chain"), r.excess("R_cycle")) if x is not None]
    finite = v["chain_fixed"] == 1 and (v["fcycles"] == 0 or v["R_cycle"] >= 0)
    return PeriodRow(P, max(r.mu_f, mu_x), r.mu_f, r.mu_p, mu_x, max(parts) if finite and parts else None,
                     r.excess("R_chain") if v["chain_fixed"] else None, r.excess("R_start") if v["chain_fixed"] else None,
                     r.excess("R_double") if v["chain_fixed"] else None, v["chain_pairs"], v["longest_chain"])


# ---------------------------------------------------------------------------------------------------------------------
# The single cell's walk as edges of the graph


@dataclass(frozen=True, slots=True)
class Replay:
    steps: int  # steps checked
    crossings: list[int]  # depths i of the white diagonals crossed inside period P (A = D_i white)
    exits: list[int]  # depths i where the walk leaves period P (D_{i+1} white, odd weight of D_i)
    mismatches: list[int]  # depths whose step is not an edge of the graph


def single_cell_walk(depth: int, steps: int, period: int = 64, window: int = 256,
                     progress: bool = True) -> tuple[np.ndarray, np.ndarray, int]:
    """The least front walk w (to `depth`) and the last rows of the diagonals, with the time of the first row."""
    from computations.front_walker import walk_from_tail
    from computations.settled_slope import stream

    d = stream(depth, steps, period=period, window=window, progress=progress)
    w = walk_from_tail(d.onset, d.tail, steps, period)  # (depth + 1,)
    return w, d.tail, steps - window  # (depth + 1,), (window, depth + 1)


def replay(w: np.ndarray, tail: np.ndarray, base: int, P: int, lo: int, hi: int) -> Replay:
    """Check the walk's states (D_i, D_{i+1}, w_i mod P), lo <= i <= hi, as a path of the graph of period P: every
    step lo <= i < hi has the cost w_{i+1} - w_i and leads to the next state, and the walk leaves period P only at
    i = hi. The words are read from the rows of `tail` (time base + r), which must repeat with period P there."""
    from computations.settled_words import words_from_tail

    # w: (n,); tail: (window, n)
    words = [int(x) for x in words_from_tail(tail, P)]  # (n,)
    assert all((tail[P:2 * P, i] == tail[:P, i]).all() for i in range(lo, hi + 2)), "the words repeat with period P"
    crossings, exits, bad = [], [], []
    for i in tqdm(range(lo, hi + 1), desc=f"replay at period {P}", unit="depth", file=sys.stderr, mininterval=5,
                  disable=hi - lo < 20000):
        a, b, f = words[i], words[i + 1], int(w[i] - base) % P
        s = walk_step(a, b, f, P)
        if a == 0:
            crossings.append(i)
        if not s.nexts:
            exits.append(i)
            if w[i + 1] - w[i] != s.cost or i != hi:
                bad.append(i)
            continue
        if i == hi:
            bad.append(i)  # the walk should leave period P here
            continue
        target = (words[i + 1], words[i + 2], int(w[i + 1] - base) % P)
        if w[i + 1] - w[i] != s.cost or target not in s.nexts:
            bad.append(i)
    return Replay(hi - lo + 1, crossings, exits, bad)


# ---------------------------------------------------------------------------------------------------------------------
# Local potentials


def window_codes(g: WalkGraph, h: int, off: int) -> np.ndarray:
    """The local features of every state: d (the white run of A ahead of f, 0 for A white), the h cells of A and of B
    at the times f + off .. f + off + h - 1, and whether A is white and whether B is white, as one integer."""
    P = g.P
    N = len(g.cost)
    m = (1 << P) - 1
    s = np.arange(N, dtype=np.int64)  # (N,)
    p, f = s // P, s % P  # (N,), (N,)
    A, B = p >> P, p & m  # (N,), (N,)
    d = np.where(A == 0, 0, gap_table(P)[A, f])  # (N,)
    win = np.zeros(N, dtype=np.int64)  # (N,)
    for k in range(h):
        t = (f + off + k) % P  # (N,)
        win |= ((A >> t) & 1) << (2 * k)
        win |= ((B >> t) & 1) << (2 * k + 1)
    return ((d * (1 << (2 * h)) + win) * 2 + (A == 0)) * 2 + (B == 0)  # (N,)


def lookahead_codes(g: WalkGraph, k: int) -> np.ndarray:
    """The costs of the next k steps of the walk from every state (the first successor at a crossing, P + 1 for an
    exit or beyond it), as one integer."""
    P = g.P
    code = np.zeros(len(g.cost), dtype=np.int64)  # (N,)
    cur = np.arange(len(g.cost), dtype=np.int64)  # (N,)
    for _ in range(k):
        safe = np.maximum(cur, 0)  # (N,)
        c = np.where((cur >= 0) & (g.cost[safe] >= 0), g.cost[safe], P + 1)  # (N,)
        code = code * (P + 2) + c
        cur = np.where(cur >= 0, g.succ[safe, 0], -1)
    return code  # (N,)


@dataclass(frozen=True, slots=True)
class FeatureGraph:
    h: int  # the window width of `window_codes` (0 for other features)
    code: np.ndarray  # (n,) the feature code of each node
    src: np.ndarray  # (m,) node of the source of each distinct edge
    dst: np.ndarray  # (m,) node of its target
    cost: np.ndarray  # (m,) its cost
    loop: tuple[int, int, int]  # the costliest edge between two states of equal features: (cost, state, successor)


def feature_graph(g: WalkGraph, code: np.ndarray, h: int = 0) -> FeatureGraph:
    """The quotient of the walk graph of period P by features `code` (`window_codes` of width h, or any other): one
    edge per distinct (features of s, features of s', cost) over the edges that stay in period P (exits left out)."""
    # code: (N,)
    rows, loop = [], (0, -1, -1)
    for e in range(2):
        s = np.flatnonzero((g.succ[:, e] >= 0) & (g.cost >= 0))  # (k,)
        t = g.succ[s, e]  # (k,)
        rows.append(np.stack([code[s], code[t], g.cost[s]], axis=1))  # (k, 3)
        same = s[code[s] == code[t]]  # (k',)
        if len(same) and int(g.cost[same].max()) > loop[0]:
            i = int(same[np.argmax(g.cost[same])])
            loop = (int(g.cost[i]), i, int(g.succ[i, e]))
    key = np.unique(np.concatenate(rows), axis=0)  # (m, 3)
    nodes, inv = np.unique(key[:, :2].ravel(), return_inverse=True)  # (n,), (2 m,)
    inv = inv.reshape(-1, 2)  # (m, 2)
    return FeatureGraph(h, nodes, inv[:, 0], inv[:, 1], key[:, 2], loop)


def feature_cycle_mean(fg: FeatureGraph) -> Fraction:
    """The largest mean cost of a cycle of the feature graph, by Karp's theorem. A potential that is any function of
    the features, with cost(s) - gamma <= Phi(s) - Phi(s') on every edge, exists exactly when gamma is at least this."""
    n = len(fg.code)
    NEG = np.iinfo(np.int64).min // 4
    D = np.full((n + 1, n), NEG, dtype=np.int64)  # (n + 1, n): the heaviest walk of k edges ending at each node
    D[0] = 0
    for k in range(1, n + 1):
        cand = np.where(D[k - 1][fg.src] > NEG, D[k - 1][fg.src] + fg.cost, NEG)  # (m,)
        np.maximum.at(D[k], fg.dst, cand)
    ks = np.arange(n)  # (n,)
    ok = D[:n] > NEG  # (n, n)
    ratio = np.where(ok, (D[n][None, :] - D[:n]) / (n - ks)[:, None], np.inf)  # (n, n)
    inner = np.where(D[n] > NEG, ratio.min(axis=0), -np.inf)  # (n,)
    v = int(np.argmax(inner))
    if inner[v] == -np.inf:
        return Fraction(0)
    return min(Fraction(int(D[n][v] - D[k][v]), n - k) for k in range(n) if D[k][v] > NEG)


def fit_potential(fgs: list[FeatureGraph], gamma: Fraction) -> tuple[bool, float]:
    """The linear program for Phi(s) = k d(s) + table(cells) + z [A white] + y [B white], with k >= 0, one
    (k, table, z, y) for all the feature graphs given (all of width h), and cost - gamma <= Phi(s) - Phi(s') on every
    edge: whether it is feasible, and the least k if so."""
    from scipy.optimize import linprog

    h = fgs[0].h
    nv = 3 + (1 << (2 * h))  # k, z, y, table
    blocks = []
    for fg in fgs:
        assert fg.h == h
        d = fg.code // 4 >> (2 * h)  # (n,)
        win = fg.code // 4 & ((1 << (2 * h)) - 1)  # (n,)
        white = fg.code // 2 % 2  # (n,)
        bwhite = fg.code % 2  # (n,)
        m = len(fg.src)
        A = np.zeros((m, nv))  # (m, nv): -(Phi(s) - Phi(s')) <= gamma - cost
        A[:, 0] = -(d[fg.src] - d[fg.dst])
        A[:, 1] = -(white[fg.src] - white[fg.dst])
        A[:, 2] = -(bwhite[fg.src] - bwhite[fg.dst])
        np.add.at(A, (np.arange(m), 3 + win[fg.src]), -1.0)
        np.add.at(A, (np.arange(m), 3 + win[fg.dst]), 1.0)
        blocks.append((A, float(gamma) - fg.cost.astype(np.float64)))
    A_ub = np.concatenate([b[0] for b in blocks])  # (M, nv)
    b_ub = np.concatenate([b[1] for b in blocks])  # (M,)
    c = np.zeros(nv)  # (nv,)
    c[0] = 1.0
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, bounds=[(0, None)] + [(None, None)] * (nv - 1), method="highs")
    return res.status == 0, float(res.x[0]) if res.status == 0 else float("nan")


def show_state(s: int, P: int) -> str:
    """A state as text: the words A and B read from time 0 to P - 1, and the phase."""
    p, f = divmod(s, P)
    a, b = p >> P, p & ((1 << P) - 1)
    return f"A={format(a, f'0{P}b')[::-1]} B={format(b, f'0{P}b')[::-1]} f={f}"


# ---------------------------------------------------------------------------------------------------------------------


def _range(text: str) -> list[int]:
    """'2-12' or '4,6,8' as a list of integers."""
    if "-" in text:
        lo, hi = text.split("-")
        return list(range(int(lo), int(hi) + 1))
    return [int(x) for x in text.split(",")]


def _fmt(x: Fraction | None) -> str:
    """A cycle mean as a fraction and its decimal value."""
    return "inf" if x is None else (str(x) if x.denominator == 1 else f"{x}={float(x):.4f}")


def _half(x: Fraction | None) -> str:
    """An excess in halves as a decimal."""
    return "inf" if x is None else f"{float(x):g}"


def regimes_of(tail: np.ndarray, depth: int) -> list[tuple[int, int, int]]:
    """The regimes between doublings of the single cell to `depth`, as (P, lo, hi): lo is the white diagonal that
    starts the regime, hi the depth whose step leaves period P (D_{hi+1} white, D_hi of odd weight). Read from rows
    that cover the periods."""
    from computations.settled_slope import least_periods

    # tail: (window, n)
    period = least_periods(tail)  # (n,)
    white = ~tail.any(axis=0)  # (n,)
    whites = [j for j in range(2, depth) if white[j]]
    out, lo = [], whites[0]
    for j in whites[1:]:
        P = int(period[j - 1])
        if int(tail[:P, j - 1].sum()) % 2:  # odd weight: the period doubles after the white diagonal j
            out.append((P, lo, j - 1))
            lo = j
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--periods", type=str, default="", help="periods for mu_P and the excesses, e.g. 2-12")
    parser.add_argument("--replay", type=int, default=0, help="replay the single cell's walk to this depth")
    parser.add_argument("--features", type=str, default="", help="periods for the local potentials, e.g. 4-9")
    parser.add_argument("--widths", type=str, default="0,1,2,3", help="window widths h for --features")
    parser.add_argument("--lookahead", type=str, default="1,2,3,4", help="lookahead lengths for --features")
    args = parser.parse_args()
    if args.periods:
        print(f"{'P':>3} {'mu_P':>18} {'in cycles of F':>18} {'primitive':>18} {'through crossings':>24} "
              f"{'R_all':>6} {'R_chain':>7} {'R_start':>7} {'R_double':>8} {'chain pairs':>12} {'longest':>8}")
        for P in tqdm(_range(args.periods), desc="periods", unit="P", file=sys.stderr):
            r = period_row(P, progress=P >= 13)
            print(f"{P:>3} {_fmt(r.mu):>18} {_fmt(r.mu_f):>18} {_fmt(r.mu_p):>18} {_fmt(r.mu_cross):>24} "
                  f"{_half(r.R_all):>6} {_half(r.R_chain):>7} {_half(r.R_start):>7} "
                  f"{_half(r.R_double) if P % 2 == 0 else '-':>8} {r.chain_pairs:>12} {r.longest_chain:>8}", flush=True)
    if args.replay:
        depth = args.replay + 4
        w, tail, base = single_cell_walk(depth, 3 * depth // 2 + 600)
        for P, lo, hi in regimes_of(tail, depth):
            r = replay(w, tail, base, P, lo, hi)
            steps = np.diff(w[lo:hi + 2])  # (hi - lo + 1,)
            excess = np.cumsum(2 * steps - 5)  # (hi - lo + 1,): 2 (w_{i+1} - w_lo) - 5 (i + 1 - lo)
            print(f"period {P}, depths {lo} to {hi}: {r.steps} steps, crossings at {r.crossings}, exit at {r.exits}, "
                  f"{len(r.mismatches)} steps not edges of the graph; largest excess over 5/2 from the start "
                  f"{max(0, int(excess.max())) / 2}")
    if args.features:
        widths = _range(args.widths)
        for P in _range(args.features):
            g = walk_graph(P)
            for h in widths:
                for off in range(-h, 1) if h else [0]:
                    fg = feature_graph(g, window_codes(g, h, off), h)
                    mu = feature_cycle_mean(fg) if len(fg.code) <= 1000 else None
                    ok, k = fit_potential([fg], GAMMA)
                    cost, s, t = fg.loop
                    print(f"P {P} window h {h} offset {off}: {len(fg.code)} feature classes, largest cycle mean "
                          f"{_fmt(mu) if mu is not None else '-'}, k d + table at 5/2 feasible: {ok}; costliest edge "
                          f"between equal features: {cost}, {show_state(s, P)} -> {show_state(t, P)}", flush=True)
            for k in _range(args.lookahead):
                fg = feature_graph(g, lookahead_codes(g, k))
                mu = feature_cycle_mean(fg) if len(fg.code) <= 2000 else None
                print(f"P {P} lookahead {k}: {len(fg.code)} feature classes, largest cycle mean "
                      f"{_fmt(mu) if mu is not None else '-'}", flush=True)


if __name__ == "__main__":
    main()
