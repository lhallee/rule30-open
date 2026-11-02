"""Finite abstractions of the seed onsets, their mean payoff, and the uniform increments that any finite certificate
would have to bound.

The setting is that of `seed_onsets`. A seed is a row white left of a black cell lo; its left diagonals D_i follow
D_{i+2}(t+1) = D_i(t) xor (D_{i+1}(t) or D_{i+2}(t)) from D_i(0) = x_i (D_0 = 1, D_{-1} = D_{-2} = 0), and T_i is the
onset of D_i. The front R_j = max(T_0, ..., T_j) is nondecreasing, and a bound R_j <= gamma j + C over every seed is
the same as M_j <= gamma j + C for every j. A finite certificate is a finite set of abstract states with a map from
every seed at every depth j to a state, transitions that cover every step j -> j + 1 of every seed, and an integer
potential Phi with R_{j+1} - R_j <= gamma + Phi(old) - Phi(new) on every transition.

- `jump_costs`: c_n = 1 + the longest cyclic white run of the periodic part of the single cell's D_n. The seed whose
  diagonals 0 .. n repeat from time 0 (a late row of the single cell) at the phase where its time 0 starts that white
  run, with the next cell chosen against the periodic continuation, has R_n = 0 and R_{n+1} = c_n
  (`driven_one_step` checks it). Summed along such a seed, a certificate gives R_{n+k} - R_n <= gamma k + range(Phi),
  so range(Phi) >= c_n - gamma for every n.
- `driven_beam`: lower bounds on N_{n,k}, the largest onset of the k-th diagonal past n over the seeds whose diagonals
  0 .. n repeat from time 0, by a beam search over the free cells (the exact values for k <= 16 are `driven_max` of
  `seed_onsets`). A certificate needs N_{n,k} <= gamma k + range(Phi) for every n and k.
- The window abstraction. The state at depth j is the pair (D_{j-1}, D_j) on the times [R_j - a, R_j) (the window;
  a = min(R_j, h), h the width) and its periodic word on [R_j, R_j + P), P a multiple of every period met, plus a. The
  transition reads the next diagonal D_{j+1} from its value at R_j - a, which the state forgets and the abstraction
  leaves free (for a < h it is the cell x_{j+1} at time 0, and the step is exact); from there D_{j+1} follows by the
  recurrence, its onset with period P gives R_{j+1} (and a bound on T_{j+1}), and the new state is read off. Every step
  of every seed is one of the two transitions of its state, so the abstraction is sound. `window_bounds` (numpy) and
  `window_bounds_c` (`seed_certificate_window.c`) run it depth by depth from the single state at depth 0 and keep, for
  each state, the largest R that reaches it: U_j >= R_j and V_j >= T_j for every seed.
- `pair_graph` takes as states every periodic pair word of period P (not only those that occur) with every age and
  window: a finite graph, sound for every depth whose diagonals all have periods dividing P, and `max_cycle_mean` finds
  its largest cycle mean (Howard's policy iteration) with an integer potential that `check_certificate` verifies edge
  by edge.
- `--seeds`: a beam over the seeds themselves and the seed x_3 = 1 give lower bounds on M_j; where they meet V_j, M_j
  is exact.

    python -m computations.seed_certificate --jumps 200000                      # c_n by period, about 3 min
    python -m computations.seed_certificate --graph 4 --widths 0,1,2,3,4,5       # pair graphs at period 4, 2 s
    python -m computations.seed_certificate --graph 8 --widths 0,1,2             # pair graphs at period 8, 1.5 min
    python -m computations.seed_certificate --window 398 --widths 0,2,4,6,8      # window bounds, about 30 s
    python -m computations.seed_certificate --window 87866 --widths 6            # about 21 min
    python -m computations.seed_certificate --window 13541 --widths 8            # about 45 min, two threads
    python -m computations.seed_certificate --seeds 1000 --beam-width 256        # exact M_j past 76, about 3 min
    python -m computations.seed_certificate --beam 60,120,200,240 --k 150 --beam-width 512  # about 30 s
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
from dataclasses import dataclass
from fractions import Fraction

import numpy as np
from tqdm.auto import tqdm

from computations.seed_onsets import _binary, ceil_three_halves, scalar_onsets, seed_vector, skeleton
from computations.settled_slope import least_periods, stream, white_runs

U64 = np.uint64


# ---------------------------------------------------------------------------------------------------------------------
# One-step jumps and driven increments


def jump_costs(tail: np.ndarray) -> np.ndarray:
    """c_n = 1 + the longest cyclic white run of the periodic part of D_n (0 for a white diagonal), from rows that
    cover the periodic part twice."""
    # tail: (window, n)
    g = white_runs(tail)  # (n,)
    return np.where(g < 0, 0, g + 1)  # (n,)


def driven_one_step(a: np.ndarray, b: np.ndarray, P: int) -> int:
    """The largest onset of the first driven diagonal over its two initial values and the P phases of the pair (a, b)
    (words of length P repeated from time 0), one time at a time: the independent check of `jump_costs`."""
    best = 0
    H = 4 * P
    for phi in range(P):
        for x in (0, 1):
            c = x
            seq = np.zeros(H, dtype=np.uint8)  # (H,)
            for t in range(H):
                seq[t] = c
                c = int(a[(t + phi) % P]) ^ (int(b[(t + phi) % P]) | c)
            diff = np.flatnonzero(seq[P:] != seq[:-P])  # (·,)
            assert diff.size == 0 or diff.max() < H - 2 * P, "period P too short"
            best = max(best, int(diff.max()) + 1 if diff.size else 0)
    return best


def _onsets(D: np.ndarray, P: int) -> np.ndarray:
    """Least T with D[:, t + P] = D[:, t] for T <= t <= H - 1 - P, for each row."""
    # D: (B, H)
    diff = D[:, P:] != D[:, :-P]  # (B, H - P)
    last = diff.shape[1] - 1 - np.argmax(diff[:, ::-1], axis=1)  # (B,)
    return np.where(diff.any(axis=1), last + 1, 0)  # (B,)


def driven_beam(a: np.ndarray, b: np.ndarray, k: int, width: int, P: int = 8) -> np.ndarray:
    """Lower bounds on the onsets of driven diagonals 1 .. k behind the pair (a, b) repeated from time 0: a beam search
    that keeps, at each depth, the `width` distinct pairs of last diagonals with the latest pair onsets. Entry m - 1 is
    the latest onset of driven diagonal m found."""
    H = 8 * ((2 * k + 64) // 8)
    prev = np.resize(a, H)[None, :].astype(np.uint8)  # (1, H)
    cur = np.resize(b, H)[None, :].astype(np.uint8)  # (1, H)
    Tcur = np.zeros(1, dtype=np.int64)  # (1,)
    best = np.zeros(k, dtype=np.int64)  # (k,)
    for m in range(k):
        n = prev.shape[0]
        A = np.concatenate([prev, prev])  # (2n, H)
        Bm = np.concatenate([cur, cur])  # (2n, H)
        new = np.zeros((2 * n, H), dtype=np.uint8)  # (2n, H)
        new[n:, 0] = 1
        for t in range(H - 1):
            new[:, t + 1] = A[:, t] ^ (Bm[:, t] | new[:, t])
        T = _onsets(new, P)  # (2n,)
        best[m] = T.max()
        S = np.maximum(T, np.concatenate([Tcur, Tcur]))  # (2n,): pair onsets
        key = S * (H + 1) + T  # (2n,)
        order = np.argsort(-key, kind="stable")[:4 * width]  # (·,)
        packed = np.packbits(np.concatenate([Bm[order], new[order]], axis=1), axis=1)  # (·, H / 4)
        _, first = np.unique(packed, axis=0, return_index=True)
        keep = order[np.sort(first)][:width]  # (≤ width,)
        prev, cur, Tcur = Bm[keep], new[keep], T[keep]
    assert best.max() <= H - P - 1, "horizon too short"
    return best  # (k,)


def driven_scan(depths: list[int], k: int, width: int, P: int = 8, progress: bool = True) -> np.ndarray:
    """Row r: lower bounds on N_{n,m}, m = 1 .. k, for n = depths[r]: the largest onset of the m-th diagonal past n over
    the seeds whose diagonals 0 .. n repeat from time 0, by `driven_beam` at every phase. P must be a multiple of every
    period to max(depths) + k (8 below depth 399)."""
    _, tail = skeleton(max(depths))  # (64, max(depths) + 1)
    N = np.zeros((len(depths), k), dtype=np.int64)  # (len(depths), k)
    for r, n in enumerate(tqdm(depths, desc="driven beam", file=sys.stderr, mininterval=5, disable=not progress)):
        for phi in range(P):
            N[r] = np.maximum(N[r], driven_beam(tail[phi:phi + P, n - 1], tail[phi:phi + P, n], k, width, P))
    return N


# ---------------------------------------------------------------------------------------------------------------------
# The window abstraction


@dataclass(frozen=True, slots=True)
class States:
    pw: np.ndarray  # (n,) uint64: A on [R, R + P) in bits 0 .. P - 1, B on [R, R + P) in bits P .. 2P - 1
    win: np.ndarray  # (n,) uint64: A on [R - h, R) in bits 0 .. h - 1, B in bits h .. 2h - 1 (zero below R - a)
    age: np.ndarray  # (n,) int64: a = min(R, h)


def _bit(x: np.ndarray, q: int | np.ndarray) -> np.ndarray:
    """Bit q of each entry, as uint64 0 or 1."""
    return (x >> U64(q) if isinstance(q, int) else x >> q.astype(U64)) & U64(1)


def step_states(s: States, c: int, h: int, P: int) -> tuple[States, np.ndarray, np.ndarray, np.ndarray]:
    """The transition with free value c of the next diagonal at R - a: the new states, the increments R' - R, a bound
    tau with T_{j+1} <= R + tau (exact unless the next diagonal repeats from R - a on, then tau = -a), and a mask of
    the valid transitions (invalid: the next diagonal does not repeat with period P, which happens only behind a
    diagonal white on a whole period)."""
    n = s.pw.shape[0]
    mP = U64((1 << P) - 1)
    mh = U64((1 << h) - 1)
    wa, wb = s.pw & mP, (s.pw >> U64(P)) & mP  # (n,), (n,)
    tile_a = wa | (wa << U64(P)) | (wa << U64(2 * P))  # (n,): A on [0, 3P)
    tile_b = wb | (wb << U64(P)) | (wb << U64(2 * P))  # (n,)
    A = (s.win & mh) | (tile_a << U64(h))  # (n,): bit q = A at time R - h + q
    B = ((s.win >> U64(h)) & mh) | (tile_b << U64(h))  # (n,)
    Q = h + 3 * P
    q0 = (h - s.age).astype(np.int64)  # (n,): bit of the free value
    cval = np.full(n, c, dtype=U64)  # (n,)
    C = np.zeros(n, dtype=U64)  # (n,)
    for q in range(Q):
        C |= cval << U64(q)
        nxt = _bit(A, q) ^ (_bit(B, q) | cval)  # (n,)
        cval = np.where(q + 1 <= q0, U64(c), nxt)
    Cr = C >> U64(h)  # (n,): C on [R, R + 3P)
    mism = (Cr ^ (Cr >> U64(P))) & U64((1 << (2 * P)) - 1)  # (n,): bit u = [C(u) != C(u + P)], u < 2P
    valid = (mism >> U64(P)) == 0  # (n,)
    last = np.zeros(n, dtype=np.int64)  # (n,): one more than the last mismatch, 0 if none
    for u in range(P):
        last = np.where(_bit(mism, u) == 1, u + 1, last)
    delta = last  # (n,)
    full = (C ^ (C >> U64(P))) & U64((1 << (h + 2 * P)) - 1)  # (n,): bit q = [C(q) != C(q + P)] at time R - h + q
    tau = -s.age.copy()  # (n,)
    for q in range(h + P):
        tau = np.where((_bit(full, q) == 1) & (q >= q0), q + 1 - h, tau)
    age = np.minimum(s.age + delta, h)  # (n,)
    d = delta.astype(U64)  # (n,)
    keep = (mh >> (U64(h) - age.astype(U64))) << (U64(h) - age.astype(U64)) if h else np.zeros(n, dtype=U64)  # (n,)
    keep &= mh
    win = ((B >> d) & keep) | (((C >> d) & keep) << U64(h))  # (n,)
    pw = ((B >> (d + U64(h))) & mP) | (((C >> (d + U64(h))) & mP) << U64(P))  # (n,)
    return States(pw, win, age), delta, tau, valid


def state_keys(s: States, h: int, P: int) -> np.ndarray:
    """One uint64 per state: pw in the high 2P bits, then the age, then the window (needs 2P + 2h + 5 <= 64)."""
    assert 2 * P + 2 * h + 5 <= 64
    return (s.pw << U64(2 * h + 5)) | (s.age.astype(U64) << U64(2 * h)) | s.win


def from_keys(key: np.ndarray, h: int, P: int) -> States:
    """The inverse of `state_keys`."""
    return States(key >> U64(2 * h + 5), key & U64((1 << (2 * h)) - 1),
                  ((key >> U64(2 * h)) & U64(31)).astype(np.int64))


def start_state(P: int) -> States:
    """Depth 0: the pair (D_{-1}, D_0) = (white, black) from time 0, R_0 = 0."""
    return States(np.array([((1 << P) - 1) << P], dtype=U64), np.zeros(1, dtype=U64), np.zeros(1, dtype=np.int64))


@dataclass(frozen=True, slots=True)
class WindowRun:
    bound: np.ndarray  # (J + 1,) U_j, the largest R over the abstract states at depth j
    states: np.ndarray  # (J + 1,) number of abstract states at depth j
    exact: np.ndarray  # (J + 1,) True while every state has a < h (the abstraction is then exact)
    onset: np.ndarray  # (J + 1,) V_j >= T_j for every seed: the largest R + tau over the transitions into depth j
    keys: np.ndarray | None = None  # (n,) the state keys at depth J (`state_keys`), increasing
    values: np.ndarray | None = None  # (n,) the largest R reaching each


def window_bounds(J: int, h: int, P: int = 16, progress: bool = True) -> WindowRun:
    """U_j >= R_j over every seed, for j <= J, by the window abstraction of width h run depth by depth. P must be a
    multiple of every period to depth J (16 below depth 87,867 for the single cell; the run stops with an error if a
    transition leaves period P)."""
    s = start_state(P)
    R = np.zeros(1, dtype=np.int64)  # (n,)
    bound = np.zeros(J + 1, dtype=np.int64)  # (J + 1,)
    count = np.ones(J + 1, dtype=np.int64)  # (J + 1,)
    exact = np.zeros(J + 1, dtype=bool)  # (J + 1,)
    exact[0] = True
    onset = np.zeros(J + 1, dtype=np.int64)  # (J + 1,)
    for j in tqdm(range(J), desc=f"window h={h}", file=sys.stderr, mininterval=5, disable=not progress):
        keys, vals = [], []
        for c in (0, 1):
            t, delta, tau, valid = step_states(s, c, h, P)
            assert valid.all(), f"a transition at depth {j} leaves period {P}"
            onset[j + 1] = max(onset[j + 1], int((R + tau).max()))
            keys.append(state_keys(t, h, P))
            vals.append(R + delta)
        key = np.concatenate(keys)  # (2n,)
        val = np.concatenate(vals)  # (2n,)
        order = np.lexsort((val, key))  # (2n,): by key, then value
        key, val = key[order], val[order]
        last = np.r_[key[1:] != key[:-1], True]  # (2n,): the largest value of each key is last
        key, R = key[last], val[last]
        s = from_keys(key, h, P)
        bound[j + 1], count[j + 1] = R.max(), len(R)
        exact[j + 1] = bool((s.age < h).all()) if h else False
    return WindowRun(bound, count, exact, onset, key, R)


def window_bounds_c(J: int, h: int, P: int = 16, threads: int = 1, progress: bool = False) -> WindowRun:
    """`window_bounds` by `seed_certificate_window.c` (dense arrays, 8 times per table step); `exact` is not reported
    (all False). Raises RuntimeError with the depth if a transition leaves period P."""
    run = subprocess.run([str(_binary("seed_certificate_window")), str(J), str(h), str(P)], stdout=subprocess.PIPE,
                         stderr=None if progress else subprocess.PIPE, text=True,
                         env={**os.environ, "OMP_NUM_THREADS": str(threads)})
    if run.returncode != 0:
        raise RuntimeError(f"window run stopped (code {run.returncode}): {run.stderr}")
    rows = np.array([[int(x) for x in ln.split()] for ln in run.stdout.strip().splitlines()], dtype=np.int64)
    # rows: (J + 1, 5): j, U_j, V_j, states, words
    assert (rows[:, 0] == np.arange(J + 1)).all()
    return WindowRun(rows[:, 1].copy(), rows[:, 3].copy(), np.zeros(J + 1, dtype=bool), rows[:, 2].copy())


# ---------------------------------------------------------------------------------------------------------------------
# The pair graph and its mean payoff


@dataclass(frozen=True, slots=True)
class Graph:
    keys: np.ndarray  # (n,) state keys (`state_keys`)
    succ: np.ndarray  # (n, 2) index of the successor for c = 0, 1 (-1 if the transition is invalid or leaves the set)
    weight: np.ndarray  # (n, 2) the increment R' - R


def pair_graph(P: int, h: int) -> Graph:
    """Every pair word of period P (2^{2P} of them, read at R) with every age a <= h and every window of width h that
    is zero below R - a, and the two transitions of each. States without a valid successor are removed until none is
    left."""
    words = np.arange(1 << (2 * P), dtype=U64)  # (4^P,)
    parts = []
    for a in range(h + 1):
        low = np.arange(1 << a, dtype=U64) << U64(h - a)  # (2^a,): window halves zero below R - a
        wins = (low[:, None] | (low[None, :] << U64(h))).ravel()  # (4^a,)
        parts.append((np.repeat(words, len(wins)), np.tile(wins, len(words)), np.full(len(words) * len(wins), a)))
    pw = np.concatenate([p[0] for p in parts])  # (n,)
    win = np.concatenate([p[1] for p in parts])  # (n,)
    age = np.concatenate([p[2] for p in parts]).astype(np.int64)  # (n,)
    s = States(pw, win, age)
    order = np.argsort(state_keys(s, h, P))  # (n,)
    s = States(pw[order], win[order], age[order])
    keys = state_keys(s, h, P)  # (n,), increasing
    succ = np.full((len(keys), 2), -1, dtype=np.int64)  # (n, 2)
    weight = np.zeros((len(keys), 2), dtype=np.int64)  # (n, 2)
    for c in (0, 1):
        t, delta, _, valid = step_states(s, c, h, P)
        k = state_keys(t, h, P)  # (n,)
        pos = np.minimum(np.searchsorted(keys, k), len(keys) - 1)  # (n,)
        assert (keys[pos][valid] == k[valid]).all()
        succ[:, c] = np.where(valid, pos, -1)
        weight[:, c] = delta
    alive = np.ones(len(keys), dtype=bool)  # (n,)
    while True:
        ok = (succ >= 0) & alive[np.maximum(succ, 0)]  # (n, 2)
        new = alive & ok.any(axis=1)  # (n,)
        if new.sum() == alive.sum():
            break
        alive = new
    index = np.cumsum(alive) - 1  # (n,)
    ok = (succ >= 0) & alive[np.maximum(succ, 0)]  # (n, 2)
    succ = np.where(ok, index[np.maximum(succ, 0)], -1)[alive]  # (m, 2)
    return Graph(keys[alive], succ, weight[alive])


def _cycles(nxt: np.ndarray, w: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """For the functional graph v -> nxt[v] with weights w[v]: a node on the cycle each node reaches (its least
    index), and the weight sum and length of each node's cycle (indexed by that representative)."""
    n = len(nxt)
    jump = nxt.copy()  # (n,)
    steps = 1
    while steps < n:
        jump = jump[jump]
        steps *= 2
    on = np.zeros(n, dtype=bool)  # (n,)
    on[jump] = True  # nxt^(2^K)(v) is on a cycle, and every cycle node is reached by itself
    rep = np.arange(n)  # (n,)
    hop = nxt.copy()  # (n,)
    steps = 1
    while steps < n:
        rep = np.minimum(rep, rep[hop])
        hop = hop[hop]
        steps *= 2
    rep_of = rep[jump]  # (n,): least node of the cycle reached
    total = np.bincount(rep[on], weights=w[on], minlength=n).astype(np.int64)  # (n,)
    length = np.bincount(rep[on], minlength=n).astype(np.int64)  # (n,)
    return rep_of, total, length


def max_cycle_mean(g: Graph, max_rounds: int = 200) -> tuple[Fraction, np.ndarray]:
    """The largest mean weight of a cycle of the graph, by Howard's policy iteration, and a cycle (node indices) that
    attains it."""
    n = len(g.succ)
    choice = np.argmax(np.where(g.succ >= 0, g.weight, -10**9), axis=1)  # (n,)
    for _ in range(max_rounds):
        nxt = g.succ[np.arange(n), choice]  # (n,)
        w = g.weight[np.arange(n), choice]  # (n,)
        rep, total, length = _cycles(nxt, w)
        eta = total[rep] / length[rep]  # (n,) float: the mean of the cycle each node reaches
        x = _bias(nxt, w, eta, rep)
        cand_eta = np.where(g.succ >= 0, eta[np.maximum(g.succ, 0)], -np.inf)  # (n, 2)
        cand_x = np.where(g.succ >= 0, g.weight - eta[:, None] + x[np.maximum(g.succ, 0)], -np.inf)  # (n, 2)
        best_eta = cand_eta.max(axis=1)  # (n,)
        improve_eta = best_eta > eta + 1e-9  # (n,)
        new = choice.copy()  # (n,)
        new[improve_eta] = np.argmax(cand_eta[improve_eta], axis=1)
        rest = ~improve_eta
        cx = np.where(np.abs(cand_eta - eta[:, None]) < 1e-9, cand_x, -np.inf)  # (n, 2)
        better = rest & (cx.max(axis=1) > x + 1e-9)  # (n,)
        new[better] = np.argmax(cx[better], axis=1)
        if (new == choice).all():
            break
        choice = new
    else:
        raise RuntimeError("policy iteration did not converge")
    k = int(np.argmax(eta))
    r = int(rep[k])
    cycle = [r]
    v = int(nxt[r])
    while v != r:
        cycle.append(v)
        v = int(nxt[v])
    return Fraction(int(total[r]), int(length[r])), np.array(cycle)


def _bias(nxt: np.ndarray, w: np.ndarray, eta: np.ndarray, rep: np.ndarray) -> np.ndarray:
    """x with x(v) = w(v) - eta(v) + x(nxt v) for every node but the cycle representatives, where x = 0: the sum of
    w - eta along the path from v to its representative, by pointer doubling."""
    n = len(nxt)
    idx = np.arange(n)
    is_rep = idx == rep  # (n,)
    acc = np.where(is_rep, 0.0, w - eta)  # (n,)
    hop = np.where(is_rep, idx, nxt)  # (n,)
    steps = 1
    while steps < n:
        acc = acc + acc[hop]
        hop = hop[hop]
        steps *= 2
    return acc  # (n,)


def check_certificate(g: Graph, mean: Fraction, rounds: int = 100000) -> np.ndarray:
    """An integer potential Phi with den w - num + Phi(target) <= Phi(source) on every edge (mean = num / den), the
    longest-path values of those weights, found by value iteration; it exists exactly when no cycle has a mean above
    `mean`. Every edge is checked before it is returned."""
    num, den = mean.numerator, mean.denominator
    W = np.where(g.succ >= 0, den * g.weight - num, -(1 << 40))  # (n, 2)
    tgt = np.maximum(g.succ, 0)  # (n, 2)
    phi = np.zeros(len(g.succ), dtype=np.int64)  # (n,)
    for _ in range(rounds):
        new = np.maximum(0, (W + phi[tgt]).max(axis=1))  # (n,)
        if (new == phi).all():
            break
        phi = new
    else:
        raise RuntimeError("no potential: a cycle has a larger mean")
    ok = (g.succ < 0) | (W + phi[tgt] <= phi[:, None])  # (n, 2)
    assert ok.all()
    return phi  # (n,)


def describe(g: Graph, cycle: np.ndarray, h: int, P: int) -> list[str]:
    """The states of a cycle as text: the pair word A | B at R (times R .. R + P - 1), the window, and the increment."""
    s = from_keys(g.keys[cycle], h, P)
    out = []
    for i, v in enumerate(cycle):
        a = "".join(str((int(s.pw[i]) >> k) & 1) for k in range(P))
        b = "".join(str((int(s.pw[i]) >> (P + k)) & 1) for k in range(P))
        nxt = cycle[(i + 1) % len(cycle)]
        cs = np.flatnonzero(g.succ[v] == nxt)  # (·,): parallel edges, the heavier is on the cycle
        c = int(cs[np.argmax(g.weight[v, cs])])
        out.append(f"A={a} B={b} window={int(s.win[i]):0{2 * h}b} c={c} increment={g.weight[v, c]}")
    return out


def so_scalar(depth: int) -> np.ndarray:
    """Onsets of diagonals 0 .. depth of the seed x_3 = 1 (black cells at lo and lo + 3)."""
    return scalar_onsets(seed_vector("001"), depth, 2 * depth + 200, 64)  # (depth + 1,)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--jumps", type=int, default=0, help="c_n for n up to this depth")
    parser.add_argument("--graph", type=int, default=0, help="period P of the pair graph")
    parser.add_argument("--window", type=int, default=0, help="window bounds to this depth")
    parser.add_argument("--widths", default="0,2,4", help="window widths h")
    parser.add_argument("--beam", default="", help="driven beam behind these depths n (comma separated)")
    parser.add_argument("--seeds", type=int, default=0, help="beam over seeds and window bound to this depth")
    parser.add_argument("--threads", type=int, default=2)
    parser.add_argument("--save", default="", help="save U_j, V_j and the state counts as <save>_h<h>.npy")
    parser.add_argument("--k", type=int, default=60)
    parser.add_argument("--beam-width", type=int, default=256)
    args = parser.parse_args()
    widths = [int(x) for x in args.widths.split(",")]

    if args.jumps:
        depth = args.jumps
        d = stream(depth, 3 * depth // 2 + 600, period=64, window=256)
        c = jump_costs(d.tail)  # (depth + 1,)
        period = least_periods(d.tail)  # (depth + 1,)
        print(f"c_n = 1 + longest white run of the periodic part of D_n, n <= {depth}:")
        for p in sorted(set(period[c > 0].tolist())):
            sel = np.flatnonzero((period == p) & (c > 0))  # (·,)
            print(f"  period {p:>3}: depths {sel.min()} .. {sel.max()}, largest c_n = {c[sel].max()} "
                  f"(first at n = {sel[np.argmax(c[sel])]})")

    if args.graph:
        P = args.graph
        for h in widths:
            g = pair_graph(P, h)
            mean, cycle = max_cycle_mean(g)
            phi = check_certificate(g, mean)
            print(f"P = {P}, h = {h}: {len(g.succ)} states, largest cycle mean {mean} = {float(mean):.4f}, "
                  f"cycle of length {len(cycle)}, potential range {int(phi.max() - phi.min())} (in units 1/{mean.denominator})")
            for line in describe(g, cycle, h, P)[:16]:
                print("   ", line)

    if args.window:
        J = args.window
        j = np.arange(J + 1)  # (J + 1,)
        for h in widths:
            try:
                run = window_bounds_c(J, h, P=8 if J <= 398 else 16, threads=args.threads, progress=True)
            except RuntimeError as err:
                print(f"h = {h}: {err}")
                continue
            ex = run.onset - ceil_three_halves(j)  # (J + 1,)
            over = np.flatnonzero(ex > 5)  # (·,)
            print(f"h = {h}, depths 0 .. {J}: largest V_j - ceil(3j/2) = {int(ex.max())} (at j = {int(np.argmax(ex))}); "
                  f"first j with V_j > ceil(3j/2) + 5: {int(over[0]) if over.size else 'none'}; "
                  f"largest U_j - ceil(3j/2) = {int((run.bound - ceil_three_halves(j)).max())}; "
                  f"largest number of states {run.states.max()}")
            cuts = [c for c in (0, 76, 100, 200, 400, 1000, 4000, 10000, 20000, 40000, 53207, 87867) if c < J] + [J]
            for lo, hi in zip(cuts[:-1], cuts[1:]):
                print(f"   j in [{lo}, {hi}]: slope of U {(run.bound[hi] - run.bound[lo]) / (hi - lo):.4f}, "
                      f"largest V_j - ceil(3j/2) {int(ex[lo:hi + 1].max())}")
            if args.save:
                np.save(f"{args.save}_h{h}.npy", np.stack([run.bound, run.onset, run.states]))

    if args.beam:
        depths = [int(x) for x in args.beam.split(",")]
        assert max(depths) + args.k <= 398, "period 8 holds below depth 399"
        N = driven_scan(depths, args.k, args.beam_width)  # (len(depths), k)
        m = np.arange(1, args.k + 1)  # (k,)
        print(f"driven beam, k <= {args.k}, width {args.beam_width}: the largest N_(n,m) - ceil(3m/2) over m <= k, "
              f"and N_(n,k)")
        for r, n in enumerate(depths):
            ex = N[r] - ceil_three_halves(m)  # (k,)
            print(f"  n = {n:>3}: {int(ex.max())} at m = {int(np.argmax(ex)) + 1}; N_(n,{args.k}) = {N[r, -1]} "
                  f"({N[r, -1] / args.k:.3f} k)")

    if args.seeds:
        L = driven_beam(np.zeros(16, dtype=np.uint8), np.ones(16, dtype=np.uint8), args.seeds, args.beam_width, P=16)
        L = np.concatenate([[0], L])  # (seeds + 1,)
        run = window_bounds_c(args.seeds, 8, P=16, threads=2)
        two = so_scalar(args.seeds)  # (seeds + 1,)
        low = np.maximum(L, two)  # (seeds + 1,)
        exact = np.flatnonzero(run.onset == low)  # (·,)
        print(f"seeds by beam (width {args.beam_width}) and the seed x_3 = 1 against the window bound h = 8:")
        print(f"  M_j determined (V_j attained) for j in {exact[exact >= 77].tolist()}")
        print(f"  their values: {run.onset[exact[exact >= 77]].tolist()}; attained by x_3 = 1 at "
              f"{[int(x) for x in exact[exact >= 77] if two[x] == run.onset[x]]}")
        j = np.arange(args.seeds + 1)  # (seeds + 1,)
        for lo in range(0, args.seeds + 1, 100):
            sl = slice(lo, lo + 100)
            print(f"  j in [{lo}, {min(lo + 99, args.seeds)}]: max V_j - lower {int((run.onset - low)[sl].max())}, "
                  f"max lower - ceil(3j/2) {int((low - ceil_three_halves(j))[sl].max())}")


if __name__ == "__main__":
    main()
