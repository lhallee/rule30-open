"""The largest density of black cells over every center column that the left half allows, and how dense words chain.

Lambda_L is the set of drivers c(0) = 1, c(1), c(2), ... that obey the left-only constraint of `constrained_runs`:
with the left half x driven by c from a white start, c(t + 1) = not x_{-1}(t) whenever c(t) = 1; after a white center
the next value is free. The single cell's center column lies in Lambda_L. A state at time t is the pair (left half at
time t, c(t)); a white state has two successors and a black state one.

1. `driver_dp`: for every reachable state, the largest number of black cells among c(0 .. t) over the drivers that
   reach it, layer by layer with the states deduplicated (exact), or keeping the `beam` states with the largest counts
   (a lower bound). M(T) is the largest count over the states at time T; with `forks`, G(s, T) is the largest count of
   black cells among c(s .. T) from any state reachable at time s, which bounds the gain of every driver on [s, T].
   With `track` it keeps one driver per state that attains the count, so the last layer gives an optimal driver.
2. `follow_lengths`: for each state at time t and a periodic word w, the most letters c(t), c(t + 1), ... that an
   admissible driver can take from w in phase, over every phase with w[phase] = c(t). l_w(t) is its maximum over
   the reachable states (`lifetimes`, from `constrained_runs.constrained_states`).
3. `reentry`: from the ends of the longest w-stretches from time t (every state and phase attaining l_w(t)), the
   least number g of further steps after which some reachable state again has l_w >= l_w(t) / 2, with the most black
   cells a driver puts in those g steps.
4. `chain_beam`: a beam over the same states with extra moves that jump to the end of a maximal w-stretch, so dense
   stretches whose intermediate states would fall out of the beam survive.
5. `describe`: run lengths of an optimal driver, its forced and chosen white cells, and a check that each black run
   lasts exactly as long as the alternating right end of the left half at its start allows.
6. `potential`: the least slope that a potential theta . features(s) over a fixed basis of 27 features certifies on the
   reachable graph up to time `fit`, and what the same theta needs on the later edges up to `test`.

    python -m computations.driver_density exact --steps 190 --every 5 --forks 60,90,120   # about 7 min, 4 GB
    python -m computations.driver_density beam --steps 3000 --width 60000 --track        # about 11 min
    python -m computations.driver_density beam --steps 1000 --width 240000               # about 5 min
    python -m computations.driver_density lifetimes --steps 170 --every 10               # about 6 min, 2 GB
    python -m computations.driver_density reentry --times 40,80,120,160                    # about 1 min
    python -m computations.driver_density chain --steps 1000 --width 20000                 # about 6 min
    python -m computations.driver_density describe --steps 160 --beam-steps 3000          # about 15 min
    python -m computations.driver_density potential --fit 60 --test 100 --bounds 1,10,1000   # about 6 min
"""

from __future__ import annotations

import argparse
import itertools
import math
import sys
from collections import Counter
from collections.abc import Iterator, Sequence
from dataclasses import dataclass, field

import numpy as np
from tqdm.auto import tqdm

from computations.constrained_runs import constrained_states
from computations.run_mechanism import black_reach, driven_step

ONE = np.uint64(1)

# ---------------------------------------------------------------------------------------------------------------------
# 1. Largest black counts by dynamic programming over the reachable states
# ---------------------------------------------------------------------------------------------------------------------
# A left half is a multiword integer as in run_mechanism: bit k - 1 of X[i] is cell -k at time t. c[i] is c(t),
# V[i, 0] the largest count of black cells among c(0 .. t), V[i, f] the largest count among c(s_f .. t) for fork s_f.


def successors(X: np.ndarray, c: np.ndarray, V: np.ndarray, D: np.ndarray | None,
               t: int) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray | None]:
    """Every admissible successor at time t + 1 of the states at time t, with the counts and drivers carried."""
    # X: (n, W) uint64; c: (n,) uint8; V: (n, F) int16; D: (n, Wd) uint64 or None
    white = c == 0  # (n,)
    Xw = driven_step(X[white], 0)  # (nw, W)
    Xb_old = X[~white]  # (nb, W)
    forced = (ONE ^ (Xb_old[:, 0] & ONE)).astype(np.uint8)  # (nb,), not cell -1 at time t
    Xb = driven_step(Xb_old, 1)  # (nb, W)
    del Xb_old
    Vw = V[white]  # (nw, F)
    Vb = V[~white] + forced[:, None].astype(np.int16)  # (nb, F)
    nw = len(Xw)
    Xn = np.concatenate([Xw, Xw, Xb])  # (2 nw + nb, W)
    cn = np.concatenate([np.zeros(nw, np.uint8), np.ones(nw, np.uint8), forced])  # (2 nw + nb,)
    Vn = np.concatenate([Vw, Vw + np.int16(1), Vb])  # (2 nw + nb, F)
    Dn = None
    if D is not None:
        Dw = D[white]  # (nw, Wd)
        D1 = Dw.copy()  # (nw, Wd)
        D1[:, (t + 1) // 64] |= ONE << np.uint64((t + 1) % 64)
        Db = D[~white].copy()  # (nb, Wd)
        Db[:, (t + 1) // 64] |= forced.astype(np.uint64) << np.uint64((t + 1) % 64)
        Dn = np.concatenate([Dw, D1, Db])  # (2 nw + nb, Wd)
    return Xn, cn, Vn, Dn


def dedupe_max(X: np.ndarray, c: np.ndarray, V: np.ndarray, D: np.ndarray | None,
               active: int) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray | None]:
    """Merge equal states, keeping the largest count in each column of V (and a driver attaining column 0). Only the
    first `active` words of X can be nonzero."""
    # X: (n, W); c: (n,); V: (n, F); D: (n, Wd) or None
    keys = [X[:, j] for j in range(active)] + [c]
    if D is not None:
        keys = [V[:, 0]] + keys  # least significant: the last of each group attains the largest count
    order = np.lexsort(keys)  # (n,)
    Xs = X[order]  # (n, W)
    cs = c[order]  # (n,)
    new = np.ones(len(order), dtype=bool)  # (n,)
    new[1:] = (cs[1:] != cs[:-1]) | (Xs[1:, :active] != Xs[:-1, :active]).any(axis=1)
    first = np.flatnonzero(new)  # (m,)
    last = np.append(first[1:], len(order)) - 1  # (m,)
    Vm = np.maximum.reduceat(V[order], first, axis=0)  # (m, F)
    Dm = D[order[last]] if D is not None else None
    return Xs[first], cs[first], Vm, Dm


@dataclass
class DPRow:
    t: int
    states: int  # states kept at time t (all reachable ones in the exact run)
    best: int  # M(t): the largest count of black cells among c(0 .. t)
    gains: dict[int, int] = field(default_factory=dict)  # fork s -> G(s, t)
    driver: list[int] | None = None  # c(0 .. t) of a driver attaining `best`, with `track`


def driver_bits(D: np.ndarray, t: int) -> list[int]:
    """c(0 .. t) from a packed driver (bit u of the row is c(u))."""
    # D: (Wd,) uint64
    return [int(D[u // 64] >> np.uint64(u % 64)) & 1 for u in range(t + 1)]


def driver_dp(steps: int, forks: Sequence[int] = (), beam: int | None = None, track: bool = False,
              progress: bool = False) -> Iterator[DPRow]:
    """Yield a DPRow for t = 0 .. steps. Exact when `beam` is None; otherwise only the `beam` states with the largest
    counts are kept after each step, so `best` is a lower bound (attained by a driver)."""
    W = steps // 64 + 1
    Wd = steps // 64 + 1
    F = 1 + len(forks)
    fork_col = {s: 1 + i for i, s in enumerate(forks)}
    X = np.zeros((1, W), dtype=np.uint64)  # (1, W)
    c = np.ones(1, dtype=np.uint8)  # (1,)
    V = np.ones((1, F), dtype=np.int16)  # (1, F)
    D = np.ones((1, Wd), dtype=np.uint64) if track else None  # (1, Wd)
    if D is not None:
        D[:, 1:] = 0
    for t in tqdm(range(steps + 1), desc="driver dp", file=sys.stderr, disable=not progress):
        if t in fork_col:
            V[:, fork_col[t]] = c
        k = int(np.argmax(V[:, 0]))
        row = DPRow(t, len(c), int(V[k, 0]), {s: int(V[:, f].max()) for s, f in fork_col.items() if s <= t})
        if D is not None:
            row.driver = driver_bits(D[k], t)
        yield row
        if t == steps:
            return
        X, c, V, D = successors(X, c, V, D, t)
        X, c, V, D = dedupe_max(X, c, V, D, min(W, (t + 1) // 64 + 1))
        if beam is not None and len(c) > beam:
            keep = np.argpartition(-V[:, 0], beam - 1)[:beam]  # (beam,)
            keep.sort()
            X, c, V = X[keep], c[keep], V[keep]
            D = D[keep] if D is not None else None


def admissible_drivers(n: int) -> Iterator[tuple[int, ...]]:
    """Every admissible driver word c(0) .. c(n - 1), by depth-first search with the left half carried along."""
    W = n // 64 + 1

    def go(word: list[int], X: np.ndarray) -> Iterator[tuple[int, ...]]:
        # X: (1, W), the left half at time len(word) - 1
        if len(word) == n:
            yield tuple(word)
            return
        cur = word[-1]
        nxt = driven_step(X, cur)  # (1, W)
        options = (1 - int(X[0, 0] & ONE),) if cur == 1 else (0, 1)
        for d in options:
            yield from go(word + [d], nxt)

    yield from go([1], np.zeros((1, W), dtype=np.uint64))


def brute_best(T: int) -> int:
    """M(T) by enumerating every admissible driver of length T + 1."""
    return max(sum(w) for w in admissible_drivers(T + 1))


# ---------------------------------------------------------------------------------------------------------------------
# 2. Lifetimes of periodic words
# ---------------------------------------------------------------------------------------------------------------------


def primitive_words(pmax: int, min_density: float) -> list[str]:
    """One representative (the lexicographically largest rotation) of every primitive cyclic word of period at most
    pmax with a share of 1s at least min_density."""
    out: list[str] = []
    for p in range(1, pmax + 1):
        for bits in itertools.product("01", repeat=p):
            w = "".join(bits)
            if w.count("1") < min_density * p:
                continue
            if any(p % d == 0 and w == w[:d] * (p // d) for d in range(1, p)):
                continue
            if w != max(w[i:] + w[:i] for i in range(p)):
                continue
            out.append(w)
    return out


def follow_lengths(X: np.ndarray, c: np.ndarray, w: str, horizon: int,
                   phases: Sequence[int] | None = None) -> np.ndarray:
    """For each state (X, c) at some time t, the most letters c(t), c(t + 1), ... an admissible driver takes from the
    periodic word w in phase, over every phase with w[phase] = c(t) (or over `phases` only), capped at `horizon`.
    Cell -1 at time t + s depends only on cells -1 .. -(s + 1), so the first horizon // 64 + 1 words of X suffice."""
    # X: (n, W) uint64; c: (n,) uint8
    p = len(w)
    letters = [int(a) for a in w]
    Wh = min(X.shape[1], horizon // 64 + 1)
    out = np.zeros(len(c), dtype=np.int64)  # (n,)
    for ph in (range(p) if phases is None else phases):
        idx = np.flatnonzero(c == letters[ph])  # (m,)
        Y = X[idx, :Wh].copy()  # (m, Wh)
        s = 0
        while len(idx) and s < horizon:
            cur = letters[(ph + s) % p]
            s += 1
            out[idx] = np.maximum(out[idx], s)
            if s == horizon:
                break
            if cur == 1:
                ok = (ONE ^ (Y[:, 0] & ONE)) == np.uint64(letters[(ph + s) % p])  # (m,)
                idx, Y = idx[ok], Y[ok]
            Y = driven_step(Y, cur)
    return out  # (n,)


@dataclass
class LifeRow:
    t: int
    states: int
    lengths: dict[str, int]  # w -> l_w(t)


def lifetimes(steps: int, every: int, words: Sequence[str], horizon: int = 120,
              progress: bool = False) -> Iterator[LifeRow]:
    """l_w(t) over every reachable state at t = every, 2 every, ..., steps, for each word w."""
    for t, B, C in constrained_states(steps, progress):
        if t == 0 or t % every:
            continue
        yield LifeRow(t, len(C), {w: int(follow_lengths(B, C, w, horizon).max()) for w in words})


# ---------------------------------------------------------------------------------------------------------------------
# 3. Re-entry cost
# ---------------------------------------------------------------------------------------------------------------------


def _states_at(t: int) -> tuple[np.ndarray, np.ndarray]:
    for u, B, C in constrained_states(t):
        if u == t:
            return B, C
    raise ValueError(t)


@dataclass
class Reentry:
    w: str
    t: int
    length: int  # l_w(t)
    target: int  # ceil(l_w(t) / 2)
    ends: int  # distinct end states (time t + l, center forced off w) over every state and phase attaining l_w(t)
    gap: int | None  # least g over the ends with a state at t + l + g whose follow length reaches target (None: none)
    gap_max: int | None  # the largest such least g over the ends (None: some end has none by gmax)
    gap_black: int | None  # most black cells among c(t + l .. t + l + g - 1), at an end attaining `gap`
    stretch_black: int  # black cells in the w-stretch c(t .. t + l - 1) ending there


def _gap(Xg: np.ndarray, cg: np.ndarray, w: str, target: int, gmax: int, horizon: int,
         cap: int) -> tuple[int | None, int | None]:
    """From one state, the least g with a state g steps later whose follow length reaches target, and the most black
    cells among the g cells before it; (None, None) if there is none by gmax."""
    # Xg: (1, W) uint64; cg: (1,) uint8
    W = Xg.shape[1]
    Vg = np.full((1, 1), int(cg[0]), dtype=np.int16)  # (1, 1), black cells from the end state's time to now
    for g in range(gmax + 1):
        ok = follow_lengths(Xg, cg, w, horizon) >= target  # (m,)
        if ok.any():
            return g, int((Vg[ok, 0] - cg[ok]).max())  # c(now) starts the next stretch, not the gap
        Xg, cg, Vg, _ = successors(Xg, cg, Vg, None, 0)
        Xg, cg, Vg, _ = dedupe_max(Xg, cg, Vg, None, W)
        if len(cg) > cap:
            raise MemoryError(f"layer {g + 1} has {len(cg)} states")
    return None, None


def reentry(w: str, t: int, gmax: int = 40, horizon: int = 120, cap: int = 1 << 22,
            states: tuple[np.ndarray, np.ndarray] | None = None) -> Reentry:
    """From the end of every longest w-stretch starting at time t (every reachable state and phase that attains
    l_w(t)), the least number of steps to a state that again follows w for at least half as long, by breadth-first
    search over admissible drivers (a layer above `cap` states raises). The reported gap is the least over the ends,
    so it is the cheapest re-entry. `states` are the reachable states at time t, if already computed."""
    B, C = states if states is not None else _states_at(t)
    W = (t + horizon + gmax + 4) // 64 + 1
    X = np.zeros((len(C), W), dtype=np.uint64)  # (n, W)
    X[:, :B.shape[1]] = B
    p = len(w)
    letters = [int(a) for a in w]
    per = np.stack([follow_lengths(X, C, w, horizon, phases=[ph]).astype(np.int16) for ph in range(p)])  # (p, n)
    L = int(per.max())
    ends: dict[tuple[bytes, int], tuple[np.ndarray, int]] = {}  # end state -> (its left half, most stretch black)
    for ph, k in np.argwhere(per == L):
        Y = X[k:k + 1].copy()  # (1, W)
        cur = int(C[k])
        for s in range(L):  # follow w for L letters; the letter at t + L is forced and leaves w
            nxt = 1 - int(Y[0, 0] & ONE) if cur == 1 else letters[(ph + s + 1) % p]
            assert s == L - 1 or nxt == letters[(ph + s + 1) % p]
            Y = driven_step(Y, cur)
            cur = nxt
        assert cur != letters[(ph + L) % p]
        black = sum(letters[(ph + s) % p] for s in range(L))
        key = (Y.tobytes(), cur)
        ends[key] = (Y, max(black, ends[key][1] if key in ends else 0))
    target = math.ceil(L / 2)
    found: list[tuple[int, int, int]] = []  # (gap, gap black, stretch black) per end with a re-entry
    missing = False
    for (_, cur), (Y, black) in ends.items():
        g, gb = _gap(Y, np.array([cur], dtype=np.uint8), w, target, gmax, horizon, cap)
        if g is None or gb is None:
            missing = True
        else:
            found.append((g, gb, black))
    if not found:
        return Reentry(w, t, L, target, len(ends), None, None, None, max(b for _, b in ends.values()))
    g, gb, black = min(found, key=lambda z: (z[0], -(z[1] + z[2]) / (L + z[0])))
    return Reentry(w, t, L, target, len(ends), g, None if missing else max(z[0] for z in found), gb, black)


# ---------------------------------------------------------------------------------------------------------------------
# 4. A beam with jumps along dense words
# ---------------------------------------------------------------------------------------------------------------------


def stretch_ends(X: np.ndarray, c: np.ndarray, w: str, min_len: int,
                 limit: int) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """For each state and phase with a maximal w-stretch of at least min_len and at most `limit` letters: the row it
    starts from, the state at its end (time t + length, whose center is forced off w), the length and the black
    cells in the stretch."""
    # X: (n, W); c: (n,)
    p = len(w)
    letters = [int(a) for a in w]
    src, outX, outc, outL, outV = [], [], [], [], []
    for ph in range(p):
        idx = np.flatnonzero(c == letters[ph])  # (m,)
        Y = X[idx].copy()  # (m, W)
        s, black = 0, 0
        while len(idx) and s < limit:
            cur = letters[(ph + s) % p]
            black += cur
            s += 1
            nxt = letters[(ph + s) % p]
            if cur == 1:
                forced = (ONE ^ (Y[:, 0] & ONE)).astype(np.uint8)  # (m,)
                dead = forced != nxt  # (m,)
                if s >= min_len and dead.any():
                    src.append(idx[dead])
                    outX.append(driven_step(Y[dead], 1))
                    outc.append(forced[dead])
                    outL.append(np.full(int(dead.sum()), s))
                    outV.append(np.full(int(dead.sum()), black))
                idx, Y = idx[~dead], Y[~dead]
            Y = driven_step(Y, cur)
    if not src:
        return (np.zeros(0, np.int64), np.zeros((0, X.shape[1]), np.uint64), np.zeros(0, np.uint8),
                np.zeros(0, np.int64), np.zeros(0, np.int64))
    return (np.concatenate(src), np.concatenate(outX), np.concatenate(outc), np.concatenate(outL),
            np.concatenate(outV))


def _prune(X: np.ndarray, c: np.ndarray, V: np.ndarray, width: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    # X: (n, W); c: (n,); V: (n, F)
    if len(c) <= width:
        return X, c, V
    keep = np.argpartition(-V[:, 0], width - 1)[:width]  # (width,)
    keep.sort()
    return X[keep], c[keep], V[keep]


def chain_beam(steps: int, width: int, words: Sequence[str], min_len: int = 8,
               progress: bool = False) -> Iterator[DPRow]:
    """A beam of `width` states like `driver_dp`, where each kept state also jumps to the end of every maximal
    w-stretch of at least min_len letters from it (w in words), landing in a later layer without being pruned on the
    way. Every count is attained by an admissible driver, so `best` is a lower bound on M(t)."""
    W = (steps + 2) // 64 + 1
    pending: dict[int, list[tuple[np.ndarray, np.ndarray, np.ndarray]]] = {}
    X = np.zeros((1, W), dtype=np.uint64)  # (1, W)
    c = np.ones(1, dtype=np.uint8)  # (1,)
    V = np.ones((1, 1), dtype=np.int16)  # (1, 1)
    for t in tqdm(range(steps + 1), desc="chain beam", file=sys.stderr, disable=not progress):
        if t in pending:
            parts = pending.pop(t)
            X = np.concatenate([X] + [a for a, _, _ in parts])
            c = np.concatenate([c] + [b for _, b, _ in parts])
            V = np.concatenate([V] + [v for _, _, v in parts])
            X, c, V, _ = dedupe_max(X, c, V, None, W)
            X, c, V = _prune(X, c, V, width)
        yield DPRow(t, len(c), int(V[:, 0].max()))
        if t == steps:
            return
        for w in words:
            src, eX, ec, eL, eV = stretch_ends(X, c, w, min_len, steps - t)
            for L in np.unique(eL):
                sel = eL == L  # (k,)
                # c(t) is the first letter of the stretch, counted in both V and eV
                vals = V[src[sel], 0].astype(np.int64) - c[src[sel]] + eV[sel] + ec[sel]  # (k,)
                pending.setdefault(t + int(L), []).append((eX[sel], ec[sel], vals.astype(np.int16)[:, None]))
        X, c, V, _ = successors(X, c, V, None, t)
        X, c, V, _ = dedupe_max(X, c, V, None, W)
        X, c, V = _prune(X, c, V, width)


# ---------------------------------------------------------------------------------------------------------------------
# 5. The shape of optimal drivers
# ---------------------------------------------------------------------------------------------------------------------


def greedy_driver(steps: int) -> list[int]:
    """The driver in Lambda_L that is black whenever its value is free: c(0 .. steps)."""
    X = np.zeros((1, (steps + 2) // 64 + 1), dtype=np.uint64)  # (1, W)
    word = [1]
    for _ in range(steps):
        cur = word[-1]
        word.append(1 - int(X[0, 0] & ONE) if cur == 1 else 1)
        X = driven_step(X, cur)
    return word


def run_lengths(word: Sequence[int]) -> tuple[list[int], list[int]]:
    """The lengths of the maximal black runs and of the maximal white runs of a word, in order."""
    black: list[int] = []
    white: list[int] = []
    for bit, grp in itertools.groupby(word):
        (black if bit else white).append(len(list(grp)))
    return black, white


def run_start_domains(word: Sequence[int]) -> list[tuple[int, int, int]]:
    """For each maximal black run of the driver (start a, length L), the alternating right end of the left half at
    time a that `black_reach` reads, as (a, L, reach): a black run from a lasts at most `reach` steps."""
    T = len(word) - 1
    W = (T + 2) // 64 + 1
    X = np.zeros((1, W), dtype=np.uint64)  # (1, W)
    out: list[tuple[int, int, int]] = []
    a = 0
    halves = []
    for u in range(T + 1):
        halves.append(X.copy())
        X = driven_step(X, word[u])
    for bit, grp in itertools.groupby(enumerate(word), key=lambda z: z[1]):
        g = list(grp)
        if bit:
            a, L = g[0][0], len(g)
            out.append((a, L, int(black_reach(halves[a], max(a, 1))[0])))
    return out


# ---------------------------------------------------------------------------------------------------------------------
# 6. Potentials over a restricted feature basis
# ---------------------------------------------------------------------------------------------------------------------
# A certificate of slope rho is a function Phi of the state with c(t + 1) <= rho + Phi(s) - Phi(s') on every edge
# s -> s'; summed along a driver it gives M(T) <= rho T + Phi(start) - min Phi. On a finite layered graph some
# unrestricted Phi always exists, so Phi is restricted to theta . features(s) with |theta_i| <= bound, fitted on the
# edges with t < fit and then evaluated, unchanged, on the edges with fit <= t < test.

FEATURE_NAMES = (["c", "c and cell -1", "first domain", "second domain", "black reach", "agreement"]
                 + [f"cell -{k}" for k in range(1, 21)] + ["black among -21..-40"])


def _trailing_ones(y: np.ndarray) -> np.ndarray:
    """The number of trailing 1 bits of each word (at most 64)."""
    # y: (n,) uint64
    out = np.zeros(len(y), dtype=np.int64)  # (n,)
    z = y.copy()
    for _ in range(64):
        live = (z & ONE) == ONE  # (n,)
        if not live.any():
            break
        out += live
        z = np.where(live, z >> ONE, np.uint64(0))
    return out


def state_features(X: np.ndarray, c: np.ndarray, single: np.ndarray) -> np.ndarray:
    """The feature basis of each state: c, c and cell -1, the lengths of the first two alternating domains from the
    center, the black reach of `black_reach` (zero for a white center), the number of leading cells -1, -2, ...
    that agree with the single cell's left half `single` at the same time, the cells -1 .. -20 and the black count
    of the cells -21 .. -40."""
    # X: (n, W) uint64; c: (n,) uint8; single: (W,) uint64
    x0 = X[:, 0]  # (n,)
    y = x0 ^ (x0 >> ONE)  # (n,), bit k - 1 is set when cells -k and -(k + 1) differ
    d1 = 1 + _trailing_ones(y)  # (n,)
    d2 = 1 + _trailing_ones(y >> np.minimum(d1, 63).astype(np.uint64))  # (n,)
    cell1 = (x0 & ONE).astype(np.int64)  # (n,)
    reach = np.where((c == 1) & (cell1 == 0), d1, 0)  # (n,)
    agree = _trailing_ones(~(x0 ^ single[0]))  # (n,)
    cells = ((x0[:, None] >> np.arange(20, dtype=np.uint64)[None, :]) & ONE).astype(np.int64)  # (n, 20)
    cols = [c.astype(np.int64), c.astype(np.int64) * cell1, d1, d2, reach, agree]
    far = ((x0[:, None] >> np.arange(20, 40, dtype=np.uint64)[None, :]) & ONE).sum(axis=1)  # (n,)
    return np.column_stack(cols + [cells, far]).astype(np.float64)  # (n, 27)


def potential_edges(steps: int) -> Iterator[tuple[int, np.ndarray, np.ndarray]]:
    """For t = 0 .. steps - 1, the distinct rows (features(s') - features(s), c(t + 1)) over every edge s -> s' from
    the reachable states at time t."""
    from computations.rule30 import center_column
    col = [int(a) for a in center_column(steps + 1)]
    W = steps // 64 + 1
    single = np.zeros((1, W), dtype=np.uint64)  # (1, W), the single cell's left half
    X = np.zeros((1, W), dtype=np.uint64)  # (1, W)
    c = np.ones(1, dtype=np.uint8)  # (1,)
    V = np.zeros((len(c), 1), dtype=np.int16)  # (n, 1), unused counts
    for t in range(steps):
        F = state_features(X, c, single[0])  # (n, 27)
        white = c == 0  # (n,)
        parent = np.concatenate([np.flatnonzero(white), np.flatnonzero(white), np.flatnonzero(~white)])  # (m,)
        Xn, cn, V, _ = successors(X, c, V, None, t)
        single = driven_step(single, col[t])
        Fn = state_features(Xn, cn, single[0])  # (m, 27)
        rows = np.column_stack([Fn - F[parent], cn.astype(np.float64)])  # (m, 28)
        yield t, np.unique(rows, axis=0), Fn
        X, c, V, _ = dedupe_max(Xn, cn, V, None, min(W, (t + 1) // 64 + 1))


@dataclass
class PotentialFit:
    rho: float  # least rho certified on the edges with t < fit
    constant: float  # max over those states of Phi(start) - Phi(s)
    rho_test: float  # rho the same theta needs on the edges with fit <= t < test
    theta: np.ndarray  # (27,) weights
    dual_edges: int  # edges with positive dual weight
    dual_times: tuple[int, int]  # their least and largest t


def fit_potential(fit: int, test: int, bound: float) -> PotentialFit:
    """The least rho certified on the edges with t < fit by theta . features with |theta_i| <= bound (scipy HiGHS),
    the additive constant, the rho the same theta needs on the edges with fit <= t < test, and the support of the
    dual solution (a combination of edges whose feature differences cancel and whose mean count is rho)."""
    from scipy.optimize import linprog
    fit_rows, fit_times, test_rows, phis = [], [], [], []
    for t, rows, Fn in potential_edges(test):
        if t < fit:
            fit_rows.append(rows)
            fit_times.append(np.full(len(rows), t))
            phis.append(Fn)
        else:
            test_rows.append(rows)
    A = np.concatenate(fit_rows)  # (e, 28)
    times = np.concatenate(fit_times)  # (e,)
    nf = A.shape[1] - 1
    # variables (rho, theta): r + theta . (f' - f) <= rho
    A_ub = np.column_stack([-np.ones(len(A)), A[:, :nf]])  # (e, 1 + nf)
    res = linprog(np.r_[1.0, np.zeros(nf)], A_ub=A_ub, b_ub=-A[:, nf],
                  bounds=[(None, None)] + [(-bound, bound)] * nf, method="highs")
    theta = res.x[1:]  # (nf,)
    f0 = state_features(np.zeros((1, 1), np.uint64), np.ones(1, np.uint8), np.zeros(1, np.uint64))[0]  # (nf,)
    const = float(((f0[None, :] - np.concatenate(phis)) @ theta).max())
    T = np.concatenate(test_rows) if test_rows else A  # (e', 28)
    support = np.flatnonzero(-res.ineqlin.marginals > 1e-9)  # (k,)
    return PotentialFit(float(res.x[0]), const, float((T[:, nf] + T[:, :nf] @ theta).max()), theta, len(support),
                        (int(times[support].min()), int(times[support].max())))


# ---------------------------------------------------------------------------------------------------------------------
# Command line
# ---------------------------------------------------------------------------------------------------------------------


def _ints(text: str) -> list[int]:
    return [int(a) for a in text.split(",") if a]


def run_exact(args: argparse.Namespace) -> None:
    forks = _ints(args.forks)
    print("t states M(t) M(t)/(t+1) " + " ".join(f"G({s},t)" for s in forks))
    for r in driver_dp(args.steps, forks, track=args.track, progress=True):
        if r.t % args.every == 0 or r.t == args.steps:
            gains = " ".join(f"{r.gains.get(s, '-')}" for s in forks)
            print(f"{r.t} {r.states} {r.best} {r.best / (r.t + 1):.4f} {gains}", flush=True)
            if r.driver is not None and r.t == args.steps:
                print("driver", "".join(map(str, r.driver)))


def run_beam(args: argparse.Namespace) -> None:
    last = None
    print("t states best best/(t+1) gain-per-every")
    for r in driver_dp(args.steps, beam=args.width, track=args.track, progress=True):
        if r.t % args.every == 0 or r.t == args.steps:
            gain = "-" if last is None else str(r.best - last)
            print(f"{r.t} {r.states} {r.best} {r.best / (r.t + 1):.4f} {gain}", flush=True)
            last = r.best
            if r.driver is not None and r.t == args.steps:
                print("driver", "".join(map(str, r.driver)))


def lifetime_summary(rows: Sequence[LifeRow], fit_from: int) -> dict[str, tuple[float, float, float]]:
    """For each word: the least-squares slope of l_w(t) on t >= fit_from, l_w / t at the last t, and the largest
    ratio of the black letters of a longest stretch, density(w) l_w(t), to log2 of the number of states."""
    out: dict[str, tuple[float, float, float]] = {}
    sel = [r for r in rows if r.t >= fit_from]
    ts = np.array([r.t for r in sel], dtype=np.float64)  # (k,)
    for w in rows[0].lengths:
        ls = np.array([r.lengths[w] for r in sel], dtype=np.float64)  # (k,)
        d = w.count("1") / len(w)
        slope = float(np.polyfit(ts, ls, 1)[0]) if len(ts) > 1 else float("nan")
        bits = max(d * r.lengths[w] / math.log2(r.states) for r in sel)
        out[w] = (slope, sel[-1].lengths[w] / sel[-1].t, bits)
    return out


def run_lifetimes(args: argparse.Namespace) -> None:
    words = args.words.split(",") if args.words else primitive_words(args.pmax, args.density)
    print("words", " ".join(words))
    rows: list[LifeRow] = []
    for r in lifetimes(args.steps, args.every, words, args.horizon, progress=True):
        rows.append(r)
        print(r.t, r.states, " ".join(f"{w}:{r.lengths[w]}" for w in words), flush=True)
    for t0 in (10, 30, 40, 60):
        dense = [(r.lengths[w] / r.t, r.t, w) for r in rows if r.t >= t0 for w in words
                 if w.count("1") >= 0.8 * len(w)]
        if dense:
            print(f"largest l_w(t)/t over words of density >= 0.8 and t >= {t0}: {max(dense)}")
    for w, (slope, ratio, bits) in lifetime_summary(rows, args.fit_from).items():
        bits_lo = min(w.count("1") / len(w) * r.lengths[w] / math.log2(r.states) for r in rows if r.t >= args.fit_from)
        print(f"{w}: slope {slope:.3f} on t >= {args.fit_from}, l_w/t at t = {rows[-1].t}: {ratio:.3f}, black letters "
              f"over log2 N(t) from {bits_lo:.2f} to {bits:.2f}")


def run_reentry(args: argparse.Namespace) -> None:
    for t in _ints(args.times):
        states = _states_at(t)
        for w in args.words.split(","):
            r = reentry(w, t, args.gmax, states=states)
            dens = "-" if r.gap is None or r.gap_black is None else \
                f"{(r.stretch_black + r.gap_black) / (r.length + r.gap):.2f}"
            print(f"w={w} t={t} l={r.length} stretch_black={r.stretch_black} target={r.target} ends={r.ends} "
                  f"gap={r.gap} gap_max={r.gap_max} gap_black={r.gap_black} density={dens}", flush=True)


def run_chain(args: argparse.Namespace) -> None:
    words = args.words.split(",")
    for r in chain_beam(args.steps, args.width, words, args.min_len, progress=True):
        if r.t % args.every == 0 or r.t == args.steps:
            print(f"{r.t} {r.states} {r.best} {r.best / (r.t + 1):.4f}", flush=True)


def run_describe(args: argparse.Namespace) -> None:
    g = greedy_driver(max(args.steps, args.beam_steps))
    print(f"greedy driver: {sum(g)} black cells among c(0 .. {len(g) - 1}), ratio {sum(g) / len(g):.4f}")
    for label, steps, beam in (("exact", args.steps, None), ("beam", args.beam_steps, args.width)):
        if steps <= 0:
            continue
        driver = None
        for r in driver_dp(steps, beam=beam, track=True, progress=True):
            driver = r.driver
        assert driver is not None
        black, white = run_lengths(driver)
        print(f"{label} T={steps} M={sum(driver)} ratio={sum(driver) / (steps + 1):.4f}")
        print("  black run lengths:", dict(sorted(Counter(black).items())))
        print("  white run lengths:", dict(sorted(Counter(white).items())))
        doms = run_start_domains(driver)
        slack = Counter(reach - L for a, L, reach in doms if a + L <= steps)
        print("  black reach at run starts minus run length (complete runs):", dict(sorted(slack.items())))
        chosen = sum(1 for u in range(1, steps + 1) if driver[u] == 0 and driver[u - 1] == 0)
        print(f"  mean black run {np.mean(black):.3f}, mean white run {np.mean(white):.3f}; white cells forced by a "
              f"black one {sum(1 for u in range(1, steps + 1) if driver[u] == 0 and driver[u - 1] == 1)}, chosen "
              f"after a white one {chosen}")
        if steps <= 200:
            print("  driver", "".join(map(str, driver)))


def run_potential(args: argparse.Namespace) -> None:
    for bound in [float(b) for b in args.bounds.split(",")]:
        r = fit_potential(args.fit, args.test, bound)
        top = sorted(zip(np.abs(r.theta), FEATURE_NAMES, r.theta), reverse=True)[:6]
        print(f"bound {bound}: rho {r.rho:.4f} on t < {args.fit} (constant {r.constant:.2f}), the same theta needs rho "
              f"{r.rho_test:.4f} on {args.fit} <= t < {args.test}; dual support {r.dual_edges} edges at t = "
              f"{r.dual_times[0]} .. {r.dual_times[1]}; largest weights "
              + ", ".join(f"{n} {v:+.2f}" for _, n, v in top), flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("exact")
    p.add_argument("--steps", type=int, default=120)
    p.add_argument("--every", type=int, default=10)
    p.add_argument("--forks", default="")
    p.add_argument("--track", action="store_true")
    p.set_defaults(func=run_exact)
    p = sub.add_parser("beam")
    p.add_argument("--steps", type=int, default=1000)
    p.add_argument("--width", type=int, default=60000)
    p.add_argument("--every", type=int, default=100)
    p.add_argument("--track", action="store_true")
    p.set_defaults(func=run_beam)
    p = sub.add_parser("lifetimes")
    p.add_argument("--steps", type=int, default=100)
    p.add_argument("--every", type=int, default=10)
    p.add_argument("--pmax", type=int, default=8)
    p.add_argument("--density", type=float, default=0.6)
    p.add_argument("--words", default="")
    p.add_argument("--horizon", type=int, default=120)
    p.add_argument("--fit-from", type=int, default=60)
    p.set_defaults(func=run_lifetimes)
    p = sub.add_parser("reentry")
    p.add_argument("--words", default="110,1110,11110,111110,11010,1111110,11111110")
    p.add_argument("--times", default="40,80,120")
    p.add_argument("--gmax", type=int, default=40)
    p.set_defaults(func=run_reentry)
    p = sub.add_parser("chain")
    p.add_argument("--steps", type=int, default=1000)
    p.add_argument("--width", type=int, default=20000)
    p.add_argument("--words", default="110,1110,11110,111110,11010,1111110,11111110")
    p.add_argument("--min-len", type=int, default=8)
    p.add_argument("--every", type=int, default=100)
    p.set_defaults(func=run_chain)
    p = sub.add_parser("describe")
    p.add_argument("--steps", type=int, default=120)
    p.add_argument("--beam-steps", type=int, default=0)
    p.add_argument("--width", type=int, default=60000)
    p.set_defaults(func=run_describe)
    p = sub.add_parser("potential")
    p.add_argument("--fit", type=int, default=60)
    p.add_argument("--test", type=int, default=100)
    p.add_argument("--bounds", default="1,3,10,100")
    p.set_defaults(func=run_potential)
    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
