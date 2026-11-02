"""The left half driven by a center column that obeys the left-only constraint, and finite-state views of it.

`run_mechanism.driven_rows` lets the center column c be any sequence with c(0) = 1. One constraint needs no right half:
since c(t + 1) = x_{-1}(t) xor (c(t) or x_1(t)), a black center fixes the next one, c(t + 1) = not x_{-1}(t) when
c(t) = 1. A driver word c(0) = 1, c(1), ..., c(n - 1) is admissible when it obeys the constraint at every step, with
the left half driven from a white start. The single cell's center column is admissible.

1. `table`: every reachable state (left half at time t, c(t)) under admissible drivers, by breadth-first search
   (`constrained_states`), with N(t), the number of distinct left halves, and the longest black and white runs from
   time t that a reachable state allows (`black_reach` over the states with c(t) = 1, `white_reach` over those with
   c(t) = 0, both from `run_mechanism`). With `--compare` it runs `run_mechanism.driven_rows` beside it.
2. `classes`: for each k, the number of distinct sets of admissible futures of length k over the reachable states with
   t <= steps, a lower bound on the states of any deterministic automaton that accepts exactly the admissible words.
   The future of length k depends only on c(t) and the cells -1 .. -k (`future_sets`).
3. `window`: the outer automaton on the cells -1 .. -w with cell -(w + 1) free and the constraint kept, from the white
   window with c(0) = 1. `window_longest_run` is the longest black run it admits within n steps, and
   `window_infinite_run` finds the earliest time from which it admits a black run that never ends.
4. `carry`: the black run of the single cell from time t is v_2(3 N_t + 2) + 1, with N_t the left half read as an
   integer (bit k - 1 is cell -k); -2/3 is the 2-adic integer whose bits alternate 0, 1, 0, 1, ... from bit 0.
5. `bernoulli`: the longest black run of admissible words against uniform words (`admissible_run_hist`,
   `uniform_run_hist`), and the black reach of the reachable states against N_1 2^-(r - 1) (`state_depletion`).

    python -m computations.constrained_runs table --steps 150 --every 5 --compare    # about 5 min
    python -m computations.constrained_runs classes --steps 60 --kmax 12             # about 30 s
    python -m computations.constrained_runs window --wmax 10                         # about 1 s
    python -m computations.constrained_runs carry --steps 4000                       # about 1 s
    python -m computations.constrained_runs bernoulli --words 40 --states 50,100,150  # about 2 min
    python -m computations.constrained_runs bernoulli --words 4 --states 175          # about 2 min, 1.3 GB
"""

from __future__ import annotations

import argparse
import itertools
import sys
from collections.abc import Iterator
from dataclasses import dataclass

import numpy as np
from tqdm.auto import tqdm

from computations.run_mechanism import black_reach, center_window, driven_rows, driven_step, white_reach, window_cells

# ---------------------------------------------------------------------------------------------------------------------
# 1. Reachable states under the left-only constraint
# ---------------------------------------------------------------------------------------------------------------------
# A left half is a multiword integer as in run_mechanism: bit k - 1 of B[i] is cell -k at time t; C[i] is c(t).


def unique_rows(B: np.ndarray) -> np.ndarray:
    """The distinct rows of B, sorted (no index array, to keep memory low at t = 175)."""
    # B: (n, W) uint64
    W = B.shape[1]
    view = np.ascontiguousarray(B).view(np.dtype((np.void, 8 * W)))[:, 0]  # (n,)
    return np.unique(view).view(np.uint64).reshape(-1, W)  # (m, W)


def distinct_halves(B: np.ndarray) -> int:
    """The number of distinct left halves among the rows of B."""
    # B: (n, W)
    view = np.ascontiguousarray(B).view(np.dtype((np.void, 8 * B.shape[1])))[:, 0]  # (n,)
    return len(np.unique(view))


def constrained_states(steps: int, progress: bool = False) -> Iterator[tuple[int, np.ndarray, np.ndarray]]:
    """Yield (t, B, C) for t = 0 .. steps: every reachable pair (left half at time t, c(t)) under admissible drivers.
    A state with c(t) = 0 has two successors, one for each c(t + 1); a state with c(t) = 1 has one."""
    words = steps // 64 + 1
    B = np.zeros((1, words), dtype=np.uint64)  # (1, words)
    C = np.ones(1, dtype=np.uint8)  # (1,)
    yield 0, B, C
    for t in tqdm(range(steps), desc="constrained states", file=sys.stderr, disable=not progress):
        white = C == 0  # (n,)
        Bw = driven_step(B[white], 0)  # (nw, words)
        Bk = B[~white]  # (nb, words)
        forced = (np.uint64(1) ^ (Bk[:, 0] & np.uint64(1))).astype(bool)  # (nb,), not cell -1
        Bb = driven_step(Bk, 1)  # (nb, words)
        del Bk
        B0 = unique_rows(np.concatenate([Bw, Bb[~forced]]))  # (n0, words), the states with c(t + 1) = 0
        B1 = unique_rows(np.concatenate([Bw, Bb[forced]]))  # (n1, words), the states with c(t + 1) = 1
        del Bw, Bb
        B = np.concatenate([B0, B1])  # (n0 + n1, words)
        C = np.concatenate([np.zeros(len(B0), np.uint8), np.ones(len(B1), np.uint8)])  # (n0 + n1,)
        del B0, B1
        yield t + 1, B, C


@dataclass
class ConstrainedRow:
    t: int
    states: int  # reachable pairs (left half, c(t))
    rows: int  # distinct left halves, N(t) under the constraint
    black: int  # longest black run from time t over the states with c(t) = 1
    white: int  # longest white run from time t over the states with c(t) = 0
    free_rows: int | None = None  # N(t) without the constraint (run_mechanism.driven_rows)
    free_black: int | None = None
    free_white: int | None = None


def _white_max(B: np.ndarray, t: int, chunk: int) -> int:
    # B: (n, W)
    if len(B) == 0:
        return 0
    return max(int(white_reach(B[k:k + chunk], t, t + 2).max()) for k in range(0, len(B), chunk))


def constrained_table(steps: int, every: int = 1, compare: bool = False, progress: bool = False,
                      chunk: int = 1 << 19) -> Iterator[ConstrainedRow]:
    """Yield a row for t = 1 .. steps, every `every` steps and at `steps`; with `compare`, also N(t), R_B(t) and
    R_W(t) of the relaxation without the constraint."""
    free = driven_rows(steps) if compare else None
    for t, B, C in constrained_states(steps, progress):
        if free is not None and t >= 1:
            _, F, _ = next(free)
        if t == 0 or (t % every and t != steps):
            continue
        black = C == 1  # (n,)
        row = ConstrainedRow(t, len(B), distinct_halves(B),
                             int(black_reach(B[black], t).max()) if black.any() else 0,
                             _white_max(B[~black], t, chunk))
        if free is not None:
            row.free_rows = len(F)
            row.free_black = int(black_reach(F, t).max())
            row.free_white = _white_max(F, t, chunk)
        yield row


# ---------------------------------------------------------------------------------------------------------------------
# 2. Residual classes of the admissible language
# ---------------------------------------------------------------------------------------------------------------------


def future_sets(window: np.ndarray, center: np.ndarray, k: int) -> np.ndarray:
    """For each state given by its cells -1 .. -k (bit j - 1 is cell -j) and its center c(t), which words
    c(t + 1) .. c(t + k) are admissible. The constraint at time t + j reads cell -1 at time t + j, which depends on
    the cells -1 .. -(j + 1) at time t and on the centers, so k cells suffice."""
    # window: (n,) uint64; center: (n,) uint8
    n = len(window)
    words = np.array(list(itertools.product((0, 1), repeat=k)), dtype=np.uint8)  # (2^k, k), bit j is c(t + j + 1)
    ok = np.ones((n, 2 ** k), dtype=bool)  # (n, 2^k)
    x = np.repeat(window[:, None], 2 ** k, axis=1)  # (n, 2^k)
    c = np.repeat(center[:, None], 2 ** k, axis=1)  # (n, 2^k)
    mask = np.uint64((1 << k) - 1)
    for j in range(k):
        nxt = np.broadcast_to(words[None, :, j], c.shape)  # (n, 2^k)
        ok &= ~((c == 1) & (nxt != (np.uint64(1) ^ (x & np.uint64(1))).astype(np.uint8)))
        left = ((x << np.uint64(1)) | c.astype(np.uint64)) & mask
        x = ((x >> np.uint64(1)) ^ (x | left)) & mask  # cells beyond the window go wrong but are read too late
        c = nxt.copy()
    return ok  # (n, 2^k)


@dataclass
class Classes:
    k: int
    windows: int  # distinct pairs (cells -1 .. -k, c(t)) over the reachable states with t <= steps
    classes: int  # distinct sets of admissible futures of length k among them
    white_classes: int  # those of states with c(t) = 0 (their futures begin with both letters, the others' with one)


def residual_classes(steps: int, ks: list[int], progress: bool = False) -> list[Classes]:
    """Distinct length-k future sets over every reachable state with t <= steps, for each k in ks."""
    seen: dict[int, set[tuple[int, int]]] = {k: set() for k in ks}
    for _, B, C in constrained_states(steps, progress):
        for k in ks:
            win = B[:, 0] & np.uint64((1 << k) - 1)  # (n,)
            seen[k].update(zip(win.tolist(), C.tolist()))
    out: list[Classes] = []
    for k in ks:
        pairs = np.array(sorted(seen[k]), dtype=np.uint64)  # (m, 2)
        fs = np.packbits(future_sets(pairs[:, 0], pairs[:, 1].astype(np.uint8), k), axis=1)  # (m, ceil(2^k / 8))
        white = pairs[:, 1] == 0  # (m,)
        out.append(Classes(k, len(pairs), len({r.tobytes() for r in fs}), len({r.tobytes() for r in fs[white]})))
    return out


# ---------------------------------------------------------------------------------------------------------------------
# 3. Fixed-window outer automata
# ---------------------------------------------------------------------------------------------------------------------


def window_moves(w: int) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """Every move of the outer automaton on w cells: from (window x, center c) with free cell -(w + 1) to (x', c').
    The center after a white one is free, after a black one it is not cell -1."""
    S = 1 << w
    xs, cs, ys, ds = [], [], [], []
    for c in (0, 1):
        for free in (0, 1):
            x = np.arange(S, dtype=np.int64)  # (S,)
            full = x | (free << w)  # (S,), cells -1 .. -(w + 1)
            left = ((full << 1) | c) & ((1 << (w + 1)) - 1)
            y = ((full >> 1) ^ (full | left)) & (S - 1)  # (S,)
            for d in ((0, 1) if c == 0 else (None,)):
                dd = (1 ^ (x & 1)) if d is None else np.full(S, d, dtype=np.int64)  # (S,)
                xs.append(x)
                cs.append(np.full(S, c, dtype=np.int64))
                ys.append(y)
                ds.append(dd)
    return np.concatenate(xs), np.concatenate(cs), np.concatenate(ys), np.concatenate(ds)  # each (m,)


def window_longest_run(w: int, steps: int) -> np.ndarray:
    """out[n - 1] is the longest black run of the center that the outer automaton on w cells admits within n steps
    (times 0 .. n), from the white window with c(0) = 1; max-plus over the trailing black run at each state."""
    x, c, y, d = window_moves(w)  # each (m,)
    S = 1 << w
    best = np.full(2 * S, -1, dtype=np.int64)  # (2S,), state index 2x + c: longest trailing black run, -1 unreached
    best[1] = 1
    longest = 1
    out = np.zeros(steps, dtype=np.int64)  # (steps,)
    for n in range(steps):
        v = best[2 * x + c]  # (m,)
        live = v >= 0
        nv = np.where(d == 1, v + 1, 0)[live]  # (m',)
        new = np.full(2 * S, -1, dtype=np.int64)  # (2S,)
        np.maximum.at(new, (2 * y + d)[live], nv)
        best = new
        longest = max(longest, int(best.max()))
        out[n] = longest
    return out  # (steps,)


def window_infinite_run(w: int) -> tuple[int, list[int]]:
    """(a, windows): the windows x (bit j - 1 is cell -j) such that the outer automaton on w cells, in state (x, 1),
    admits a black run that never ends, and the earliest time a at which it can be in one of them; a = -1 if never."""
    x, c, y, d = window_moves(w)  # each (m,)
    S = 1 << w
    # states from which some infinite path keeps the center black: greatest fixed point inside the black states
    black_move = (c == 1) & (d == 1)  # (m,)
    alive = np.zeros(2 * S, dtype=bool)  # (2S,)
    alive[1::2] = True
    while True:
        ok = np.zeros(2 * S, dtype=bool)  # (2S,)
        src = 2 * x[black_move] + 1
        ok[src[alive[2 * y[black_move] + 1]]] = True
        nxt = alive & ok
        if np.array_equal(nxt, alive):
            break
        alive = nxt
    windows = (np.nonzero(alive)[0] // 2).tolist()
    if not windows:
        return -1, []
    # earliest arrival at an alive state from (white window, c = 1) at time 0
    reach = np.zeros(2 * S, dtype=bool)  # (2S,)
    reach[1] = True
    for a in range(4 * S + 1):
        if (reach & alive).any():
            return a, windows
        nxt = np.zeros(2 * S, dtype=bool)  # (2S,)
        nxt[(2 * y + d)[reach[2 * x + c]]] = True
        reach = nxt
    return -1, windows


# ---------------------------------------------------------------------------------------------------------------------
# 4. The carry valuation of a black run
# ---------------------------------------------------------------------------------------------------------------------


def valuation(n: int) -> int:
    """The 2-adic valuation of a positive integer."""
    return (n & -n).bit_length() - 1


def carry_check(steps: int, half: int = 80, margin: int = 100) -> tuple[int, int]:
    """(matches, black times): at every time 1 <= t < steps - margin with the single cell's center black, compare the
    black run from t with min(v_2(3 N_t + 2), half) + 1, N_t the cells -1 .. -half of row t as an integer."""
    cells = window_cells(center_window(steps, half), half)  # (steps, 2 * half + 1)
    col = cells[:, half]  # (steps,)
    weights = [1 << (k - 1) for k in range(1, half + 1)]
    matches = total = 0
    for t in range(1, steps - margin):
        if col[t] != 1:
            continue
        r = 0
        while col[t + r] == 1:
            r += 1
        N = sum(w for k, w in enumerate(weights, start=1) if cells[t, half - k])
        total += 1
        matches += int(min(valuation(3 * N + 2), half) + 1 == r)
    return matches, total


# ---------------------------------------------------------------------------------------------------------------------
# 5. Long runs among admissible words and states against fair bits
# ---------------------------------------------------------------------------------------------------------------------


def _half_step(L: int, c: int) -> int:
    # one step of the driven left half held as a Python integer, bit k - 1 is cell -k
    return (L >> 1) ^ (L | (L << 1) | c)


def admissible_run_hist(n: int) -> np.ndarray:
    """hist[r] is the number of admissible words of length n whose longest black run is r (dynamic programming over
    (left half, center, trailing black run, longest black run))."""
    states: dict[tuple[int, int, int, int], int] = {(0, 1, 1, 1): 1}
    for _ in range(n - 1):
        new: dict[tuple[int, int, int, int], int] = {}
        for (L, c, tr, lg), m in states.items():
            L2 = _half_step(L, c)
            for c2 in ((0, 1) if c == 0 else (1 ^ (L & 1),)):
                tr2 = tr + 1 if c2 else 0
                key = (L2, c2, tr2, max(lg, tr2))
                new[key] = new.get(key, 0) + m
        states = new
    hist = np.zeros(n + 1, dtype=np.int64)  # (n + 1,)
    for (_, _, _, lg), m in states.items():
        hist[lg] += m
    return hist  # (n + 1,)


def uniform_run_hist(n: int) -> np.ndarray:
    """hist[r] is the number of words of length n with first letter 1 whose longest run of 1s is r."""
    states: dict[tuple[int, int], int] = {(1, 1): 1}
    for _ in range(n - 1):
        new: dict[tuple[int, int], int] = {}
        for (tr, lg), m in states.items():
            for b in (0, 1):
                tr2 = tr + 1 if b else 0
                key = (tr2, max(lg, tr2))
                new[key] = new.get(key, 0) + m
        states = new
    hist = np.zeros(n + 1, dtype=np.int64)  # (n + 1,)
    for (_, lg), m in states.items():
        hist[lg] += m
    return hist  # (n + 1,)


@dataclass
class Depletion:
    t: int
    black_states: int  # N_1: reachable states with c(t) = 1
    counts: dict[int, int]  # r -> number of those states whose black run from t is at least r


def state_depletion(times: list[int], progress: bool = False) -> list[Depletion]:
    """For each t in times, the reachable states with c(t) = 1 counted by their black run from t."""
    out: list[Depletion] = []
    for t, B, C in constrained_states(max(times), progress):
        if t not in times:
            continue
        rb = black_reach(B[C == 1], t)  # (N_1,)
        out.append(Depletion(t, len(rb), {r: int((rb >= r).sum()) for r in range(1, int(rb.max()) + 1)}))
    return out


# ---------------------------------------------------------------------------------------------------------------------


def run_table(args: argparse.Namespace) -> None:
    head = f"{'t':>4} {'states':>9} {'N(t)':>9} {'log2 N':>7} {'R_B':>4} {'R_B/t':>6} {'R_W':>4} {'R_W/t':>6}"
    print(head + ("  free: N(t), R_B, R_W, N ratio" if args.compare else ""))
    for r in constrained_table(args.steps, args.every, args.compare, progress=True):
        line = (f"{r.t:>4} {r.states:>9} {r.rows:>9} {np.log2(r.rows):>7.2f} {r.black:>4} {r.black / r.t:>6.3f} "
                f"{r.white:>4} {r.white / r.t:>6.3f}")
        if args.compare:
            line += f"  {r.free_rows:>9} {r.free_black:>4} {r.free_white:>4} {r.free_rows / r.rows:>6.3f}"
        print(line, flush=True)


def run_classes(args: argparse.Namespace) -> None:
    print(f"k  windows (cells -1 .. -k, c) reached for t <= {args.steps}  distinct k-futures (of them with c = 0)  "
          "2^k + 1  2^(k+1)")
    for r in residual_classes(args.steps, list(range(2, args.kmax + 1)), progress=True):
        print(f"{r.k:>2} {r.windows:>10} {r.classes:>10} ({r.white_classes:>5}) {2 ** r.k + 1:>8} {2 ** (r.k + 1):>8}",
              flush=True)


def run_window(args: argparse.Namespace) -> None:
    ns = [50, 100, 200]
    print(f"w  longest black run within n steps, n = {ns}; earliest start of an endless black run; windows that keep "
          "it, cells -1 .. -w")
    for w in range(3, args.wmax + 1):
        runs = window_longest_run(w, max(ns))
        a, windows = window_infinite_run(w)
        cells = ["".join(str((x >> j) & 1) for j in range(w)) for x in windows]
        print(f"{w:>2} {[int(runs[n - 1]) for n in ns]} {a:>3} {cells}", flush=True)


def run_carry(args: argparse.Namespace) -> None:
    m, total = carry_check(args.steps)
    print(f"black times t < {args.steps - 100}: run from t equal to v_2(3 N_t + 2) + 1 at {m} of {total}")


def run_bernoulli(args: argparse.Namespace) -> None:
    print("n  admissible words  log2(count)/n  share with run >= 0.2n: admissible, uniform, ratio  longest run: "
          "admissible, uniform  share with run >= 0.4n: admissible")
    for n in tqdm(range(4, args.words + 1, 2), desc="words", file=sys.stderr):
        a = admissible_run_hist(n)  # (n + 1,)
        b = uniform_run_hist(n)  # (n + 1,)
        r2, r4 = int(np.ceil(0.2 * n)), int(np.ceil(0.4 * n))
        fa, fb = a[r2:].sum() / a.sum(), b[r2:].sum() / b.sum()
        tqdm.write(f"{n:>3} {a.sum():>10} {np.log2(a.sum()) / n:>6.3f}  {fa:.4f} {fb:.4f} {fa / fb:6.3f}  "
                   f"{np.nonzero(a)[0].max():>3} {np.nonzero(b)[0].max():>3}  {a[r4:].sum() / a.sum():.4f}")
    times = [int(s) for s in args.states.split(",")]
    print("t  N_1  r: states with black run >= r / N_1 2^-(r - 1)")
    for dep in state_depletion(times, progress=True):
        parts = [f"{r}: {n}/{dep.black_states * 2.0 ** -(r - 1):.1f}" for r, n in dep.counts.items() if r >= 2]
        worst = max(n / (dep.black_states * 2.0 ** -(r - 1)) for r, n in dep.counts.items() if r >= 4)
        print(f"{dep.t:>4} {dep.black_states:>8}  " + ", ".join(parts) + f"  (largest ratio for r >= 4: {worst:.2f})",
              flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("table")
    p.add_argument("--steps", type=int, default=100)
    p.add_argument("--every", type=int, default=5)
    p.add_argument("--compare", action="store_true")
    p.set_defaults(func=run_table)
    p = sub.add_parser("classes")
    p.add_argument("--steps", type=int, default=60)
    p.add_argument("--kmax", type=int, default=12)
    p.set_defaults(func=run_classes)
    p = sub.add_parser("window")
    p.add_argument("--wmax", type=int, default=10)
    p.set_defaults(func=run_window)
    p = sub.add_parser("carry")
    p.add_argument("--steps", type=int, default=4000)
    p.set_defaults(func=run_carry)
    p = sub.add_parser("bernoulli")
    p.add_argument("--words", type=int, default=40)
    p.add_argument("--states", default="50,100,150")
    p.set_defaults(func=run_bernoulli)
    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
