"""A ladder of exact right columns: the most cells of one color the center column can have when the right half is
kept exact up to cell k and cell k + 1 is free.

Level k. The left half (cells -1, -2, ...) is exact from a white start and driven by the center c; the right cells
1 .. k are exact from a white start, x_i(t + 1) = x_{i-1}(t) xor (x_i(t) or x_{i+1}(t)) with x_0 = c; cell k + 1 is
free at every step (the free word f(0), f(1), ...); and c(0) = 1, c(t + 1) = x_{-1}(t) xor (c(t) or x_1(t)). The single
cell is the member whose free word is its own column k + 1, and level k + 1 is the part of level k whose free word is
cell k + 1 of an exact column. Level 0 (cell 1 free) is the left-only relaxation of `constrained_runs`.

For a color b, M_b(k, T) is the largest number of times t in 0 .. T with c(t) = b over the free words of level k.

1. `exact`: M_b(k, T) by dynamic programming over the states (left half, c, x_1 .. x_k) with the largest count per
   state (`ladder_exact`), and the window maximum W_b(k, T): the most cells of color b among c(h + 1 .. T), h = T // 2,
   over every state reachable at time h (the count is reset to 0 there), a rate estimate free of the start.
2. `beam`: a lower bound on M_b(k, T) that keeps the `width` states with the largest counts (`ladder_beam`), ranked
   by default with the centers c(t + 1 .. t + k) that the state already fixes (`committed`), with a witness free word
   replayed cell by cell (`simulate`); `--plain` ranks by the count so far.
3. `drivers`: the center column of a beam witness, its runs, and, for each free cell, the first center value that
   flipping it alone changes (`first_change`).

The main numbers of findings/diagonals/right-ladder.md (its Reproduce section lists the width checks):

    python -m computations.right_ladder exact --steps 150 --levels 0,1,2,3,4,5,6,7,8 --every 10   # about 40 min
    python -m computations.right_ladder exact --steps 150 --levels 12,16,24 --every 10            # about 40 min
    python -m computations.right_ladder beam --steps 3000 --levels 1 --width 60000 --plain        # about 50 min
    python -m computations.right_ladder beam --steps 2000 --levels 0,2,4 --width 60000 --plain    # about 2 h
    python -m computations.right_ladder beam --steps 1000 --levels 8,16,32,48 --width 60000       # about 1.5 h
    python -m computations.right_ladder beam --steps 2000 --levels 8,16,32,48 --width 15000 --plain   # about 40 min
    python -m computations.right_ladder beam --steps 150 --levels 1,4,8,12,16,24 --width 15000 --every 10
    python -m computations.right_ladder drivers --steps 600 --levels 1,2,4,8,16 --width 15000      # about 10 min
"""

from __future__ import annotations

import argparse
import sys
from collections.abc import Iterator
from dataclasses import dataclass

import numpy as np
from tqdm.auto import tqdm

from computations.run_mechanism import _shl1, _shr1

# A state is a row of B (the left half, bit j - 1 of the multiword integer is cell -j), C (the center, 0 or 1) and R
# (bit i - 1 is x_i, for i = 1 .. k). V is the count of the chosen color so far, F the free word (bit t is f(t)).


def level_step(B: np.ndarray, C: np.ndarray, R: np.ndarray, k: int, f: int) -> tuple[np.ndarray, np.ndarray,
                                                                                     np.ndarray]:
    """One step of level k for every state, with free cell f at the current time."""
    # B: (n, W) uint64; C: (n,) uint64; R: (n,) uint64
    x1 = (R & np.uint64(1)) if k >= 1 else np.full(len(C), f, dtype=np.uint64)  # (n,)
    xm1 = B[:, 0] & np.uint64(1)  # (n,)
    Cn = xm1 ^ (C | x1)  # (n,)
    left = _shl1(B)  # (n, W)
    left[:, 0] |= C
    Bn = _shr1(B) ^ (B | left)  # (n, W)
    if k >= 1:
        mask = np.uint64((1 << k) - 1)
        full = R | (np.uint64(f) << np.uint64(k))  # (n,), bits 0 .. k are x_1 .. x_{k+1}
        lft = ((R << np.uint64(1)) | C) & mask  # (n,), bit i - 1 is x_{i-1}
        Rn = (lft ^ (R | (full >> np.uint64(1)))) & mask  # (n,)
    else:
        Rn = R.copy()  # (n,), empty
    return Bn, Cn, Rn


def reduce_max(B: np.ndarray, C: np.ndarray, R: np.ndarray, V: np.ndarray,
               F: np.ndarray | None = None) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray | None]:
    """The distinct states, each with the largest count among its copies (and the free word of a copy that has it)."""
    # B: (n, W); C, R: (n,) uint64; V: (n,) int32; F: (n, Wf) or None
    key = np.concatenate([B, (C | (R << np.uint64(1)))[:, None]], axis=1)  # (n, W + 1)
    view = np.ascontiguousarray(key).view(np.dtype((np.void, 8 * key.shape[1])))[:, 0]  # (n,)
    order = np.lexsort((V, view))  # (n,), by state, then by count
    sv = view[order]  # (n,)
    last = np.ones(len(sv), dtype=bool)  # (n,), the last copy of each state carries the largest count
    last[:-1] = sv[1:] != sv[:-1]
    keep = order[last]  # (m,)
    return B[keep], C[keep], R[keep], V[keep], (F[keep] if F is not None else None)


def _start(T: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    W = T // 64 + 1
    return np.zeros((1, W), np.uint64), np.ones(1, np.uint64), np.zeros(1, np.uint64)  # (1, W), (1,), (1,)


def _expand(B: np.ndarray, C: np.ndarray, R: np.ndarray, V: np.ndarray, k: int, color: int, t: int,
            F: np.ndarray | None = None) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray | None]:
    """Both successors of every state (free cell 0, then 1), with the count of c(t + 1) == color added."""
    outs = [level_step(B, C, R, k, f) for f in (0, 1)]
    Bn = np.concatenate([o[0] for o in outs])  # (2n, W)
    Cn = np.concatenate([o[1] for o in outs])  # (2n,)
    Rn = np.concatenate([o[2] for o in outs])  # (2n,)
    Vn = np.concatenate([V, V]) + (Cn == np.uint64(color)).astype(np.int32)  # (2n,)
    Fn = None
    if F is not None:
        F1 = F.copy()  # (n, Wf)
        F1[:, t // 64] |= np.uint64(1) << np.uint64(t % 64)
        Fn = np.concatenate([F, F1])  # (2n, Wf)
    return Bn, Cn, Rn, Vn, Fn


@dataclass
class ExactRow:
    t: int
    states: int  # distinct states (left half, c, x_1 .. x_k) at time t
    best: int  # M_b(k, t): most cells of the color among c(0 .. t)
    window: int | None = None  # most cells of the color among c(h + 1 .. t) from any state reachable at h


def ladder_exact(T: int, k: int, color: int, every: int = 1, window: bool = True,
                 progress: bool = False) -> Iterator[ExactRow]:
    """Exact M_b(k, t) for t = 1 .. T (yielded every `every` steps and at T), and with `window` the window maximum
    W_b(k, T) with h = T // 2 (in the row for T)."""
    B, C, R = _start(T)
    V = np.array([int(color == 1)], np.int32)  # (1,)
    h = T // 2
    win: tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray] | None = None
    if window and h == 0:
        win = (B, C, R, np.zeros(1, np.int32))
    for t in tqdm(range(T), desc=f"exact k={k} b={color}", file=sys.stderr, disable=not progress):
        B, C, R, V, _ = reduce_max(*_expand(B, C, R, V, k, color, t))
        if win is not None:
            Bw, Cw, Rw, Vw, _ = reduce_max(*_expand(*win, k, color, t))
            win = (Bw, Cw, Rw, Vw)
        if window and t + 1 == h:
            win = (B, C, R, np.zeros(len(B), np.int32))
        if (t + 1) % every == 0 or t + 1 == T:
            row = ExactRow(t + 1, len(B), int(V.max()))
            if t + 1 == T and win is not None:
                row.window = int(win[3].max())
            yield row


@dataclass
class BeamResult:
    checkpoints: list[tuple[int, int]]  # (t, the largest count among the kept states at t)
    best: int  # the count of the witness over c(0 .. T)
    free: list[int]  # the witness free word f(0 .. T - 1)


def committed(B: np.ndarray, C: np.ndarray, R: np.ndarray, k: int, color: int) -> np.ndarray:
    """For each state at time t, the cells of the color among c(t + 1 .. t + k). The free cell at time s first reaches
    the center at time s + k + 1, so these centers are fixed by the state; they are computed on the 64 cells of the
    left half nearest the center, which is exact for k <= 62."""
    # B: (n, W); C, R: (n,) uint64
    Bw, Cw, Rw = B[:, :1].copy(), C.copy(), R.copy()  # (n, 1), (n,), (n,)
    out = np.zeros(len(C), np.int32)  # (n,)
    for _ in range(k):
        Bw, Cw, Rw = level_step(Bw, Cw, Rw, k, 0)
        out += (Cw == np.uint64(color)).astype(np.int32)
    return out


def ladder_beam(T: int, k: int, color: int, width: int, every: int = 50, seed: int = 0, lookahead: bool = True,
                progress: bool = False) -> BeamResult:
    """A lower bound on M_b(k, T): after each step keep the `width` states with the largest counts (ties broken at
    random with `seed`), and return a free word that attains the best kept count. With `lookahead` the states are
    ranked by the count over c(0 .. t + k), which the state at t fixes (`committed`); without it, by the count over
    c(0 .. t), which ranks states that differ only in the free cells of the last k steps at random."""
    assert k <= 62
    rng = np.random.default_rng(seed)
    B, C, R = _start(T)
    V = np.array([int(color == 1)], np.int32)  # (1,)
    F = np.zeros((1, T // 64 + 1), np.uint64)  # (1, Wf)
    checkpoints: list[tuple[int, int]] = []
    for t in tqdm(range(T), desc=f"beam k={k} b={color}", file=sys.stderr, disable=not progress):
        B, C, R, V, F = reduce_max(*_expand(B, C, R, V, k, color, t, F))
        assert F is not None
        if len(V) > width:
            score = V + 0.5 * rng.random(len(V))  # (n,)
            if lookahead:
                score = score + committed(B, C, R, k, color)
            keep = np.argpartition(-score, width)[:width]  # (width,)
            B, C, R, V, F = B[keep], C[keep], R[keep], V[keep], F[keep]
        if (t + 1) % every == 0 or t + 1 == T:
            checkpoints.append((t + 1, int(V.max())))
    i = int(np.argmax(V))
    free = [int((F[i, s // 64] >> np.uint64(s % 64)) & np.uint64(1)) for s in range(T)]
    return BeamResult(checkpoints, int(V[i]), free)


def steady_rate(checkpoints: list[tuple[int, int]], start: int) -> float:
    """The gain per step of the beam's best count from the checkpoint at `start` to the last one."""
    t0, v0 = next((t, v) for t, v in checkpoints if t >= start)
    t1, v1 = checkpoints[-1]
    return (v1 - v0) / (t1 - t0)


# ---------------------------------------------------------------------------------------------------------------------
# Independent replay, cell by cell
# ---------------------------------------------------------------------------------------------------------------------


def simulate(k: int, free: np.ndarray) -> np.ndarray:
    """The center columns c(0 .. T) of level k for a batch of free words, by Rule 30 on the row of cells
    -(T + 1) .. k + 1 started from the single cell, with cell k + 1 overwritten by f(t) before step t."""
    # free: (m, T) uint8, column t is f(t)
    m, T = free.shape
    width = T + k + 3
    o = T + 1  # the index of cell 0
    row = np.zeros((m, width), np.uint8)  # (m, width), index o + i is cell i
    row[:, o] = 1
    out = np.zeros((m, T + 1), np.uint8)  # (m, T + 1)
    out[:, 0] = 1
    for t in range(T):
        row[:, o + k + 1] = free[:, t]
        new = np.zeros_like(row)  # (m, width)
        new[:, 1:-1] = row[:, :-2] ^ (row[:, 1:-1] | row[:, 2:])
        row = new
        out[:, t + 1] = row[:, o]
    return out


def single_cell_column(T: int, col: int) -> np.ndarray:
    """Column `col` of the single cell at times 0 .. T."""
    width = 2 * T + 3
    o = T + 1
    row = np.zeros(width, np.uint8)  # (width,)
    row[o] = 1
    out = np.zeros(T + 1, np.uint8)  # (T + 1,)
    out[0] = row[o + col]
    for t in range(T):
        new = np.zeros_like(row)  # (width,)
        new[1:-1] = row[:-2] ^ (row[1:-1] | row[2:])
        row = new
        out[t + 1] = row[o + col]
    return out


def single_cell_count(T: int, color: int) -> int:
    """The single cell's cells of the color among c(0 .. T), a lower bound on M_b(k, T) at every level."""
    return int((single_cell_column(T, 0) == color).sum())


# ---------------------------------------------------------------------------------------------------------------------
# Drivers
# ---------------------------------------------------------------------------------------------------------------------


def runs(word: np.ndarray) -> list[tuple[int, int]]:
    """The maximal runs of a 0/1 word as (color, length)."""
    # word: (n,)
    out: list[tuple[int, int]] = []
    for b in word.tolist():
        if out and out[-1][0] == b:
            out[-1] = (b, out[-1][1] + 1)
        else:
            out.append((b, 1))
    return out


def free_decided(k: int, free: np.ndarray) -> np.ndarray:
    """For each time s in 0 .. T - 1, whether flipping f(s) alone changes the center column c(0 .. T)."""
    # free: (T,) uint8
    T = len(free)
    flips = np.repeat(free[None, :], T + 1, axis=0)  # (T + 1, T), row 0 unflipped, row s + 1 flips f(s)
    flips[np.arange(1, T + 1), np.arange(T)] ^= 1
    cols = simulate(k, flips)  # (T + 1, T + 1)
    return (cols[1:] != cols[0][None, :]).any(axis=1)  # (T,)


def first_change(k: int, free: np.ndarray) -> np.ndarray:
    """For each s, the first time u at which flipping f(s) alone changes c(u), or -1 if it never does by T."""
    # free: (T,) uint8
    T = len(free)
    flips = np.repeat(free[None, :], T + 1, axis=0)  # (T + 1, T)
    flips[np.arange(1, T + 1), np.arange(T)] ^= 1
    cols = simulate(k, flips)  # (T + 1, T + 1)
    diff = cols[1:] != cols[0][None, :]  # (T, T + 1)
    return np.where(diff.any(axis=1), diff.argmax(axis=1), -1)  # (T,)


# ---------------------------------------------------------------------------------------------------------------------
# Command line
# ---------------------------------------------------------------------------------------------------------------------


def _levels(text: str) -> list[int]:
    return [int(x) for x in text.split(",")]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("exact")
    p.add_argument("--steps", type=int, default=100)
    p.add_argument("--levels", type=_levels, default=[1, 2, 3])
    p.add_argument("--every", type=int, default=10)
    p.add_argument("--colors", type=_levels, default=[0, 1])
    p = sub.add_parser("beam")
    p.add_argument("--steps", type=int, default=1000)
    p.add_argument("--levels", type=_levels, default=[1])
    p.add_argument("--width", type=int, default=60000)
    p.add_argument("--every", type=int, default=100)
    p.add_argument("--colors", type=_levels, default=[0, 1])
    p.add_argument("--plain", action="store_true", help="rank by the count so far, without the lookahead")
    p = sub.add_parser("drivers")
    p.add_argument("--steps", type=int, default=1000)
    p.add_argument("--levels", type=_levels, default=[1])
    p.add_argument("--width", type=int, default=60000)
    p.add_argument("--colors", type=_levels, default=[0, 1])
    args = parser.parse_args()

    if args.cmd == "exact":
        for k in args.levels:
            for color in args.colors:
                single = {t: single_cell_count(t, color) for t in range(args.steps + 1)}
                for row in ladder_exact(args.steps, k, color, args.every, progress=True):
                    extra = ""
                    if row.window is not None:
                        span = row.t - row.t // 2
                        extra = f"  window {row.window}/{span} = {row.window / span:.3f}"
                    print(f"k={k} b={color} t={row.t:4d} states={row.states:9d} max={row.best:4d} "
                          f"ratio={row.best / (row.t + 1):.3f} single={single[row.t]}{extra}", flush=True)
    elif args.cmd == "beam":
        for k in args.levels:
            for color in args.colors:
                res = ladder_beam(args.steps, k, color, args.width, args.every, lookahead=not args.plain,
                                  progress=True)
                replay = simulate(k, np.array([res.free], np.uint8))[0]  # (T + 1,)
                assert int((replay == color).sum()) == res.best
                pts = " ".join(f"{t}:{v}" for t, v in res.checkpoints)
                print(f"k={k} b={color} width={args.width} lookahead={not args.plain} best={res.best} "
                      f"ratio={res.best / (args.steps + 1):.4f} single={single_cell_count(args.steps, color)}",
                      flush=True)
                print(f"  checkpoints {pts}", flush=True)
                gains = [b - a for (_, a), (_, b) in zip(res.checkpoints, res.checkpoints[1:])]
                print(f"  gains per {args.every} steps: {gains}", flush=True)
                print(f"  steady rate from t = {args.steps // 2}: {steady_rate(res.checkpoints, args.steps // 2):.4f}",
                      flush=True)
    else:
        for k in args.levels:
            for color in args.colors:
                res = ladder_beam(args.steps, k, color, args.width, progress=True)
                free = np.array(res.free, np.uint8)  # (T,)
                center = simulate(k, free[None, :])[0]  # (T + 1,)
                rs = runs(center[args.steps // 2:])
                hist: dict[tuple[int, int], int] = {}
                for r in rs:
                    hist[r] = hist.get(r, 0) + 1
                first = first_change(k, free)  # (T,)
                span = np.arange(args.steps // 4, args.steps // 2)  # (T / 4,), free cells with time to act
                acts = first[span] >= 0  # (T / 4,)
                lag = first[span][acts] - span[acts]  # (a,)
                mean_run = {b: np.mean([n for c, n in rs if c == b]) for b in (0, 1)}
                print(f"k={k} b={color} best={res.best} ratio={res.best / (args.steps + 1):.4f}", flush=True)
                print("  center, last 120:", "".join(map(str, center[-120:].tolist())), flush=True)
                print("  runs in the second half (color, length): count:", sorted(hist.items()), flush=True)
                print(f"  mean run in the second half: white {mean_run[0]:.2f}, black {mean_run[1]:.2f}", flush=True)
                print(f"  free cells f(s), {span[0]} <= s < {span[-1] + 1}: {acts.sum()} of {len(span)} change the "
                      f"center by T; lag to the first change: {np.mean(lag == k + 1):.2f} exactly k + 1, median "
                      f"{np.median(lag):.0f}, 90th percentile {np.percentile(lag, 90):.0f}, largest {lag.max()}",
                      flush=True)

if __name__ == "__main__":
    main()
