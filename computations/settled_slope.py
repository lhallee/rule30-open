"""The hypotheses of the SettledSlope module, checked on the single cell's left diagonals.

The left diagonals D_j(t) = cell(t, j - t) of the single black cell obey D_{j+2}(t+1) = D_j(t) xor (D_{j+1}(t) or
D_{j+2}(t)), with D_0 = 1 and D_1(t) = 1 for t >= 1. Diagonal j depends only on the diagonals i <= j, so the vector
v_t = (D_0(t), ..., D_J(t)) evolves by itself: bit k of v_{t+1} is bit k - 2 of v_t xor (bit k - 1 or bit k), from
v_0 = 1. `stream` runs it as a Python integer and records, for each diagonal, the first time from which it repeats with
a common period (64, a multiple of every period to depth 200,000), and the last `window` rows.

From those rows, for the hypotheses of `Rule30Open.Diagonals.SettledSlope`:

- `least_periods`: the least power-of-two period of each diagonal on the last rows;
- `white_runs`: the longest cyclic white run g_j of the periodic part of D_j (-1 if D_j is white);
- `alternations`: the longest antiphase alternation m_j of the pair (D_j, D_{j+1}): the largest number of consecutive
  times at which D_{j+1} = not D_j and D_j changes from each time to the next (so no window of m_j + 1 times exists,
  the Lean `AltBound j T m_j`);
- `pair_onset_bound`: the pair onset Q_j = 1 + sum_{i=1}^{j} c_i that the reset lemma gives, with c_i = g_i + 1, or
  0 for a white diagonal (`pair_repeats_of_white_runs` in Lean);
- `settling_offset`: the least delta with T_j <= ceil(num j / den) + delta for every j, the settling hypothesis at
  gamma = num / den.

    python -m computations.settled_slope --depth 200000   # about 3 min, 0.2 GB
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass

import numpy as np
from tqdm.auto import tqdm


@dataclass(frozen=True, slots=True)
class Diagonals:
    depth: int  # diagonals 0 .. depth are read
    steps: int  # times 0 .. steps - 1
    period: int  # the common period of the onsets
    onset: np.ndarray  # (depth + 1,) least T with D_j(t + period) = D_j(t) for T <= t <= steps - 1 - period
    tail: np.ndarray  # (window, depth + 1) D_j(t) for t = steps - window .. steps - 1


def bits(v: int, n: int) -> np.ndarray:
    """Bits 0 .. n - 1 of v."""
    raw = v.to_bytes((n + 7) // 8, "little")
    return np.unpackbits(np.frombuffer(raw, dtype=np.uint8), bitorder="little")[:n]  # (n,)


def stream(depth: int, steps: int, period: int = 64, window: int = 256, progress: bool = True) -> Diagonals:
    """Evolve the vector of diagonals 0 .. depth for `steps` times; onsets with respect to `period`, last rows."""
    assert window <= steps and period < steps
    n = depth + 1
    mask = (1 << n) - 1
    v = 1  # bit j is D_j(t)
    ring = [0] * period  # ring[t % period] = v_{t - period} when read at time t
    last = np.full(n, -1, dtype=np.int64)  # (n,): the last t - period with D_j(t) != D_j(t - period)
    tail = np.zeros((window, n), dtype=np.uint8)  # (window, n)
    for t in tqdm(range(steps), desc="diagonals", unit="step", file=sys.stderr, mininterval=5, disable=not progress):
        if t >= period:
            d = v ^ ring[t % period]
            if d:
                lo = ((d & -d).bit_length() - 1) // 8 * 8  # a byte boundary at or below the lowest change
                changed = bits(d >> lo, d.bit_length() - lo)  # (hi - lo,)
                last[np.flatnonzero(changed) + lo] = t - period
        if t >= steps - window:
            tail[t - (steps - window)] = bits(v, n)
        ring[t % period] = v
        v = ((v << 2) ^ ((v << 1) | v)) & mask
    return Diagonals(depth, steps, period, last + 1, tail)


def least_periods(tail: np.ndarray) -> np.ndarray:
    """The least power of two p with D_j(t + p) = D_j(t) on the rows, for each diagonal (0 if none up to len / 4)."""
    # tail: (window, n)
    window, n = tail.shape
    period = np.zeros(n, dtype=np.int64)  # (n,)
    p = 1
    while 4 * p <= window:
        new = (tail[p:] == tail[:-p]).all(axis=0) & (period == 0)  # (n,)
        period[new] = p
        p *= 2
    return period  # (n,)


def white_runs(tail: np.ndarray) -> np.ndarray:
    """The longest white run of each diagonal on the rows, -1 if it is white there. On rows that cover the periodic part
    twice this is the longest cyclic white run g_j of the periodic part."""
    # tail: (window, n)
    run = np.zeros(tail.shape[1], dtype=np.int64)  # (n,)
    best = np.zeros(tail.shape[1], dtype=np.int64)  # (n,)
    for row in tail:  # (n,)
        run = np.where(row == 0, run + 1, 0)
        best = np.maximum(best, run)
    best[best == tail.shape[0]] = -1
    return best  # (n,)


def alternations(tail: np.ndarray) -> np.ndarray:
    """For each pair (D_j, D_{j+1}), j < n - 1: the largest number of consecutive times on the rows at which
    D_{j+1}(t) != D_j(t), with D_j(t + 1) != D_j(t) between consecutive ones. On rows that cover the periodic part twice
    (plus one) this is the longest antiphase alternation m_j of the settled pair."""
    # tail: (window, n)
    anti = tail[:, 1:] != tail[:, :-1]  # (window, n - 1): D_{j+1}(t) != D_j(t)
    link = tail[1:, :-1] != tail[:-1, :-1]  # (window - 1, n - 1): D_j(t + 1) != D_j(t)
    run = anti[0].astype(np.int64)  # (n - 1,)
    best = run.copy()  # (n - 1,)
    for t in range(1, tail.shape[0]):
        run = np.where(anti[t], np.where(link[t - 1], run + 1, 1), 0)
        best = np.maximum(best, run)
    return best  # (n - 1,)


def pair_onset_bound(white_run: np.ndarray) -> np.ndarray:
    """Q_j = 1 + sum_{i=1}^{j} c_i with c_i = g_i + 1 (0 for a white diagonal): the time from which the reset lemma
    makes the pair (D_j, D_{j+1}) repeat (`pair_repeats_of_white_runs`)."""
    # white_run: (n,)
    cost = white_run + 1  # (n,), 0 where white_run = -1
    cost[0] = 0
    return 1 + np.cumsum(cost)  # (n,)


def settling_offset(onset: np.ndarray, num: int, den: int) -> int:
    """The least delta >= 0 with onset_j <= ceil(num j / den) + delta for every j."""
    # onset: (n,)
    j = np.arange(len(onset), dtype=np.int64)  # (n,)
    return max(0, int((onset - (num * j + den - 1) // den).max()))


def cost_offset(white_run: np.ndarray, gamma: int) -> int:
    """The least delta >= 0 with sum_{i=1}^{j} c_i <= gamma j + delta for every j (the Lean `costSum`)."""
    # white_run: (n,)
    S = pair_onset_bound(white_run) - 1  # (n,)
    return max(0, int((S - gamma * np.arange(len(S), dtype=np.int64)).max()))


@dataclass(frozen=True, slots=True)
class PeriodRow:
    period: int  # least period P of the diagonals in the row
    first: int  # the first and last depth with that period
    last: int
    count: int  # diagonals with that period
    mean_cost: float  # mean of c_j = g_j + 1 over them
    max_white: int  # largest cyclic white run g_j
    max_alt: int  # largest antiphase alternation m_j of the pairs (D_j, D_{j+1}) among them


def by_period(period: np.ndarray, white_run: np.ndarray, alt: np.ndarray) -> list[PeriodRow]:
    """The white runs and alternations of the settled diagonals grouped by least period (white diagonals left out)."""
    # period, white_run: (n,); alt: (n - 1,)
    rows: list[PeriodRow] = []
    for p in sorted(set(period[white_run >= 0].tolist())):
        sel = np.flatnonzero((period == p) & (white_run >= 0))  # (k,)
        pairs = sel[sel < len(alt)]  # (k',)
        rows.append(PeriodRow(p, int(sel.min()), int(sel.max()), len(sel), float((white_run[sel] + 1).mean()),
                              int(white_run[sel].max()), int(alt[pairs].max()) if len(pairs) else 0))
    return rows


def black_slope(num: int, den: int) -> tuple[int, int]:
    """The slope 3 (gamma - 1) / (5 gamma - 1) at gamma = num / den, as (numerator, denominator)."""
    return 3 * (num - den), 5 * num - den


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--depth", type=int, default=200000)
    parser.add_argument("--steps", type=int, default=0, help="default 3 depth / 2 + 600")
    args = parser.parse_args()
    steps = args.steps or 3 * args.depth // 2 + 600
    d = stream(args.depth, steps)
    j = np.arange(args.depth + 1)  # (n,)
    checked = d.onset <= steps - 4 * d.period  # (n,): onset read with at least four periods after it
    print(f"diagonals 0 .. {args.depth}, {steps} steps, onsets for period {d.period}; "
          f"onset at least four periods before the end for every j: {bool(checked.all())}")
    period = least_periods(d.tail)  # (n,)
    white = white_runs(d.tail)  # (n,)
    alt = alternations(d.tail)  # (n - 1,)
    print(f"least periods seen: {sorted(set(period.tolist()))}; white diagonals: {np.flatnonzero(white < 0).tolist()}")
    for num, den in [(3, 2), (27, 20), (4, 3)]:
        s = black_slope(num, den)
        print(f"gamma = {num}/{den}: delta = {settling_offset(d.onset, num, den)}, black slope {s[0]}/{s[1]}"
              f" = {s[0] / s[1]:.4f}")
    print(f"{'depths':>18} {'max T/j':>8} {'at':>7} {'max g':>6} {'mean g+1':>9} {'max m':>6} {'Q_j/j':>7}")
    Q = pair_onset_bound(white)  # (n,)
    for lo, hi in [(1, 8), (8, 100), (100, 400), (400, 8000), (8000, 53207), (53207, 87867), (87867, args.depth)]:
        if hi > args.depth or lo >= hi:
            continue
        r = d.onset[lo:hi] / j[lo:hi]  # (hi - lo,)
        k = int(np.argmax(r))
        cost = np.where(white[lo:hi] < 0, 0, white[lo:hi] + 1)  # (hi - lo,)
        print(f"{lo:>8} .. {hi - 1:>7} {r.max():8.4f} {lo + k:>7} {int(white[lo:hi].max()):>6} {cost.mean():9.3f}"
              f" {int(alt[lo:min(hi, args.depth)].max()):>6} {Q[hi - 1] / (hi - 1):7.3f}")
    print(f"longest antiphase alternation over every pair j < {args.depth}: {int(alt.max())} times, at "
          f"{np.flatnonzero(alt == alt.max())[:5].tolist()}")
    print(f"{'period':>6} {'depths':>18} {'count':>7} {'mean c':>7} {'max g':>6} {'max m':>6}")
    for r in by_period(period, white, alt):
        print(f"{r.period:>6} {r.first:>8} .. {r.last:>7} {r.count:>7} {r.mean_cost:7.3f} {r.max_white:>6} {r.max_alt:>6}")
    for gamma in [4, 5, 6]:
        print(f"white-run cost: sum c_i <= {gamma} j + {cost_offset(white, gamma)} for j <= {args.depth}")


if __name__ == "__main__":
    main()
