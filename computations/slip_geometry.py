"""Where the slips of column 1 beside an alternating center come from.

Drive the empty right half with a center reading 0, 1, 0, 1, ... (center 0 at even times). Column 1 nearly repeats
the block AAAB of 36 steps (A = 1000100110, B = 100110) and slips about once per 145 steps
([the right channel](../findings/period-two/right-channel.md)). This module follows the slips in space and time.

A right half is an integer whose bit i is cell i + 1; one step with center bit c is
R -> ((R << 1) | c) ^ (R | (R >> 1)). Column 1 at times before `steps` needs only bits below `steps - t + width` at
time t, so the integer is cut back as the run goes on.

    python -m computations.slip_geometry --steps 1000000             # slips, runs, renewal tests, about 1 minute
    python -m computations.slip_geometry --steps 200000 --fronts     # the locked layer and the front, about 2 minutes
    python -m computations.slip_geometry --steps 200000 --reach      # how far right column 1 looks, about 2 minutes
    python -m computations.slip_geometry --steps 400000 --windows    # windows with a white or i.i.d. right boundary
"""

from __future__ import annotations

import argparse
import sys

import numpy as np
from scipy import stats
from tqdm.auto import tqdm

LAG = 36  # the period of AAAB
A_BLOCK = "1000100110"
B_BLOCK = "100110"


def center_bit(t: int, phase: int = 0) -> int:
    """The alternating center at time t: 0 at even times when `phase` is 0, 1 at even times when it is 1."""
    return (int(t) + phase) & 1


def right_rows(steps: int, width: int, phase: int = 0, start: int = 0, progress: bool = False) -> np.ndarray:
    """Cells 1 .. width of the right half `start` driven by the alternating center, at times 0 .. steps - 1. Exact:
    the integer keeps every bit that column `width` can still feel before `steps`."""
    rows = np.zeros((steps, width), dtype=np.uint8)  # (steps, width)
    nbytes = (width + 7) // 8
    low = (1 << width) - 1
    row = start
    for t in tqdm(range(steps), disable=not progress, mininterval=5.0):
        chunk = np.frombuffer((row & low).to_bytes(nbytes, "little"), dtype=np.uint8)  # (nbytes,)
        rows[t] = np.unpackbits(chunk, bitorder="little")[:width]
        row = ((row << 1) | center_bit(t, phase)) ^ (row | (row >> 1))
        if t % 4096 == 0:
            row &= (1 << (steps - t + width + 2)) - 1
    return rows  # (steps, width)


def column_one(steps: int, phase: int = 0, start: int = 0, progress: bool = False) -> np.ndarray:
    """Column 1 at times 0 .. steps - 1 (the first column of `right_rows`)."""
    return right_rows(steps, 1, phase, start, progress)[:, 0]  # (steps,)


def direct_rows(steps: int, width: int, phase: int = 0) -> np.ndarray:
    """The same cells by a direct run of the rule on an array of `steps + width + 1` cells, the independent check."""
    n = steps + width + 1
    cells = np.zeros(n, dtype=np.uint8)  # (n,), cell i + 1 at index i
    out = np.zeros((steps, width), dtype=np.uint8)  # (steps, width)
    for t in range(steps):
        out[t] = cells[:width]
        left = np.concatenate([[center_bit(t, phase)], cells[:-1]])  # (n,)
        right = np.concatenate([cells[1:], [0]])  # (n,)
        cells = left ^ (cells | right)
    return out  # (steps, width)


def window_rows(steps: int, width: int, boundary: str, phase: int = 0, seed: int = 0) -> np.ndarray:
    """Cells 1 .. width of a window driven by the alternating center on the left and, on the right, by a column that
    is white (`boundary` = "white") or i.i.d. fair bits (`boundary` = "iid")."""
    rng = np.random.default_rng(seed)
    noise = rng.integers(0, 2, steps) if boundary == "iid" else np.zeros(steps, dtype=np.int64)  # (steps,)
    cells = np.zeros(width, dtype=np.uint8)  # (width,)
    out = np.zeros((steps, width), dtype=np.uint8)  # (steps, width)
    for t in range(steps):
        out[t] = cells
        left = np.concatenate([[center_bit(t, phase)], cells[:-1]])  # (width,)
        right = np.concatenate([cells[1:], [noise[t]]])  # (width,)
        cells = left ^ (cells | right)
    return out  # (steps, width)


def window_column_one(steps: int, width: int, boundary: str, phase: int = 0, seed: int = 0) -> np.ndarray:
    """Column 1 of `window_rows`, run with integers for speed: bit i is cell i + 1, bit `width` the boundary column."""
    rng = np.random.default_rng(seed)
    noise = rng.integers(0, 2, steps) if boundary == "iid" else np.zeros(steps, dtype=np.int64)  # (steps,)
    mask = (1 << width) - 1
    row = 0
    column = np.zeros(steps, dtype=np.uint8)  # (steps,)
    for t in range(steps):
        column[t] = row & 1
        full = row | (int(noise[t]) << width)
        row = (((row << 1) | center_bit(t, phase)) ^ (row | (full >> 1))) & mask
    return column  # (steps,)


def slip_events(column: np.ndarray, lag: int = LAG, merge: int = LAG) -> tuple[np.ndarray, np.ndarray]:
    """Slip events of a column: maximal clusters of times t >= lag with column[t] != column[t - lag], two mismatches
    joined when fewer than `merge` steps apart. Returns the first and last mismatch of each event."""
    # column: (T,)
    times = np.flatnonzero(column[lag:] != column[:-lag]) + lag  # (m,)
    if times.size == 0:
        return np.zeros(0, dtype=np.int64), np.zeros(0, dtype=np.int64)
    cut = np.flatnonzero(np.diff(times) >= merge)  # (e - 1,)
    starts = np.concatenate([[times[0]], times[cut + 1]])  # (e,)
    ends = np.concatenate([times[cut], [times[-1]]])  # (e,)
    return starts, ends


def lock_depth(rows: np.ndarray, lag: int = LAG) -> np.ndarray:
    """For each time t >= lag, the number of columns 1, 2, ... that agree with themselves `lag` steps earlier before
    the first that does not (the width of the locked layer); the full width when all agree. -1 before `lag`."""
    # rows: (T, W)
    T, W = rows.shape
    depth = np.full(T, -1, dtype=np.int64)  # (T,)
    diff = rows[lag:] != rows[:-lag]  # (T - lag, W)
    depth[lag:] = np.where(diff.any(axis=1), diff.argmax(axis=1), W)
    return depth  # (T,)


def renewal_tests(gaps: np.ndarray, lags: int = 5, permutations: int = 2000, seed: int = 0) -> dict[str, object]:
    """Statistics of interarrival times: mean, coefficient of variation, Spearman correlation of gaps `k` apart for
    k = 1 .. lags with a two-sided permutation p-value, and the Kolmogorov-Smirnov distance to a geometric law with the
    same mean shifted to the least gap (a memoryless renewal process past its dead time), taken over the integers."""
    rng = np.random.default_rng(seed)
    gaps = np.asarray(gaps, dtype=np.float64)  # (n,)
    out: dict[str, object] = {"count": int(gaps.size), "mean": float(gaps.mean()),
                              "cv": float(gaps.std() / gaps.mean())}
    corr: list[tuple[int, float, float]] = []
    for k in range(1, lags + 1):
        rho = stats.spearmanr(gaps[:-k], gaps[k:]).statistic
        null = np.array([stats.spearmanr(g[:-k], g[k:]).statistic
                         for g in (rng.permutation(gaps) for _ in range(permutations))])  # (permutations,)
        p = (1 + np.sum(np.abs(null) >= abs(rho))) / (permutations + 1)
        corr.append((k, float(rho), float(p)))
    out["serial"] = corr
    low = gaps.min()
    q = 1.0 / (gaps.mean() - low + 1.0)
    k = np.arange(0, int(gaps.max() - low) + 1)  # (K,)
    ecdf = np.searchsorted(np.sort(gaps - low), k, side="right") / gaps.size  # (K,)
    out["ks_geometric"] = float(np.max(np.abs(ecdf - stats.geom(q, loc=-1).cdf(k))))
    return out


def leftward_damage_speed(width: int, steps: int, trials: int, seed: int = 0) -> np.ndarray:
    """For `trials` uniform random rows on a ring of `width` cells, flip the middle cell and follow the leftmost cell
    that differs between the two runs: returns its leftward displacement after each step, averaged over trials. The
    damage moves right at speed 1, so its left edge measures how fast information travels leftward."""
    rng = np.random.default_rng(seed)
    a = rng.integers(0, 2, (trials, width), dtype=np.uint8)  # (trials, width)
    b = a.copy()
    mid = width // 2
    b[:, mid] ^= 1
    shift = np.zeros(steps, dtype=np.float64)  # (steps,)
    for t in range(steps):
        a = np.roll(a, 1, axis=1) ^ (a | np.roll(a, -1, axis=1))
        b = np.roll(b, 1, axis=1) ^ (b | np.roll(b, -1, axis=1))
        diff = (a != b)[:, :mid + 1]  # (trials, mid + 1)
        left = np.where(diff.any(axis=1), diff.argmax(axis=1), mid + 1)  # (trials,)
        shift[t] = float(np.mean(mid - left))
    return shift  # (steps,)


def advance(row: int, t: int, k: int, phase: int = 0) -> tuple[int, np.ndarray]:
    """Run the right half `row` from time t for k steps; return the final row and column 1 at times t .. t + k - 1."""
    column = np.zeros(k, dtype=np.uint8)  # (k,)
    for j in range(k):
        column[j] = row & 1
        row = ((row << 1) | center_bit(t + j, phase)) ^ (row | (row >> 1))
    return row, column  # (k,)


def reach(row: int, t: int, look: int, horizon: int, trials: int, rng: np.random.Generator, phase: int = 0) -> int:
    """The least X such that replacing every cell right of column X of the right half `row` at time t by fresh random
    bits leaves column 1 unchanged at times t .. t + look + horizon - 1 in all `trials` draws. Column 1 at time
    t + j depends on columns 1 .. j + 1 only, so X <= look + horizon."""
    span = look + horizon
    _, truth = advance(row & ((1 << (span + 2)) - 1), t, span, phase)  # (span,)
    lo, hi = 0, span + 1
    while lo < hi:  # least X that passes; passing is monotone in X up to sampling
        x = (lo + hi) // 2
        keep = row & ((1 << x) - 1)
        ok = True
        for _ in range(trials):
            fresh = int.from_bytes(rng.bytes((span + 9) // 8), "little") & ((1 << (span + 2 - x)) - 1)
            _, col = advance(keep | (fresh << x), t, span, phase)
            if not np.array_equal(col, truth):
                ok = False
                break
        if ok:
            hi = x
        else:
            lo = x + 1
    return lo


def states_at(times: list[int], steps: int, phase: int = 0, progress: bool = False) -> dict[int, int]:
    """The right half (cut to the bits that matter before `steps`) at each of the given times."""
    want = set(times)
    out: dict[int, int] = {}
    row = 0
    for t in tqdm(range(steps), disable=not progress, mininterval=5.0):
        if t in want:
            out[t] = row
        row = ((row << 1) | center_bit(t, phase)) ^ (row | (row >> 1))
        if t % 4096 == 0:
            row &= (1 << (steps - t + 4)) - 1
    return out


def front_slopes(depth: np.ndarray, starts: np.ndarray, before: int = 40) -> np.ndarray:
    """For each slip start s, the slope of the lock depth from its last maximum in s - before .. s - 1 down to s:
    the velocity of the front that closes the locked layer (negative means leftward)."""
    out = []
    for s in starts:
        if s - before < LAG:
            continue
        seg = depth[s - before:s + 1]  # (before + 1,)
        top = int(np.flatnonzero(seg == seg.max())[-1])
        if top < before:
            out.append((seg[-1] - seg[top]) / (before - top))
    return np.array(out, dtype=np.float64)  # (n,)


def summarize(column: np.ndarray, label: str) -> dict[str, object]:
    """Slip rate, the event lengths and the renewal tests for one column."""
    starts, ends = slip_events(column)
    gaps = np.diff(starts)  # (e - 1,)
    out: dict[str, object] = {"label": label, "steps": int(column.size), "events": int(starts.size)}
    if starts.size > 20:
        out["per_slip"] = float(column.size / starts.size)
        out["length_median"] = float(np.median(ends - starts + 1))
        out["odd_starts"] = float(np.mean(starts % 2 == 1))
        out.update(renewal_tests(gaps))
        out["gaps"] = gaps
    return out


def print_summary(s: dict[str, object]) -> None:
    """One block of text for a `summarize` result."""
    print(f"{s['label']}: {s['events']} slip events in {s['steps']} steps")
    if "per_slip" in s:
        gaps = s["gaps"]
        assert isinstance(gaps, np.ndarray)
        print(f"  one per {s['per_slip']:.1f} steps; median event length {s['length_median']:.0f}; "
              f"odd starts {s['odd_starts']:.3f}")
        print(f"  gaps: mean {s['mean']:.1f}, cv {s['cv']:.3f}, min {gaps.min()}, quartiles "
              f"{np.percentile(gaps, [25, 50, 75]).tolist()}, max {gaps.max()}; KS to shifted geometric "
              f"{s['ks_geometric']:.3f}")
        for k, rho, p in s["serial"]:  # type: ignore[union-attr]
            print(f"  Spearman of gaps {k} apart {rho:+.4f} (permutation p {p:.4f})")


def gap_runs(column: np.ndarray, phase: int = 0, settle: int = 1000) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Column 1 at the white steps of the center, from step `settle` on, as gaps between black cells: returns the gaps,
    and, for each gap of 3, the number n of gaps of 5 that follow it before the next gap of 3 (the run lengths) and the
    step of the black cell that ends the gap of 3. Beside the alternating center the lock AAAB is n = 3 repeated."""
    # column: (T,)
    white = np.arange(column.size) % 2 == phase % 2  # (T,), center white when (t + phase) is even
    steps = np.flatnonzero(white & (column == 1))  # (b,) steps of black cells at white steps
    steps = steps[steps >= settle]
    gaps = np.diff(steps) // 2  # (b - 1,) in white steps
    threes = np.flatnonzero(gaps == 3)  # (r,)
    runs = np.diff(threes) - 1  # (r - 1,) gaps strictly between consecutive gaps of 3
    return gaps, runs, steps[threes[:-1] + 1]


def pair_dependence(seq: np.ndarray, top: int, permutations: int = 1000, seed: int = 0) -> tuple[float, float]:
    """Chi-square statistic of the table of consecutive pairs (seq[i], seq[i + 1]), values above `top` pooled, and its
    permutation p-value against shuffles of the sequence (independent values with the same frequencies)."""
    rng = np.random.default_rng(seed)
    seq = np.minimum(np.asarray(seq), top)  # (n,)
    values = np.unique(seq)
    code = np.searchsorted(values, seq)  # (n,)
    m = values.size

    def chi(c: np.ndarray) -> float:
        table = np.bincount(c[:-1] * m + c[1:], minlength=m * m).reshape(m, m).astype(np.float64)  # (m, m)
        expect = table.sum(1, keepdims=True) * table.sum(0, keepdims=True) / table.sum()  # (m, m)
        ok = expect > 0
        return float(((table - expect)[ok] ** 2 / expect[ok]).sum())

    stat = chi(code)
    null = np.array([chi(rng.permutation(code)) for _ in range(permutations)])  # (permutations,)
    return stat, float((1 + np.sum(null >= stat)) / (permutations + 1))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--steps", type=int, default=200_000)
    parser.add_argument("--fronts", action="store_true")
    parser.add_argument("--reach", action="store_true")
    parser.add_argument("--windows", action="store_true")
    parser.add_argument("--samples", type=int, default=40, help="slips and random times for --reach")
    args = parser.parse_args()
    if args.fronts:
        run_fronts(args.steps)
    elif args.reach:
        run_reach(args.steps, args.samples)
    elif args.windows:
        run_windows(args.steps)
    else:
        run_summary(args.steps)


def run_summary(steps: int) -> None:
    """Slip events, their renewal tests and the runs of gaps of 5. The two phases give the same column one step apart
    (the empty half under 1, 0, 1, ... is the half under 0, 1, 0, ... a step later), so phase 0 suffices."""
    column = column_one(steps, 0, progress=True)  # (steps,)
    print_summary(summarize(column, "phase 0"))
    gaps, runs, _ = gap_runs(column)
    values, counts = np.unique(gaps, return_counts=True)
    print("gaps between black cells of column 1 at white steps:", dict(zip(values.tolist(), counts.tolist())))
    print(f"gaps of 3 back to back: {int(np.sum((gaps[1:] == 3) & (gaps[:-1] == 3)))}")
    values, counts = np.unique(runs, return_counts=True)
    print(f"runs of gaps of 5 between gaps of 3 ({runs.size}):", dict(zip(values.tolist(), counts.tolist())))
    stat, p = pair_dependence(runs, 12)
    print(f"consecutive runs (pooled above 12): chi-square {stat:.1f}, permutation p {p:.4f}")
    locked = (runs == 3).astype(np.int64)  # (r,)
    stat, p = pair_dependence(locked, 1)
    print(f"consecutive runs, locked (n = 3) or not: chi-square {stat:.1f}, permutation p {p:.4f}")
    cut = np.flatnonzero(np.diff(np.concatenate([[0], locked, [0]])))  # (2 m,) starts and ends of stretches of 3
    stretches = cut[1::2] - cut[0::2]  # (m,) lengths of the maximal stretches of n = 3, in blocks of 36 steps
    p3 = locked.mean()
    print(f"stretches of n = 3: {stretches.size}, mean {stretches.mean():.2f} blocks of 36 steps; independent runs "
          f"with the frequency {p3:.3f} of n = 3 would give mean {1 / (1 - p3):.2f}")
    print_summary({"label": "stretches of n = 3 as interarrival times", "events": int(stretches.size),
                   "steps": int(column.size), "per_slip": float(column.size / stretches.size),
                   "length_median": float("nan"), "odd_starts": float("nan"), "gaps": stretches,
                   **renewal_tests(stretches)})


def run_fronts(steps: int, width: int = 64) -> None:
    """The width of the locked layer and the slope of the front that closes it before each slip."""
    rows = right_rows(steps, width, progress=True)  # (steps, width)
    depth = lock_depth(rows)  # (steps,)
    starts, _ = slip_events(rows[:, 0])
    late = depth[2000:]
    print(f"locked layer over steps 2,000 .. {steps}: mean {late.mean():.2f} columns, percentiles 5/25/50/75/95/99.9 "
          f"{np.percentile(late, [5, 25, 50, 75, 95, 99.9]).tolist()}, max {late.max()}")
    slopes = front_slopes(depth, starts[starts > 2000])  # (n,)
    print(f"front before {slopes.size} slips: median slope {np.median(slopes):.3f}, quartiles "
          f"{np.percentile(slopes, [25, 75]).tolist()} columns per step")
    late_starts = starts[starts > 2000]
    for length in (15, 21, 25):
        prof = approach_profiles(depth, late_starts, length)
        print(f"last {length} steps of lock depth before {late_starts.size} slips: {len(prof)} distinct traces, the "
              f"commonest {list(prof[0][0])} for {prof[0][1]}")
    rng = np.random.default_rng(2)
    sample = [int(x) for x in late_starts[:150]]
    ks = [8, 12, 16, 18, 20, 24, 28, 32]
    states = states_at(sorted({x - k for x in sample for k in ks}), steps)
    column = rows[:, 0]
    for extra in (1, 3, 5):
        frac = [[committed(states[x - k], x - k, k, int(depth[x - k]) + extra, int(column[x - LAG]), 32, rng)
                 for x in sample] for k in ks]
        print(f"layer plus {extra} columns kept {ks} steps before {len(sample)} slips: the slip happens in every "
              f"one of 32 draws for {[round(float(np.mean(np.array(f) == 1)), 3) for f in frac]} of them")
    cols = np.arange(width)[None, :]  # (1, width)
    inside = (cols < depth[:, None]) & (np.arange(steps)[:, None] >= 2000)  # (steps, width)
    outside = (cols > depth[:, None] + 8) & (cols < width - 8) & (np.arange(steps)[:, None] >= 2000)
    control = np.random.default_rng(0).integers(0, 2, (200, 1024), dtype=np.uint8)  # (200, 1024)
    history = []
    for _ in range(300):
        control = np.roll(control, 1, axis=1) ^ (control | np.roll(control, -1, axis=1))
        history.append(control[:, 300:700])
    rand = np.stack(history[-60:], axis=1).reshape(-1, 400)  # (200 * 60, 400), rows of 60-step diagrams in sequence
    for name, mask in (("stripe", stripe_cells), ("ether", ether_cells)):
        marks = mask(rows)  # (steps, width)
        print(f"{name} cells: inside the layer {marks[inside].mean():.4f}, beyond it {marks[outside].mean():.4f}, "
              f"in diagrams of random rows {mask(rand).reshape(200, 60, 400)[:, 8:, 8:-8].mean():.4f}")


def approach_profiles(depth: np.ndarray, starts: np.ndarray, length: int) -> list[tuple[tuple[int, ...], int]]:
    """The lock depth over the last `length` steps up to each slip start, as distinct traces with their counts, most
    common first."""
    counts: dict[tuple[int, ...], int] = {}
    for s in starts:
        if s - length + 1 >= LAG:
            key = tuple(int(v) for v in depth[s - length + 1:s + 1])
            counts[key] = counts.get(key, 0) + 1
    return sorted(counts.items(), key=lambda item: -item[1])


def committed(state: int, t: int, k: int, keep: int, target: int, trials: int, rng: np.random.Generator) -> float:
    """The fraction of `trials` draws in which column 1 at time t + k differs from `target` when the right half
    `state` at time t keeps its columns 1 .. keep and has fresh random bits beyond."""
    base = state & ((1 << keep) - 1)
    hits = 0
    for _ in range(trials):
        fresh = int.from_bytes(rng.bytes((k + 16) // 8), "little")
        _, col = advance(base | (fresh << keep), t, k + 1)
        hits += int(col[k] != target)
    return hits / trials


def stripe_cells(rows: np.ndarray) -> np.ndarray:
    """Cells of a stripe domain: equal to the cell a step earlier and unlike both neighbors (one row per step)."""
    r = rows.astype(np.int8)  # (T, W)
    out = np.zeros(rows.shape, dtype=bool)  # (T, W)
    out[1:, 1:-1] = (r[1:, 1:-1] == r[:-1, 1:-1]) & (r[1:, 1:-1] != r[1:, 2:]) & (r[1:, 1:-1] != r[1:, :-2])
    return out


def ether_cells(rows: np.ndarray) -> np.ndarray:
    """Cells of an ether domain: on a 3 x 3 block of cells each equal to the cell 4 steps earlier and 7 cells right."""
    r = rows.astype(np.int8)  # (T, W)
    base = np.zeros(rows.shape, dtype=bool)  # (T, W)
    base[4:, :-7] = (r[4:, :-7] == r[:-4, :-7]) & (r[4:, :-7] == r[4:, 7:])
    out = base.copy()
    for d in (1, 2):
        out[:, :-d] &= base[:, d:]
        out[d:] &= base[:-d]
    return out


def run_reach(steps: int, samples: int) -> None:
    """How far right, k steps before a slip or before a random step, the cells lie that column 1 depends on."""
    ks = [8, 16, 32, 64, 128, 256]
    rng = np.random.default_rng(5)
    column = column_one(steps)  # (steps,)
    starts, _ = slip_events(column)
    starts = starts[(starts > 2000) & (starts < steps - 10)]
    slips = [int(x) for x in rng.choice(starts, samples, replace=False)]
    randoms = [int(x) for x in rng.integers(2000, steps - 10, samples)]
    states = states_at(sorted({t - k for t in slips + randoms for k in ks}), steps, progress=True)
    for name, times in (("slip", slips), ("random", randoms)):
        reach_k = np.array([[reach(states[t - k], t - k, k, 1, 48, rng) for k in ks]
                            for t in tqdm(times, mininterval=5.0)])  # (samples, len(ks))
        print(f"{name} steps: X(k) for k = {ks}: median {np.median(reach_k, 0).tolist()}, "
              f"max {reach_k.max(0).tolist()}")
        tail = np.polyfit(np.array(ks[-3:], dtype=np.float64), np.median(reach_k, 0)[-3:], 1)
        print(f"  slope of the median over k = {ks[-3:]}: {tail[0]:.3f}")
    speed = leftward_damage_speed(2048, 400, 200)  # (400,)
    print(f"leftward damage speed in uniform random rows, steps 200 .. 400: {(speed[399] - speed[199]) / 200:.3f}")


def run_windows(steps: int) -> None:
    """Columns 1 .. W with a white or an i.i.d. right boundary, against the true half: slip rate and the law of the
    gaps between slips (two-sample Kolmogorov-Smirnov)."""
    truth = column_one(steps, progress=True)  # (steps,)
    tstarts, _ = slip_events(truth)
    tgaps = np.diff(tstarts)  # (e - 1,)
    _, truns, _ = gap_runs(truth)
    print(f"true half: {tstarts.size} slips, one per {steps / tstarts.size:.1f} steps")
    for width in (8, 12, 16, 20, 24, 32, 48, 64):
        for boundary in ("white", "iid"):
            for seed in range(3 if boundary == "iid" else 1):
                column = window_column_one(steps, width, boundary, seed=seed)  # (steps,)
                gaps, runs, _ = gap_runs(column)
                trapped = bool(np.all((gaps[-100:] == 3) | (gaps[-100:] == 5))) if gaps.size > 100 else False
                starts, _ = slip_events(column)
                line = (f"W = {width:2d} {boundary:5s} seed {seed}: {starts.size:5d} slips, "
                        f"last 100 gaps 3 or 5: {trapped}")
                if starts.size > 50:
                    ks = stats.ks_2samp(np.diff(starts), tgaps)
                    line += f", one per {steps / starts.size:6.1f}, KS {ks.statistic:.3f} (p {ks.pvalue:.2g})"
                    if runs.size > 50:
                        kr = stats.ks_2samp(runs, truns)
                        line += f"; runs KS {kr.statistic:.3f} (p {kr.pvalue:.2g})"
                else:
                    tail = column[-400:]
                    period = next((q for q in range(1, 200) if np.array_equal(tail[q:], tail[:-q])), None)
                    line += f", column 1 ends with period {period}"
                print(line)
                sys.stdout.flush()


if __name__ == "__main__":
    main()
