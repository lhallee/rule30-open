"""Right halves driven by a word of least period three: does column 1 settle at the center's white times?

The kit reduces least period three to the words 001 and 011 (`Rule30EtherThree`). Driven by 001, a right half enters a
labeled trap of period 21 (`Rule30EtherThreeTrap.t001`), on which column 1 at the center's white times is a function of
the label, so masked Jen excludes 001 once every finite half enters. This module asks whether 011 has anything of the
kind. It drives right halves with the center repeating the word, records column 1, and reports, for each drive phase,
how many halves have column 1 constant over the second half of the run (the kit's `skeleton_011` forces it at the two
black phases), and how many have column 1 at the white times periodic over the last third of the run.

    python -m computations.period_three --cells 12 --steps 6000   # every right half of up to 12 cells, both words
    python -m computations.period_three --long 100000             # the white half and 11 random halves of 24 cells
    python -m computations.period_three --follow 2351:0 3682:2 4033:2 --steps 200000   # when given 001 halves settle
    python -m computations.period_three --trap --cells 10 --steps 400000   # exact entry into t001, every small half
    python -m computations.period_three --conditioned-coin 16 --cells 8 --steps 50000   # the coin beyond, conditioned
    python -m computations.period_three --cut-profile --cells 8 --steps 2000000   # entry into t001 cut, and the coin

`--trap` reads the kit's trap `t001` from its source, 815 states of 47 columns with labels modulo 21, and finds the
first step at which each right half, driven by 001, has its columns 1 .. 47 equal to a state whose label agrees with
the drive's phase modulo 3. The trap is closed (`t001_check`), so the half stays in it from then on.
"""

from __future__ import annotations

import argparse
import re
import sys
import time
import numpy as np

from pathlib import Path

from tqdm.auto import tqdm

from computations.absorption import step_rows


WORDS = ("001", "011")
TRAP = Path(__file__).resolve().parents[1] / ".lake/packages/rule30prize/lean/Ruliology/CellularAutomata/Rule30EtherThreeTrap.lean"
TRAP_WIDTH = 47  # the columns t001 reads


def column_one(word: str, halves: list[int], phase: int, steps: int) -> np.ndarray:
    """Column 1 of each right half (bit j is column j + 1) at times 0 .. steps - 1, driven by the center repeating
    `word` from `phase`: the center reads word[(t + phase) % 3] at time t."""
    width = max([1] + [half.bit_length() for half in halves])
    rows = np.zeros((len(halves), (width + steps) // 64 + 2), dtype=np.uint64)  # (n, words)
    for i, half in enumerate(halves):
        for j in range(0, width, 64):
            rows[i, j // 64] = np.uint64((half >> j) & ((1 << 64) - 1))
    column = np.zeros((steps, len(halves)), dtype=np.uint8)  # (steps, n)
    for t in tqdm(range(steps), desc=f"{word} phase {phase}", file=sys.stderr, leave=False, disable=steps < 20000):
        column[t] = (rows[:, 0] & np.uint64(1)).astype(np.uint8)
        active = (width + t) // 64 + 2  # the half reaches column width + t + 1 at most
        rows[:, :active] = step_rows(rows[:, :active], int(word[(t + phase) % 3]))
    return column  # (steps, n)


def settled_periods(samples: np.ndarray, window: int) -> np.ndarray:
    """For each column of `samples`, the least p such that its last `window` entries repeat with period p, or 0 when no
    p up to len(samples) - window works."""
    # samples: (k, n)
    k = samples.shape[0]
    tail = samples[k - window:]  # (window, n)
    periods = np.zeros(samples.shape[1], dtype=np.int64)  # (n,)
    for p in range(1, k - window + 1):
        match = (tail == samples[k - window - p:k - p]).all(axis=0) & (periods == 0)  # (n,)
        periods[match] = p
    return periods  # (n,)


def report(word: str, halves: list[int], phase: int, steps: int) -> tuple[list[tuple[float, float, float]], np.ndarray]:
    """For each drive phase: the fractions of halves whose column 1 is always black, always white, over the second half
    of the run, and the mean of column 1 there; and the settled period of column 1 at the white times, in samples, per
    half (0 for none)."""
    column = column_one(word, halves, phase, steps)  # (steps, n)
    times = np.arange(steps)  # (steps,)
    rows = []
    for drive in range(3):
        values = column[(times >= steps // 2) & ((times + phase) % 3 == drive)]  # (k, n)
        rows.append((float((values == 1).all(axis=0).mean()), float((values == 0).all(axis=0).mean()),
                     float(values.mean())))
    white = np.array([word[(t + phase) % 3] == "0" for t in range(steps)])  # (steps,)
    samples = column[white]  # (k, n)
    return rows, settled_periods(samples, samples.shape[0] // 3)


def settled_from(word: str, half: int, phase: int, steps: int, period: int) -> int:
    """The first step from which column 1 at the white times repeats with `period` samples to the end of the run."""
    column = column_one(word, [half], phase, steps)[:, 0]  # (steps,)
    times = np.flatnonzero([word[(t + phase) % 3] == "0" for t in range(steps)])  # (k,)
    samples = column[times]  # (k,)
    misses = np.flatnonzero(samples[period:] != samples[:-period])  # (m,)
    first = int(misses[-1]) + period + 1 if len(misses) else 0
    return int(times[min(first, len(times) - 1)])


def trap_keys() -> np.ndarray:
    """The states of the kit's trap t001 as sorted keys strip * 4 + (label mod 3), read from the kit's source."""
    packed = dict(re.findall(r"def t001_(\w+) : Nat := (\d+)", TRAP.read_text(encoding="utf-8")))
    digits = sys.get_int_max_str_digits()
    sys.set_int_max_str_digits(0)  # the packed tables have thousands of digits
    try:
        states, labels, count, label_bits = (int(packed[k]) for k in ("R", "L", "n", "lb"))
    finally:
        sys.set_int_max_str_digits(digits)
    keys = {((states >> (TRAP_WIDTH * i)) % (1 << TRAP_WIDTH)) * 4 + ((labels >> (label_bits * i)) % (1 << label_bits)) % 3
            for i in range(count)}
    return np.array(sorted(keys), dtype=np.uint64)  # (n,)


def trap_entries(halves: list[int], phase: int, steps: int, keys: np.ndarray) -> np.ndarray:
    """The first step before `steps` at which each right half, driven by 001 from `phase`, is in t001, or -1."""
    width = max([1] + [half.bit_length() for half in halves])
    rows = np.zeros((len(halves), (width + steps) // 64 + 2), dtype=np.uint64)  # (n, words)
    for i, half in enumerate(halves):
        for j in range(0, width, 64):
            rows[i, j // 64] = np.uint64((half >> j) & ((1 << 64) - 1))
    entry = np.full(len(halves), -1, dtype=np.int64)  # (n,)
    alive = np.arange(len(halves))  # (m,), the halves still outside the trap, row i of `rows` being half alive[i]
    mask = np.uint64((1 << TRAP_WIDTH) - 1)
    for t in tqdm(range(steps), desc=f"t001 phase {phase}", file=sys.stderr, leave=False, mininterval=5):
        drive = (t + phase) % 3
        hit = np.isin((rows[:, 0] & mask) * np.uint64(4) + np.uint64(drive), keys)  # (m,)
        if hit.any():
            entry[alive[hit]] = t
            rows, alive = rows[~hit], alive[~hit]  # the trap is closed: an entered half stays in
            if len(alive) == 0:
                break
        active = (width + t) // 64 + 2  # the half reaches column width + t + 1 at most
        rows[:, :active] = step_rows(rows[:, :active], int("001"[drive]))
    return entry  # (n,)


def cut_entries(halves: list[int], phase: int, steps: int, widths: tuple[int, ...], keys: np.ndarray) -> np.ndarray:
    """For each width w of `widths`, the first step before `steps` at which each right half, driven by 001 from `phase`,
    has its columns 1 .. w equal to those of a state of t001 whose label agrees with the drive's phase, or -1: entry
    into t001 cut to w cells, the event whose rate `lock_chain.t001_coin` gives for a coin in column w + 1. At 47 cells
    it is entry into t001 (`trap_entries`)."""
    width = max([1] + [half.bit_length() for half in halves])
    rows = np.zeros((len(halves), (width + steps) // 64 + 2), dtype=np.uint64)  # (n, words)
    for i, half in enumerate(halves):
        for j in range(0, width, 64):
            rows[i, j // 64] = np.uint64((half >> j) & ((1 << 64) - 1))
    masks = [np.uint64((1 << w) - 1) for w in widths]
    cuts = [np.unique(((keys >> np.uint64(2)) & mask) * np.uint64(4) + (keys & np.uint64(3))) for mask in masks]
    first = np.full((len(halves), len(widths)), -1, dtype=np.int64)  # (n, k)
    alive = np.arange(len(halves))  # (m,), the halves still outside t001, row i of `rows` being half alive[i]
    full = np.uint64((1 << TRAP_WIDTH) - 1)
    for t in tqdm(range(steps), desc=f"cuts of t001 phase {phase}", file=sys.stderr, leave=False, mininterval=5):
        drive = np.uint64((t + phase) % 3)
        for j, (mask, cut) in enumerate(zip(masks, cuts)):
            open_ = np.flatnonzero(first[alive, j] < 0)  # (o,), rows not yet in t001 cut to widths[j] cells
            if open_.size:
                hit = np.isin((rows[open_, 0] & mask) * np.uint64(4) + drive, cut)  # (o,)
                first[alive[open_[hit]], j] = t
        inside = np.isin((rows[:, 0] & full) * np.uint64(4) + drive, keys)  # (m,)
        if inside.any():
            entered = first[alive[inside]]  # (e, k)
            first[alive[inside]] = np.where(entered < 0, t, entered)  # in t001, so in every cut of it
            rows, alive = rows[~inside], alive[~inside]  # the trap is closed: an entered half stays in
            if len(alive) == 0:
                break
        active = (width + t) // 64 + 2  # the half reaches column width + t + 1 at most
        rows[:, :active] = step_rows(rows[:, :active], int("001"[int(drive)]))
    return first  # (n, k)


def coin_entries(halves: list[int], phase: int, steps: int, width: int, keys: np.ndarray,
                 rng: np.random.Generator) -> np.ndarray:
    """`cut_entries` at one width with a fair coin in place of the cells beyond the window: columns 1 .. `width` start
    as each half's, column `width` + 1 is a fresh fair coin at every step, and the result is the first step before
    `steps` at which the window is that of a state of t001 whose label agrees with the drive's phase, or -1."""
    assert width <= 62
    mask, top = np.uint64((1 << width) - 1), np.uint64(width - 1)
    cut = np.unique(((keys >> np.uint64(2)) & mask) * np.uint64(4) + (keys & np.uint64(3)))  # (c,)
    window = np.array(halves, dtype=np.uint64) & mask  # (m,)
    first = np.full(len(halves), -1, dtype=np.int64)  # (n,)
    alive = np.arange(len(halves))  # (m,), the halves still outside, window i being half alive[i]
    for t in tqdm(range(steps), desc=f"coin at {width} phase {phase}", file=sys.stderr, leave=False, mininterval=5):
        drive = (t + phase) % 3
        key = window * np.uint64(4) + np.uint64(drive)  # (m,)
        hit = cut[np.minimum(np.searchsorted(cut, key), len(cut) - 1)] == key  # (m,)
        if hit.any():
            first[alive[hit]] = t
            window, alive = window[~hit], alive[~hit]
            if len(alive) == 0:
                break
        beyond = rng.integers(0, 2, size=len(window), dtype=np.uint64)  # (m,), column width + 1
        left = ((window << np.uint64(1)) | np.uint64(int("001"[drive]))) & mask  # (m,), each cell's left neighbor
        window = left ^ (window | (window >> np.uint64(1)) | (beyond << top))
    return first  # (n,)


CUT_WIDTHS = (12, 16, 20, 24, 28, 30, 32, 34, 36, 40, 47)


def cut_profile(cells: int, steps: int, widths: tuple[int, ...] = CUT_WIDTHS, replicas: int = 50,
                seed: int = 30) -> list[tuple[int, int, float, float, int, float, float]]:
    """For every right half of at most `cells` cells, driven by 001 from each phase: when it first enters t001 cut to w
    cells in Rule 30 itself (`cut_entries`) and with a fair coin in column w + 1 (`coin_entries`, `replicas` runs of each
    half and phase), as (w, entered, mean, median, coin entered, coin mean, coin median) for each w of `widths`, the
    means and medians over the runs that entered within `steps` steps."""
    keys, halves = trap_keys(), list(range(1 << cells))
    rng = np.random.default_rng(seed)
    own = np.concatenate([cut_entries(halves, phase, steps, widths, keys) for phase in range(3)])  # (3 n, k)
    out = []
    for j, width in enumerate(widths):
        coin = np.concatenate([coin_entries([h for h in halves for _ in range(replicas)], phase, steps, width, keys,
                                            rng) for phase in range(3)])  # (3 n replicas,)
        done, coin_done = own[own[:, j] >= 0, j], coin[coin >= 0]  # (a,), (b,)
        out.append((width, len(done), float(done.mean()), float(np.median(done)), len(coin_done),
                    float(coin_done.mean()), float(np.median(coin_done))))
    return out


def beyond_stats(halves: list[int], phase: int, steps: int, width: int, context: int,
                 keys: np.ndarray) -> np.ndarray:
    """Over the steps before each right half, driven by 001 from `phase`, enters t001: how often cell `width` + 1 is
    white and black, by the phase of the drive and the last `context` cells of the window of `width` cells, as counts
    out[phase, cells, value], the cells read as bits, cell `width` highest."""
    assert context <= width <= 62
    wide = max([1] + [half.bit_length() for half in halves])
    rows = np.zeros((len(halves), (wide + steps) // 64 + 2), dtype=np.uint64)  # (n, words)
    for i, half in enumerate(halves):
        for j in range(0, wide, 64):
            rows[i, j // 64] = np.uint64((half >> j) & ((1 << 64) - 1))
    counts = np.zeros(3 * (2 << context), dtype=np.int64)  # (3 * 2^(context + 1),)
    mask, near = np.uint64((1 << TRAP_WIDTH) - 1), np.uint64((1 << context) - 1)
    for t in tqdm(range(steps), desc=f"cell beyond, phase {phase}", file=sys.stderr, leave=False, mininterval=5):
        drive = (t + phase) % 3
        hit = np.isin((rows[:, 0] & mask) * np.uint64(4) + np.uint64(drive), keys)  # (m,)
        rows = rows[~hit]  # entered halves stay in the trap and are counted no more
        if len(rows) == 0:
            break
        first = rows[:, 0]  # (m,)
        cells = (first >> np.uint64(width - context)) & near  # (m,)
        beyond = (first >> np.uint64(width)) & np.uint64(1)  # (m,)
        counts += np.bincount((drive * (2 << context) + cells * np.uint64(2) + beyond).astype(np.int64),
                              minlength=counts.size)
        active = (wide + t) // 64 + 2  # the half reaches column wide + t + 1 at most
        rows[:, :active] = step_rows(rows[:, :active], int("001"[drive]))
    return counts.reshape(3, 1 << context, 2)  # (3, 2^context, 2)


def conditioned_coin(width: int, contexts: tuple[int, ...], cells: int = 8, steps: int = 50000) -> list[
        tuple[int, float]]:
    """The coin beyond the window of `width` cells conditioned on the phase and the last k cells of the window, for each
    k of `contexts`: the chance of black taken from every right half of at most `cells` cells, driven by 001 from each
    phase for up to `steps` steps before it enters t001 (`beyond_stats`, with a count of one half added to each side),
    and the factor per step by which the chance of staying out of t001 cut to `width` cells falls under it
    (`coin_lock.biased_rate`): (k, factor) for each k."""
    from computations import coin_lock, lock_chain
    context = max(contexts)
    keys = trap_keys()
    counts = sum(beyond_stats(list(range(1 << cells)), phase, steps, width, context, keys)
                 for phase in range(3))  # (3, 2^context, 2)
    member = np.zeros((3, 1 << width), dtype=bool)  # (3, 2^width)
    for strip, label in lock_chain.t001_states():
        member[label % 3, strip & ((1 << width) - 1)] = True
    windows = np.arange(1 << width)  # (2^width,)
    out = []
    for k in contexts:
        merged = counts.reshape(3, 1 << k, 1 << (context - k), 2).sum(axis=2)  # (3, 2^k, 2), the last k cells
        black = (merged[..., 1] + 0.5) / (merged.sum(axis=-1) + 1.0)  # (3, 2^k)
        prob = black[:, windows >> (width - k)]  # (3, 2^width)
        out.append((k, coin_lock.biased_rate("001", member, prob, limit=60000)))
    return out


def constant_rate(done: np.ndarray, start: int = 1260, at: int = 100000) -> tuple[float, float]:
    """Compare entry steps `done` (shape (n,)) with entry at a constant rate per step after `start`: the ratio of the
    mean excess over `start` to the median excess, 1 / ln 2 for exponential entry, and the fraction a constant rate
    fitted to the mean leaves outside at step `at`."""
    excess = done.astype(np.float64) - start  # (n,)
    return float(excess.mean() / np.median(excess)), float(np.exp(-(at - start) / excess.mean()))


def periodic_extent(half: int, phase: int, steps: int, times: list[int], width: int = 128) -> list[int]:
    """At each of `times`, how many columns from column 1 have repeated with the trap's period 21 over the last 105
    steps, for the right half driven by 001 from `phase`."""
    rows = np.zeros((1, (half.bit_length() + steps) // 64 + 2), dtype=np.uint64)  # (1, words)
    for j in range(0, max(1, half.bit_length()), 64):
        rows[0, j // 64] = np.uint64((half >> j) & ((1 << 64) - 1))
    window = np.zeros((106, width), dtype=np.uint8)  # (106, width), the last 106 rows of columns 1 .. width
    wanted, extents = set(times), {}
    for t in range(max(times) + 1):
        bits = np.unpackbits(rows[0, :width // 64].view(np.uint8), bitorder="little")  # (width,)
        window = np.roll(window, -1, axis=0)
        window[-1] = bits
        if t in wanted:
            same = np.all(window[-1 - 21 * np.arange(1, 6)] == window[-1], axis=0)  # (width,)
            extents[t] = int(np.argmin(same)) if not same.all() else width
        active = (half.bit_length() + t) // 64 + 2
        rows[:, :active] = step_rows(rows[:, :active], int("001"[(t + phase) % 3]))
    return [extents[t] for t in times]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--cells", type=int, default=12, help="every right half of at most this many cells")
    parser.add_argument("--steps", type=int, default=6000)
    parser.add_argument("--long", type=int, default=0, help="instead, the white half and 11 random halves this long")
    parser.add_argument("--follow", nargs="*", default=[], help="instead, HALF:PHASE pairs under 001, run --steps steps")
    parser.add_argument("--trap", action="store_true", help="instead, the step at which each half enters t001")
    parser.add_argument("--conditioned-coin", type=int, default=0,
                        help="instead, the coin beyond a window of this many cells, conditioned on its last cells")
    parser.add_argument("--cut-profile", action="store_true",
                        help="instead, entry into t001 cut to each of CUT_WIDTHS cells, in Rule 30 and with a fair coin")
    args = parser.parse_args()

    started = time.perf_counter()
    if args.cut_profile:
        runs = 3 << args.cells
        print(f"t001 cut to w cells, every half of at most {args.cells} cells in each phase ({runs} runs; the coin "
              f"{50 * runs} runs), first entry within {args.steps} steps:")
        for w, done, mean, median, coin_done, coin_mean, coin_median in cut_profile(args.cells, args.steps):
            print(f"  w = {w}: Rule 30 {done} entered, mean {mean:,.0f}, median {median:,.0f}; "
                  f"coin {coin_done} entered, mean {coin_mean:,.0f}, median {coin_median:,.0f}")
        print(f"({time.perf_counter() - started:.0f} s)")
        return
    if args.conditioned_coin:
        for k, factor in conditioned_coin(args.conditioned_coin, (0, 2, 4, 8, 12), args.cells, args.steps):
            print(f"t001 at {args.conditioned_coin} cells, the coin conditioned on the last {k} cells: the chance of "
                  f"staying out falls by {factor:.6f} per step, entry at {1 - factor:.2e} per step")
        return
    if args.trap:
        keys = trap_keys()
        for phase in range(3):
            entry = trap_entries(list(range(1 << args.cells)), phase, args.steps, keys)
            done = entry[entry >= 0]
            times, counts = np.unique(done, return_counts=True)
            print(f"001 phase {phase}: {len(done)} of {1 << args.cells} halves enter t001 within {args.steps} steps"
                  + (f", the latest at step {done.max()}" if len(done) else "")
                  + (f"; not entered: {np.flatnonzero(entry < 0).tolist()}" if len(done) < len(entry) else ""))
            print("  by step " + ", ".join(f"{bound:,}: {int((done <= bound).sum())}" for bound in (1300, 10000, 50000, 100000))
                  + (f"; median {int(np.median(done)):,}, mean {int(done.mean()):,}" if len(done) else ""))
            if len(done) == len(entry):
                ratio, left = constant_rate(done)
                print(f"  constant rate after step 1,260: mean excess / median excess {ratio:.2f} (1 / ln 2 = 1.44); "
                      f"out at step 100,000: {100 * left:.1f}% fitted, {100 * (done > 100000).mean():.1f}% observed")
            print("  entry steps (count): " + ", ".join(f"{t} ({c})" for t, c in zip(times.tolist(), counts.tolist())))
        print(f"({time.perf_counter() - started:.0f} s)")
        return
    if args.follow:
        for pair in args.follow:
            half, phase = (int(x) for x in pair.split(":"))
            print(f"001 half {half} phase {phase}: column 1 at the white times repeats with period 14 samples from step "
                  f"{settled_from('001', half, phase, args.steps, 14)} to step {args.steps}")
        return
    if args.long:
        rng = np.random.default_rng(40)
        halves = [0] + [int(h) for h in rng.integers(1, 1 << 24, 11)]
        steps = args.long
    else:
        halves = list(range(1 << args.cells))
        steps = args.steps
    for word in WORDS:
        for phase in range(3):
            rows, periods = report(word, halves, phase, steps)
            settled = periods[periods > 0]
            found = sorted(set(settled.tolist()))
            print(f"{word} phase {phase}: column 1 at white times settles for {len(settled)} of {len(halves)} halves"
                  + (f", with periods {found[:6]} samples" if found else ""))
            for drive, (black, white, mean) in enumerate(rows):
                print(f"  drive phase {drive} (center {word[drive]}): constant black {black:.3f}, constant white "
                      f"{white:.3f}, mean {mean:.3f}")
    print(f"({time.perf_counter() - started:.0f} s)")


if __name__ == "__main__":
    main()
