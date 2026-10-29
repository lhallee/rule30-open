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
    args = parser.parse_args()

    started = time.perf_counter()
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
