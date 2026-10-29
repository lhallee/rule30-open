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
"""

from __future__ import annotations

import argparse
import sys
import time
import numpy as np

from tqdm.auto import tqdm

from computations.absorption import step_rows


WORDS = ("001", "011")


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
        rows = step_rows(rows, int(word[(t + phase) % 3]))
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


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--cells", type=int, default=12, help="every right half of at most this many cells")
    parser.add_argument("--steps", type=int, default=6000)
    parser.add_argument("--long", type=int, default=0, help="instead, the white half and 11 random halves this long")
    parser.add_argument("--follow", nargs="*", default=[], help="instead, HALF:PHASE pairs under 001, run --steps steps")
    args = parser.parse_args()

    started = time.perf_counter()
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
