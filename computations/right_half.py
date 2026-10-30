"""The cells right of a center column that repeats a word: does column 1 lock?

Drive a finite right half with the center reading `word` over and over, and read column 1 at the white times of the
word. If it repeats from some time on, with a period that is a multiple of the word's, for every finite right half,
masked Jen (the kit's `Rule30MaskedJen.masked_jen`) excludes the word as the center's eventual period. A right half is an integer whose
bit i is cell i + 1; the center is the left neighbor of bit 0.

    python -m computations.right_half 12000 30 --max-period 7   # which primitive words lock column 1
    python -m computations.right_half 12000 30 --min-period 8 --max-period 12   # about 5 min
    python -m computations.right_half 200000 30 --follow 01111:10   # the locks of 01111 break, about 1 min

Primitive words that lock for all 31 starts, by period: 2: 0 of 1, 3: 0 of 2, 4: 3 of 3, 5: 0 of 6, 6: 0 of 9,
7: 0 of 18, 8: 8 of 30, 9: 0 of 56, 10: 17 of 99, 11: 35 of 186, 12: 46 of 335.
"""

from __future__ import annotations

import argparse
import sys
import numpy as np

from tqdm.auto import tqdm

from computations.game import necklaces


def column_one(word: str, start: int, steps: int) -> np.ndarray:
    """Column 1 at times 0 .. steps - 1 of the right half `start` driven by the center repeating `word`."""
    centers = [int(bit) for bit in word]
    row = start
    column = np.zeros(steps, dtype=np.uint8)  # (steps,)
    for t in range(steps):
        column[t] = row & 1
        row = ((row << 1) | centers[t % len(centers)]) ^ (row | (row >> 1))
    return column  # (steps,)


def locked_period(word: str, start: int, steps: int, max_multiple: int = 400) -> int | None:
    """The least multiple of the word's length with which column 1, read at the word's white times, repeats over the
    second half of the run, or None. Masked Jen needs only some common period of the center and that column."""
    p = len(word)
    column = column_one(word, start, steps)  # (steps,)
    white = np.array([word[t % p] == "0" for t in range(steps)])  # (steps,)
    half = steps // 2
    for multiple in range(1, max_multiple + 1):
        shift = multiple * p
        now, later = column[half:steps - shift], column[half + shift:]  # (steps - half - shift,) each
        mask = white[half:steps - shift]  # (steps - half - shift,)
        if np.array_equal(now[mask], later[mask]):
            return shift
    return None


def lock_breaks(word: str, start: int, steps: int, shift: int, after: int) -> tuple[int, int, int | None]:
    """For the right half `start` driven by `word`: the last time at which column 1, at a white time of the word,
    differs from its value `shift` steps later (-1 if never), how many such times come after `after`, and the first of
    them. A lock that holds stays without such times."""
    p = len(word)
    column = column_one(word, start, steps)  # (steps,)
    white = np.array([word[t % p] == "0" for t in range(steps - shift)])  # (steps - shift,)
    breaks = np.flatnonzero((column[:-shift] != column[shift:]) & white)  # (b,)
    late = breaks[breaks > after]  # (c,)
    return (int(breaks[-1]) if breaks.size else -1), int(late.size), (int(late[0]) if late.size else None)


def random_starts(count: int, width: int) -> list[int]:
    """The empty right half, then `count` random right halves of `width` cells from `numpy.random.default_rng(30)`."""
    rng = np.random.default_rng(30)
    return [0] + [sum(int(bit) << i for i, bit in enumerate(rng.integers(0, 2, width))) for _ in range(count)]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("steps", type=int)
    parser.add_argument("random_starts", type=int)
    parser.add_argument("--width", type=int, default=64, help="cells of each random right half")
    parser.add_argument("--min-period", type=int, default=2)
    parser.add_argument("--max-period", type=int, default=5)
    parser.add_argument("--follow", help="instead follow WORD:SHIFT over `steps` from the starts that lock in 12,000")
    args = parser.parse_args()

    starts = random_starts(args.random_starts, args.width)
    if args.follow:
        word, shift = args.follow.split(":")
        for k, start in enumerate(starts):
            if locked_period(word, start, 12000) is None:
                continue
            last, count, first = lock_breaks(word, start, args.steps, int(shift), 6000)
            print(f"start {k}: last break of period {shift} at {last}; {count} breaks after step 6,000"
                  + (f", the first at {first}" if first is not None else ""))
        return
    for period in range(args.min_period, args.max_period + 1):
        words = necklaces(period)
        always = 0
        for word in tqdm(words, desc=f"words of period {period}", file=sys.stderr):
            periods = [locked_period(word, start, args.steps) for start in starts]
            found = sorted({period for period in periods if period is not None})
            locked = sum(period is not None for period in periods)
            always += locked == len(starts)
            print(f"{word:>12}: column 1 locks for {locked} of {len(starts)} starts"
                  + (f", periods {found}" if found else ""))
        print(f"period {period}: {always} of {len(words)} primitive words lock for every start")


if __name__ == "__main__":
    main()
