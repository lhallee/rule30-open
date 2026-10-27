"""The cells right of a center column that repeats a word: does column 1 lock?

Drive a finite right half with the center reading `word` over and over, and read column 1 at the white times of the
word. If it repeats from some time on, with a period that is a multiple of the word's, for every finite right half,
masked Jen (the kit's `Rule30MaskedJen.masked_jen`) excludes the word as the center's eventual period. A right half is an integer whose
bit i is cell i + 1; the center is the left neighbor of bit 0.

    python -m computations.right_half 12000 30 --max-period 7   # which primitive words lock column 1
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


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("steps", type=int)
    parser.add_argument("random_starts", type=int)
    parser.add_argument("--width", type=int, default=64, help="cells of each random right half")
    parser.add_argument("--max-period", type=int, default=5)
    args = parser.parse_args()

    rng = np.random.default_rng(30)
    starts = [0] + [sum(int(bit) << i for i, bit in enumerate(rng.integers(0, 2, args.width)))
                    for _ in range(args.random_starts)]
    words = [word for period in range(2, args.max_period + 1) for word in necklaces(period)]
    for word in tqdm(words, desc="words", file=sys.stderr):
        periods = [locked_period(word, start, args.steps) for start in starts]
        found = sorted({period for period in periods if period is not None})
        locked = sum(period is not None for period in periods)
        print(f"{word:>8}: column 1 locks for {locked} of {len(starts)} starts" + (f", periods {found}" if found else ""))


if __name__ == "__main__":
    main()
