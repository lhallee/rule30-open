"""Searching for right halves that enter the kit's ether-and-wall family late, against the exhaustive census.

Drive a finite right half with a center repeating a period-four word from phase 0, as in `absorption.py`, and record
the first step at which it is in the kit's family. The census there finds the latest entry among all right halves of a
given number of cells. This module asks whether a search finds slow halves of more cells: a beam search over prefixes
keeps the `beam` slowest halves of each length and extends each by one cell, white or black, so a half of n cells is
built from a slow half of n - 1 cells. Its result at small lengths is compared with the census.

    python -m computations.slow_halves 0001 0011 0111 --beam 512 --start 12 --stop 64 --steps 8000
"""

from __future__ import annotations

import argparse
import sys
import time
import numpy as np

from tqdm.auto import tqdm

from computations import absorption


def entry_times(word: str, halves: np.ndarray, steps: int, wall: np.ndarray, phase: int = 0) -> np.ndarray:
    """The first step before `steps` at which each right half enters the kit's family, or `steps` if none does; row i
    of `halves` holds the cells of half i, column j being column j + 1."""
    # halves: (m, n)
    bits = np.zeros((halves.shape[0], halves.shape[1] + steps + 70), dtype=np.uint8)  # (m, cells)
    bits[:, :halves.shape[1]] = halves
    times = absorption.absorb(word, absorption.packed(bits), phase, steps, wall, halves.shape[1])  # (m,)
    return np.where(times < 0, steps, times)  # (m,)


def beam_search(word: str, beam: int, start: int, stop: int, steps: int, wall: np.ndarray,
                phase: int = 0) -> dict[int, tuple[int, np.ndarray]]:
    """For each length n from `start` to `stop`, the latest entry found among halves of at most n cells and one half
    that attains it. All halves of `start` cells are tried; each later length extends the kept halves by one cell."""
    halves = ((np.arange(1 << start)[:, None] >> np.arange(start)[None, :]) & 1).astype(np.uint8)  # (2^start, start)
    times = entry_times(word, halves, steps, wall, phase)  # (2^start,)
    best: dict[int, tuple[int, np.ndarray]] = {}
    for n in tqdm(range(start, stop + 1), desc=f"beam, {word}", file=sys.stderr, leave=False):
        if n > start:
            black = np.concatenate([halves, np.ones((len(halves), 1), dtype=np.uint8)], axis=1)  # (k, n)
            white = np.concatenate([halves, np.zeros((len(halves), 1), dtype=np.uint8)], axis=1)  # (k, n)
            halves = np.concatenate([white, black])  # (2k, n)
            times = np.concatenate([times, entry_times(word, black, steps, wall, phase)])  # (2k,)
        order = np.argsort(-times, kind="stable")[:beam]  # (beam,)
        halves, times = halves[order], times[order]
        best[n] = (int(times[0]), halves[0].copy())
    return best


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("words", nargs="+")
    parser.add_argument("--beam", type=int, default=512)
    parser.add_argument("--start", type=int, default=12)
    parser.add_argument("--stop", type=int, default=64)
    parser.add_argument("--steps", type=int, default=8000)
    parser.add_argument("--census-cells", type=int, default=16, help="compare with the census of this many cells")
    args = parser.parse_args()

    started = time.perf_counter()
    wall = absorption.kit_wall()  # (4, 2^13)
    for word in args.words:
        census = absorption.census(word, args.census_cells, 0, 4000, wall)  # (2^cells,)
        best = beam_search(word, args.beam, args.start, args.stop, args.steps, wall)
        lengths = [n for n in best if n % 4 == 0 or n == args.stop]
        print(f"{word}, phase 0: census of up to {args.census_cells} cells, latest entry {int(census.max())}; beam "
              f"search, latest entry found by length: " + ", ".join(f"{n}: {best[n][0]}" for n in lengths))
        n = args.stop
        print(f"  slowest half found of up to {n} cells: {''.join(map(str, best[n][1]))}")
    print(f"({time.perf_counter() - started:.0f} s)")


if __name__ == "__main__":
    main()
