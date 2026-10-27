"""The single cell's left diagonals: where they are all white, and where their eventual periods grow.

Diagonal j is t -> cell(t, j - t), j cells in from the left edge (the kit's `Rule30Diagonals.D j`). The run evolves the
single cell for `steps` steps as a Python integer and keeps every diagonal below `depth` over the last `window` steps.
Each diagonal settles after about 1.35 j steps, so `steps` must exceed that for every depth read.

    python -m computations.left_diagonals 140000 100000   # the white diagonals and period records below 10^5
"""

from __future__ import annotations

import argparse
import sys
import numpy as np

from dataclasses import dataclass
from tqdm.auto import tqdm

from computations.rule30 import step


@dataclass(frozen=True, slots=True)
class WhiteDiagonal:
    """An eventually white diagonal and what it does to the diagonal two below it."""

    depth: int
    previous_period: int  # eventual period of diagonal depth - 1
    previous_weight: int  # its black cells per period
    next_period: int  # eventual period of diagonal depth + 1


def diagonals(steps: int, depth: int, window: int) -> np.ndarray:
    """Diagonals 0 .. depth - 1 at the last `window` of `steps` steps; row j holds diagonal j."""
    width = 2 * steps + 3
    row = 1 << steps  # bit i is cell i - steps
    D = np.zeros((depth, window), dtype=np.uint8)  # (depth, window)
    for t in tqdm(range(steps), desc="evolve", unit="step", file=sys.stderr, mininterval=5):
        if t >= steps - window:
            raw = np.frombuffer(row.to_bytes((width + 7) // 8, "little"), dtype=np.uint8)  # (width / 8,)
            cells = np.unpackbits(raw, bitorder="little")  # (8 ceil(width / 8),)
            D[:, t - (steps - window)] = cells[steps - t:steps - t + depth]  # cells -t .. -t + depth - 1
        row = step(row)
    return D  # (depth, window)


def eventual_period(diagonal: np.ndarray) -> int:
    """The least power of two with which the diagonal repeats over the window."""
    # diagonal: (window,)
    p = 1
    while not np.array_equal(diagonal[p:], diagonal[:-p]):
        p *= 2
        assert p < len(diagonal) // 2, "the window is too short for this period"
    return p


def survey(D: np.ndarray) -> tuple[list[WhiteDiagonal], dict[int, int]]:
    """The eventually white diagonals, and each depth whose eventual period exceeds every shallower one's."""
    # D: (depth, window)
    white, records, longest = [], {}, 0
    for j in range(1, len(D) - 1):
        if not D[j].any():
            previous = eventual_period(D[j - 1])
            weight = int(D[j - 1, :previous].sum())
            white.append(WhiteDiagonal(j, previous, weight, eventual_period(D[j + 1])))
            continue
        period = eventual_period(D[j])
        if period > longest:
            records[j], longest = period, period
    return white, records


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("steps", type=int)
    parser.add_argument("depth", type=int)
    parser.add_argument("--window", type=int, default=128, help="steps read at the end of the run")
    args = parser.parse_args()

    white, records = survey(diagonals(args.steps, args.depth, args.window))
    for diagonal in white:
        print(f"depth {diagonal.depth}: all white; depth {diagonal.depth - 1} has period {diagonal.previous_period} "
              f"and weight {diagonal.previous_weight}; depth {diagonal.depth + 1} has period {diagonal.next_period}")
    for j, period in records.items():
        print(f"depth {j}: period {period}, a record")


if __name__ == "__main__":
    main()
