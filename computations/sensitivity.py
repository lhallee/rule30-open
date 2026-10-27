"""How fast one flipped cell of the initial row reaches the center column, from each side.

The single cell's row with cell `offset` also flipped evolves next to the unflipped one; the arrival is the first time
their center columns differ. From the left the difference moves right exactly one cell per step, so a flip at -d
arrives at t = d. From the right it passes only through the OR, and the flips at +1 and +2 never arrive (the seeds 11
and 101 keep the center column; Lean: `center_column`, `center_sigma`).

    python -m computations.sensitivity 256 4096   # arrival times for d = 1 .. 256 on both sides
"""

from __future__ import annotations

import argparse
import sys

from tqdm.auto import tqdm

from computations.rule30 import step


def arrival(offset: int, steps: int) -> int | None:
    """The first time before `steps` at which the center column differs between the single cell and the single cell
    with cell `offset` flipped, or None."""
    origin = steps + abs(offset) + 1  # bit of cell 0; the left edge stays at bit 1 or above
    row, flipped = 1 << origin, (1 << origin) ^ (1 << (origin + offset))
    for t in range(steps):
        if ((row ^ flipped) >> origin) & 1:
            return t
        row, flipped = step(row), step(flipped)
    return None


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("max_distance", type=int)
    parser.add_argument("steps", type=int)
    args = parser.parse_args()

    for d in tqdm(range(1, args.max_distance + 1), desc="distances", file=sys.stderr, mininterval=5):
        left, right = arrival(-d, args.steps), arrival(d, args.steps)
        ratio = f"{right / d:.2f} d" if right is not None else "none"
        print(f"d = {d}: from the left at t = {left}, from the right at t = {right} ({ratio})")


if __name__ == "__main__":
    main()
