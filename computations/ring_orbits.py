"""Periodic orbits of Rule 30 on rings, as witnesses that the finite game fails for a block at every width.

On a ring of M cells every column of a periodic orbit repeats. Lift the orbit to the line: it is a row whose columns
all repeat, so for any column k that repeats a block b, the cells right of k play the finite game of `game.py` for b
along a closed walk, at every width. If column k - 1 does not repeat with the period of b, the walk shows the column
left of the repeating one taking both values at one phase inside one strongly connected component that holds a play,
so the game does not exclude b at any width. Jen's theorem does not apply, since the lifted row has no leftmost 1.

`orbits` finds every periodic orbit on M cells, up to rotation, by iterating the step map past every transient;
`witnessed` lists the blocks of period at most `max_block` that some column of such an orbit repeats while its left
neighbor breaks the period.

    python -m computations.ring_orbits --max-cells 20 --max-block 16   # about 10 s
"""

from __future__ import annotations

import argparse
import sys

import numpy as np
from tqdm.auto import tqdm

from computations.game import least_rotation


def ring_step(states: np.ndarray, cells: int) -> np.ndarray:
    """One step of Rule 30 on a ring of `cells` cells, bit x the cell x, its left neighbor at x - 1."""
    # states: (n,)
    full = (1 << cells) - 1
    left = ((states << 1) | (states >> (cells - 1))) & full  # (n,), bit x holds cell x - 1
    right = ((states >> 1) | (states << (cells - 1))) & full  # (n,), bit x holds cell x + 1
    return left ^ (states | right)  # (n,)


def orbits(cells: int) -> list[np.ndarray]:
    """One representative orbit per rotation class of the periodic orbits on the ring, each as its states in order."""
    size = 1 << cells
    step = ring_step(np.arange(size, dtype=np.int64), cells)  # (2^M,)
    power = step.copy()  # (2^M,), the step map applied 2^j times
    for _ in range(cells + 1):
        power = power[power]  # 2^(M + 1) steps exceed every transient
    seen = np.zeros(size, dtype=bool)  # (2^M,)
    found = []
    for state in np.unique(power).tolist():
        if seen[state]:
            continue
        orbit = [state]
        while (state := int(step[state])) != orbit[0]:
            orbit.append(state)
        states = np.array(orbit, dtype=np.int64)  # (L,)
        for r in range(cells):
            seen[((states << r) | (states >> (cells - r))) & (size - 1)] = True
        found.append(states)
    return found


def least_period(column: np.ndarray) -> int:
    """The least period of a cyclic sequence."""
    # column: (L,)
    return next(p for p in range(1, column.size + 1) if column.size % p == 0 and
                np.array_equal(column, np.roll(column, p)))


def witnessed(max_cells: int, max_block: int) -> tuple[dict[str, int], list[int]]:
    """The blocks of period at most `max_block` that a column of a periodic orbit on at most `max_cells` cells repeats
    while the column left of it breaks that period, each with the least ring that shows it, and the number of orbits
    up to rotation on each ring from 1 cell."""
    found: dict[str, int] = {}
    counts = []
    for cells in tqdm(range(1, max_cells + 1), desc="rings", file=sys.stderr, mininterval=5):
        reps = orbits(cells)
        counts.append(len(reps))
        for states in reps:
            columns = (states[:, None] >> np.arange(cells)[None, :]) & 1  # (L, M), column x at index x
            for x in range(cells):
                period = least_period(columns[:, x])
                left = columns[:, (x - 1) % cells]  # (L,)
                if period <= max_block and not np.array_equal(left, np.roll(left, period)):
                    block = least_rotation("".join(str(int(v)) for v in columns[:period, x]))
                    found.setdefault(block, cells)
    return found, counts


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-cells", type=int, default=20)
    parser.add_argument("--max-block", type=int, default=16)
    args = parser.parse_args()
    found, counts = witnessed(args.max_cells, args.max_block)
    print(f"periodic orbits up to rotation on rings of 1 to {args.max_cells} cells: {counts} ({sum(counts)} in all)")
    print(f"blocks of period at most {args.max_block} witnessed: "
          + ", ".join(f"{block} (ring of {cells})" for block, cells in sorted(found.items())))


if __name__ == "__main__":
    main()
