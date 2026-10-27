"""Rule 30 rows as Python integers, and the single black cell's center column.

A row is the integer whose bit i is cell `origin + i`, so cell x - 1 is the bit below cell x and one step of the rule,
x' = x_(-1) xor (x or x_(+1)), is `(row << 1) ^ (row | (row >> 1))`. Bits below 0 read as white, which is exact while
the row's leftmost 1 stays at bit 1 or above.
"""

from __future__ import annotations

import numpy as np


def step(row: int) -> int:
    """One step of Rule 30 on a row held as an integer."""
    return (row << 1) ^ (row | (row >> 1))


def center_column(n: int) -> np.ndarray:
    """The first `n` cells of the single black cell's center column (OEIS A051023)."""
    row = 1 << n  # the black cell at bit n leaves room for n steps of the left edge
    column = np.zeros(n, dtype=np.uint8)  # (n,)
    for t in range(n):
        column[t] = (row >> n) & 1
        row = step(row)
    return column  # (n,)


def spacetime(cells: np.ndarray, steps: int) -> np.ndarray:
    """Rows 0 .. steps of Rule 30 from the row `cells`, white beyond its ends; each row loses one exact cell at each end
    per step, so row t is exact on cells t .. n - 1 - t."""
    # cells: (n,)
    rows = [cells.astype(bool)]  # each (n,)
    for _ in range(steps):
        row = rows[-1]  # (n,)
        left = np.concatenate([[False], row[:-1]])  # (n,), cell x - 1
        right = np.concatenate([row[1:], [False]])  # (n,), cell x + 1
        rows.append(left ^ (row | right))
    return np.stack(rows)  # (steps + 1, n)
