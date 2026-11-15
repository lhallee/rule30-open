"""Tests of computations.periodic_columns: the bit-sliced search against direct evolution under Rules 30, 90 and
150."""

from __future__ import annotations

import numpy as np

from computations import periodic_columns
from computations.rule30 import spacetime


def test_periodic_columns() -> None:
    """The bit-sliced search against direct evolution: under Rule 150 the single cell's center column survives with
    period 1 and under Rule 90 the row 101 keeps column 1 white; under Rule 30 no triple survives for 12 cells, and the
    nearest miss at 8 cells, simulated as a bool array, repeats exactly 15 times with its period and then fails."""
    found, _, _ = periodic_columns.search(8, 32, 256, 150)
    assert (1, 0, 1) in found
    found, _, _ = periodic_columns.search(8, 32, 256, 90)
    assert (0b101, 1, 1) in found
    found, longest, witness = periodic_columns.search(12, 32, 256, 30)
    assert found == [] and longest == 17
    found, longest, (row, column, period) = periodic_columns.search(8, 32, 256, 30)
    assert found == [] and longest == 15
    cells = np.zeros(8 + 2 * 300, dtype=bool)  # (608,), cell j of the row at index 300 + j
    cells[300:308] = [(row >> j) & 1 for j in range(8)]
    col = spacetime(cells, 299)[:, 300 + column]  # (300,)
    repeats = 0
    while col[period + repeats] == col[repeats]:
        repeats += 1
    assert repeats == longest
