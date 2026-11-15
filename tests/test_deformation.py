"""Tests of computations.deformation: the deformed center cell against Rule 30 and Rule 150 run directly."""

from __future__ import annotations

import numpy as np

from computations import deformation
from computations.rule30 import center_column


def test_deformation() -> None:
    """The deformed center cell's T-degrees and term counts for t <= 12; at T = 1 it is Rule 30's center column and at
    T = 0 Rule 150's whole row."""
    table = deformation.center_degrees(12)
    assert [degree for degree, _ in table] == [0, 1, 0, 3, 6, 10, 16, 27, 44, 70, 114, 190]
    assert [terms for _, terms in table] == [1, 2, 1, 3, 5, 6, 10, 15, 21, 38, 54, 102]
    rows = deformation.deformed_rows(16)
    assert [rows[t].get(0, 0).bit_count() & 1 for t in range(17)] == center_column(17).tolist()
    cells = np.zeros(35, dtype=bool)  # (35,), cell x at index x + 17
    cells[17] = True
    for t in range(17):
        assert [int(x) - 17 for x in np.flatnonzero(cells)] == sorted(x for x, cell in rows[t].items() if cell & 1)
        cells = np.concatenate([[False], cells[:-1]]) ^ cells ^ np.concatenate([cells[1:], [False]])  # (35,), Rule 150
