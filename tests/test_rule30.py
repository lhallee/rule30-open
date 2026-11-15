"""Tests of computations.rule30: the integer rows and step against direct evolution of a bool array, Wolfram's code 30
and OEIS A051023."""

from __future__ import annotations

import itertools
import numpy as np
import pytest

from computations.rule30 import center_column, pack_row, spacetime, step, unpack_row


def single_column(n: int) -> np.ndarray:
    """The center column by direct evolution of a bool array, independent of the integer rows."""
    cells = np.zeros(2 * n + 1, dtype=bool)  # (2n + 1,)
    cells[n] = True
    return spacetime(cells, n - 1)[:, n].astype(np.uint8)  # (n,)


def test_center_column() -> None:
    """The integer rows against direct evolution, and the first ten cells against OEIS A051023, as the Lean spot check
    states them."""
    assert np.array_equal(center_column(300), single_column(300))
    assert center_column(10).tolist() == [1, 1, 0, 1, 1, 1, 0, 0, 1, 1]


@pytest.mark.parametrize("k", range(6))
def test_seed_extensions(k: int) -> None:
    """The seeds (10)^k 1 and (10)^k 11 keep the center column and differ from the single cell's rows exactly where
    `sigma_difference` and `tau_difference` say."""
    steps, origin = 200, 220
    width = 2 * origin + 1
    for extra in (False, True):
        cells = np.zeros(width, dtype=bool)  # (width,), cell x at index origin + x
        cells[origin:origin + 2 * k + 1:2] = True
        if extra:
            cells[origin + 2 * k + 1] = True
        single = np.zeros(width, dtype=bool)  # (width,)
        single[origin] = True
        rows, reference = spacetime(cells, steps), spacetime(single, steps)  # (steps + 1, width) each
        assert np.array_equal(rows[:, origin], reference[:, origin])
        for t in range(steps + 1):
            offsets = {int(x) - origin - t for x in np.flatnonzero(rows[t] != reference[t])}
            if not extra:
                expected = set(range(2, 2 * k + 1, 2)) if t % 2 == 0 else (
                    {0, *range(1, 2 * k, 2), 2 * k} if k > 0 else set())
            else:
                expected = {*range(2, 2 * k + 1, 2), 2 * k + 1} if t % 2 == 0 else {0, *range(1, 2 * k + 2, 2)}
            assert offsets == expected, (k, extra, t)


def test_step_is_rule_30() -> None:
    """The integer step is Wolfram's code 30 on every neighborhood: neighborhood 4l + 2c + r maps to bit 4l + 2c + r
    of 30."""
    for neighborhood in range(8):
        left, center, right = neighborhood >> 2, (neighborhood >> 1) & 1, neighborhood & 1
        row = (left << 1) | (center << 2) | (right << 3)  # cells x - 1, x, x + 1 at bits 1, 2, 3
        assert (step(row) >> 2) & 1 == (30 >> neighborhood) & 1


def test_pack_and_unpack_rows() -> None:
    """`pack_row` against the sum of the set bits and `unpack_row` against the bits read one at a time, on every row of
    up to 10 cells and on random rows of up to 3,000, as 0/1 integers of several types and as booleans."""
    rng = np.random.default_rng(1)
    rows = [np.array(cells, dtype=np.uint8) for n in range(11) for cells in itertools.product((0, 1), repeat=n)]
    rows += [rng.integers(0, 2, int(n), dtype=np.uint8) for n in rng.integers(0, 3000, 100)]
    for cells in rows:  # cells: (n,)
        value = sum(1 << i for i, cell in enumerate(cells.tolist()) if cell)
        for dtype in (np.uint8, np.int64, bool):
            assert pack_row(cells.astype(dtype)) == value
        unpacked = unpack_row(value, cells.size)  # (n,)
        assert unpacked.dtype == np.uint8 and unpacked.tolist() == [(value >> i) & 1 for i in range(cells.size)]
    assert unpack_row(0b1011, 6).tolist() == [1, 1, 0, 1, 0, 0] and pack_row(np.zeros(0, dtype=np.uint8)) == 0
