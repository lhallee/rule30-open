"""Tests of computations.algebra: the center cell's algebraic normal form against its truth table and the Rule 150
kernel."""

from __future__ import annotations

import numpy as np

from computations import algebra
from computations.rule30 import center_column


def test_degree() -> None:
    """The center cell at time t has degree 2t - 1, with the single top monomial over cells -t + 2 .. t for t >= 3, and
    the monomial counts the structure finding quotes; the Moebius transform inverts back to the truth table."""
    counts = {3: 30, 4: 122, 5: 346, 6: 1360, 7: 4852, 8: 23094}
    for t in range(2, 9):
        anf = algebra.center_anf(t)  # (2^(2t + 1),)
        degree, top = algebra.degree_and_top(anf)
        assert degree == 2 * t - 1
        if t >= 3:
            assert top == [sum(1 << (x + t) for x in range(-t + 2, t + 1))]
            assert int(anf.sum()) == counts[t]
    table = algebra.center_truth_table(3)  # (128,)
    assert np.array_equal(algebra.moebius(algebra.moebius(table)), table)


def test_duhamel() -> None:
    """The center column as 1 plus the Rule 150 kernel applied to the earlier adjacent black pairs."""
    assert np.array_equal(algebra.duhamel_center(96), center_column(96))
