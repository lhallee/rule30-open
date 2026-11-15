"""Tests of computations.left_diagonals: the white diagonals and period records against Wolfram's notes."""

from __future__ import annotations

from computations import left_diagonals


def test_left_diagonals() -> None:
    """The white diagonals and period records below depth 700 after 1,200 steps: depths 2, 7, 28 and 399, and records
    at 3, 8, 29 and 400, as Wolfram's notes give them."""
    white, records = left_diagonals.survey(left_diagonals.diagonals(1200, 700, 128))
    assert [(d.depth, d.previous_period, d.previous_weight, d.next_period) for d in white] == [
        (2, 1, 1, 2), (7, 2, 1, 4), (28, 4, 3, 8), (399, 8, 3, 16)]
    assert records == {1: 1, 3: 2, 8: 4, 29: 8, 400: 16}
