"""Tests of computations.slow_halves: the beam search against the exhaustive census of `absorption`."""

from __future__ import annotations

from computations import absorption, slow_halves


def test_slow_halves() -> None:
    """With a beam as wide as the number of halves, the beam search is exhaustive and matches the census of up to 10
    cells under 0001; with the finding's beam it matches the census at its starting length, 12 cells, under 0111, as the
    slow-half finding quotes (416; the latest entries 544 and 980 under 0001 and 0011 are its reproduce command)."""
    wall = absorption.kit_wall()  # (4, 2^13)
    census = absorption.census("0001", 10, 0, 4000, wall)  # (2^10,)
    best = slow_halves.beam_search("0001", 1 << 10, 6, 10, 4000, wall)
    assert best[10][0] == int(census.max())
    half = best[10][1]  # (10,)
    assert slow_halves.entry_times("0001", half[None, :], 4000, wall)[0] == best[10][0]
    assert slow_halves.beam_search("0111", 512, 12, 12, 4000, wall)[12][0] == 416
