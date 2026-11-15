"""Tests of computations.small_halves: the certificates of `TenCells` against integer rows stepped one at a time and
checked column by column."""

from __future__ import annotations

import numpy as np

from computations import absorption, small_halves
from references import least_depth_slow


def test_small_halves() -> None:
    """The certificates of `TenCells`: packing round-trips, and for sampled halves of up to seven cells each entry is the
    first step at which integer rows stepped one at a time meet the family, at the least depth there, checked column
    by column."""
    rng = np.random.default_rng(43)
    entries = [(int(t), int(k)) for t, k in zip(rng.integers(0, 2000, 40), rng.integers(0, 64, 40), strict=True)]
    assert small_halves.decode(small_halves.encode(entries), 40) == entries
    wall = absorption.kit_wall()  # (4, 2^13)
    for word, phase in (("0001", 2), ("0011", 1), ("0111", 3)):
        certs = small_halves.certificates(word, 7, phase)
        assert len(certs) == 128
        for half in rng.choice(128, size=12, replace=False).tolist():
            t, k = certs[half]
            row = half
            for s in range(t):
                assert least_depth_slow(word, row, (s + phase) % 4, wall) < 0
                row = ((row << 1) | int(word[(s + phase) % 4])) ^ (row | (row >> 1))
            assert least_depth_slow(word, row, (t + phase) % 4, wall) == k
