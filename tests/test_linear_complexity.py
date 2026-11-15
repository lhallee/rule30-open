"""Tests of computations.linear_complexity: Berlekamp-Massey against LFSRs of known order and the center column."""

from __future__ import annotations

import numpy as np

from computations import linear_complexity
from computations.rule30 import center_column


def test_linear_complexity() -> None:
    """Berlekamp-Massey recovers an LFSR's order and a period's bound, and puts the center column at n / 2."""
    lfsr = [1, 0, 0, 1, 1]
    while len(lfsr) < 200:
        lfsr.append(lfsr[-3] ^ lfsr[-5])  # x^5 + x^2 + 1
    assert linear_complexity.complexity_profile(np.array(lfsr))[-1] == 5
    assert linear_complexity.complexity_profile(np.array([0, 0, 1, 1] * 50))[-1] == 3
    profile = linear_complexity.complexity_profile(center_column(4096))  # (4096,)
    assert np.abs(profile - np.arange(1, 4097) / 2).max() <= 12
