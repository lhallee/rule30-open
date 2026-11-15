"""Tests of computations.sensitivity: arrival times of single flips at the center against their known values."""

from __future__ import annotations

import numpy as np

from computations import sensitivity


def test_sensitivity() -> None:
    """A flip at -d reaches the center at exactly t = d; flips at +1 and +2 never do; from the right the median
    arrival over d = 3 .. 256 is about 2.5 d."""
    assert all(sensitivity.arrival(-d, 200) == d for d in range(1, 65))
    assert sensitivity.arrival(1, 3000) is None and sensitivity.arrival(2, 3000) is None
    ratios = np.array([sensitivity.arrival(d, 8 * d + 50) / d for d in range(3, 257)])  # (254,)
    assert ratios.min() >= 1 and 2.3 < float(np.median(ratios)) < 2.7
