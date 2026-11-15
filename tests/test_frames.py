"""Tests of computations.frames: Phi and Psi against the center column and the periods the frames finding quotes."""

from __future__ import annotations

import numpy as np

from computations import frames
from computations.rule30 import center_column


def test_seed_past() -> None:
    """rho_k = Phi^-k(1) for k to 100: Phi^k(rho_k) = 1, the period word dies on a ring in exactly k steps, and the
    periods and preperiods are those the frames finding quotes."""
    periods, preperiods = {}, {}
    for k, prefix, period in frames.seed_past(100):
        frames.check_past(k, prefix, period)
        periods[k], preperiods[k] = len(period), len(prefix)
    starts = {p: min(k for k in periods if periods[k] == p) for p in set(periods.values())}
    assert starts == {1: 1, 3: 2, 6: 4, 12: 10, 24: 18, 48: 66}
    assert preperiods[28] == 0 and preperiods[30] == 4 and preperiods[66] == 188
    ((_, prefix, period),) = frames.seed_past(1)
    assert (prefix, period) == ([], [1]) and frames.phi((1 << 16) - 1, 16) == 1  # rho_1 = -1, the black half-line


def test_psi() -> None:
    """Psi(1) is the center column, and Psi preserves the first bit at which two numbers differ."""
    bits = 64
    psi_one = frames.psi(1, bits)
    assert [(psi_one >> t) & 1 for t in range(bits)] == center_column(bits).tolist()
    rng = np.random.default_rng(30)
    for _ in range(200):
        a = int(rng.integers(0, 1 << 62))
        n = int(rng.integers(0, 40))
        b = a ^ (1 << n) ^ (int(rng.integers(0, 1 << 20)) << (n + 1))
        difference = frames.psi(a, bits) ^ frames.psi(b, bits)
        assert difference & -difference == 1 << n
