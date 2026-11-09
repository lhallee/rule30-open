"""diagonal_freedom against independent checks: the bitwise map against the closed form of Phi, the cycle lengths
against a direct orbit of Phi, and the construction on random T-functions and in its center-override form."""

from __future__ import annotations

import random

from computations import diagonal_freedom as df


def phi_closed(y: int, n: int) -> int:
    """Phi(y) = y xor (2y or 4y) modulo 2^n, from the closed form."""
    return (y ^ ((y << 1) | (y << 2))) & ((1 << n) - 1)


def test_apply_is_phi() -> None:
    rng = random.Random(30)
    for _ in range(200):
        n = rng.randint(1, 30)
        y = rng.getrandbits(n)
        assert df.apply(y, n, df.phi_level, {}) == phi_closed(y, n)


def test_cycle_lengths_of_phi() -> None:
    # the orbit of 1 under the closed form modulo 2^n, counted directly
    for n in range(0, 18):
        y, steps = phi_closed(1, n), 1
        while y != 1 % (1 << n):
            y, steps = phi_closed(y, n), steps + 1
        assert df.cycle_lengths(1, n, df.phi_level)[n] == steps


def test_construction_on_random_t_functions() -> None:
    # cycle lengths kept, readout free or forced as the theorem says, at most two residues per level
    assert df.check_random(8, 40, seed=5) == {"lengths": 0, "readout": 0, "residues": 0, "cases": 40}


def test_center_override_small() -> None:
    # to 16 levels with t0 = 5 (L_i > i there): lengths, readout, light cone and edges, and no change before L_i
    for word in df.WORDS.values():
        r = df.check_override(16, 5, word)
        assert r["lengths"] and r["readout"] and r["cone"] and r["before"] == 0
