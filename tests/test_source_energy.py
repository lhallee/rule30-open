"""Checks of computations/source_energy.py: the kit's source energy against a direct double loop and against its
expansion into autocorrelations, the mean over all sign patterns, the alternating sequence's lower bound, the entry's
two inequalities on random, alternating and Rule 30 sequences, and the cycle averages against closed forms."""

from __future__ import annotations

import cmath
import itertools
import math
from fractions import Fraction

import numpy as np

from computations import source_energy as se
from computations.binomial_duality import binomial_transform
from computations.rule30 import center_column


def direct_energy(cells: np.ndarray, n: int) -> int:
    """Esrc(n) by the definition, cell by cell."""
    # cells: (m,)
    size = 1 << n
    total = 0
    for u in range(size):
        value = 0
        for s in se.shifts(n):
            if u + s < size:
                value += 1 - 2 * int(cells[u + s])
        total += value * value
    return total


def autocorrelation_energy(cells: np.ndarray, n: int) -> int:
    """Esrc(n) as the sum over pairs (s, s') of S of sum over u < N with u + s, u + s' < N of z(u + s) z(u + s')."""
    # cells: (m,)
    size = 1 << n
    z = 1 - 2 * cells[:size].astype(np.int64)  # (N,)
    total = 0
    for s, s2 in itertools.product(se.shifts(n), repeat=2):
        top = size - max(s, s2)
        total += int(np.dot(z[s : s + top], z[s2 : s2 + top]))
    return total


def test_energy_matches_definition_and_expansion() -> None:
    rng = np.random.default_rng(0)
    for n in range(1, 8):
        cells = rng.integers(0, 2, 1 << n).astype(np.uint8)  # (N,)
        energy = se.source_energy(cells, n)
        assert energy == direct_energy(cells, n)
        assert energy == autocorrelation_energy(cells, n)
    cells = center_column(128)  # (128,)
    assert se.source_energy(cells, 7) == direct_energy(cells, 7)


def test_iid_mean_is_the_average_over_all_patterns() -> None:
    n = 3
    energies = [
        se.source_energy(np.array(bits, dtype=np.uint8), n)
        for bits in itertools.product((0, 1), repeat=8)
    ]
    assert Fraction(sum(energies), len(energies)) == se.iid_mean(n)


def test_alternating_energy_is_not_small() -> None:
    for n in range(3, 12):
        cells = (np.arange(1 << n) & 1).astype(np.uint8)  # (N,)
        assert se.source_energy(cells, n) >= (3 * (1 << n) // 4) * (n - 2) ** 2


def test_fourier_coefficient_and_polynomial() -> None:
    rng = np.random.default_rng(1)
    cells = rng.integers(0, 2, 300).astype(np.uint8)  # (300,)
    theta = Fraction(3, 7)
    direct = sum(
        (1 - 2 * int(cells[t])) * cmath.exp(-2j * math.pi * t * 3 / 7)
        for t in range(300)
    )
    assert abs(se.fourier_coefficient(cells, 300, theta) - direct) < 1e-9
    for n in range(2, 12):
        assert abs(se.lacunary_polynomial(n, Fraction(1, 2)) - (n - 2)) < 1e-9
        direct_p = sum(
            cmath.exp(2j * math.pi * s / 3) for s in [0] + [2**j for j in range(n - 1)]
        )
        assert abs(se.lacunary_polynomial(n, Fraction(1, 3)) - direct_p) < 1e-9


def test_inequalities_hold() -> None:
    rng = np.random.default_rng(2)
    thetas = [
        Fraction(0),
        Fraction(1, 2),
        Fraction(1, 4),
        Fraction(3, 8),
        Fraction(1, 3),
        Fraction(2, 5),
        Fraction(1, 7),
    ]
    sequences = [
        rng.integers(0, 2, 1 << 9).astype(np.uint8),  # (512,)
        (np.arange(1 << 9) & 1).astype(np.uint8),  # (512,)
        ((np.arange(1 << 9) % 4) < 1).astype(np.uint8),  # (512,), a biased class mod 4
        center_column(1 << 9),  # (512,)
    ]
    for cells in sequences:
        for n in range(4, 10):
            energy = se.source_energy(cells, n)
            for length in ((1 << (n - 1)) + 1, 3 << (n - 2), 1 << n):
                for theta in thetas:
                    value = abs(se.fourier_coefficient(cells, length, theta)) / length
                    if abs(se.lacunary_polynomial(n, theta)) > 1e-9:
                        assert (
                            value <= se.fourier_bound(energy, n, length, theta) + 1e-9
                        )
                for k in range(n - 1):
                    bound = se.progression_bound(energy, n, length, k)
                    for r in range(1 << k):
                        assert (
                            abs(se.progression_sum(cells, length, k, r)) / length
                            <= bound + 1e-12
                        )


def test_cycle_averages() -> None:
    assert abs(se.cycle_average(Fraction(3, 8)) - 1) < 1e-12
    assert abs(se.cycle_average(Fraction(1, 3)) + 0.5) < 1e-12
    assert abs(se.cycle_average(Fraction(1, 5)) + 0.25) < 1e-12
    assert abs(se.cycle_average(Fraction(1, 7)) - complex(-1, math.sqrt(7)) / 6) < 1e-12
    assert abs(se.cycle_average(Fraction(1, 9))) < 1e-12
    for p in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 73):
        for k in range(3):
            for a in range(1, p):
                assert abs(se.cycle_average(Fraction(a, (2**k) * p))) > 1e-6
    # P_n(theta) / n tends to the cycle average
    assert (
        abs(
            se.lacunary_polynomial(400, Fraction(1, 7)) / 400
            - se.cycle_average(Fraction(1, 7))
        )
        < 0.01
    )


def test_class_bias_matches_progression_sum() -> None:
    cells = center_column(1 << 8)  # (256,)
    for k in range(4):
        expected = max(
            abs(se.progression_sum(cells, 256, k, r)) for r in range(1 << k)
        ) / (256 >> k)
        assert se.class_bias(cells, 8, k) == expected


def test_source_signs_are_dyadic_differences_of_the_binomial_transform() -> None:
    """c(u) + c(u + 2^j) = sum over i subset of u of gamma(i + 2^j) mod 2, with gamma the binomial transform."""
    cells = center_column(256)  # (256,)
    gamma = binomial_transform(cells)  # (256,)
    for j in range(6):
        for u in range(256 - 64):
            total = 0
            for i in range(u + 1):
                if i & u == i:
                    total ^= int(gamma[i + (1 << j)])
            assert total == int(cells[u]) ^ int(cells[u + (1 << j)])


def test_planted_nine() -> None:
    """The planted sequence: P_n(1/9) stays bounded by 6, its energy is near the exact expectation, and the class
    t = 0 mod 9 is biased."""
    for n in range(2, 300):
        assert abs(se.lacunary_polynomial(n, Fraction(1, 9))) <= 6
    n, delta = 12, 0.5
    size = 1 << n
    mean = delta * np.cos(2 * np.pi * (np.arange(size) % 9) / 9)  # (N,)
    expected = 0.0
    for u in range(size):
        terms = [s for s in se.shifts(n) if u + s < size]
        expected += (
            sum(1 - mean[u + s] ** 2 for s in terms)
            + sum(mean[u + s] for s in terms) ** 2
        )
    energies = [
        se.source_energy(se.planted_nine(size, delta, seed), n) for seed in range(8)
    ]
    assert abs(np.mean(energies) / expected - 1) < 0.05
    cells = se.planted_nine(size, delta, 0)  # (N,)
    assert abs(cells[::9].mean() - (1 - delta) / 2) < 0.06
