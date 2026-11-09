"""Checks of computations/binomial_duality.py: the transform against direct subset and binomial sums, the duality of
Rule30Open/Complexity/BinomialDuality.lean on random and planted sequences, the generating function behind the table
of multiples, and the center column's numbers against the independent scans of restricted_models and index_spectrum."""

from __future__ import annotations

from math import comb

import numpy as np

from computations import binomial_duality as b
from computations.index_spectrum import index_function, monomial_profile
from computations.restricted_models import dyadic_witnesses
from computations.rule30 import center_column


def direct_differences(values: np.ndarray, r: int) -> np.ndarray:
    """The r-th forward difference over GF(2), by r passes of x(t + 1) xor x(t)."""
    # values: (n,)
    out = values.astype(np.uint8)  # (n,)
    for _ in range(r):
        out = out[1:] ^ out[:-1]  # (n - pass,)
    return out  # (n - r,)


def test_transform_is_the_subset_sum_and_the_binomial_sum() -> None:
    rng = np.random.default_rng(1)
    values = rng.integers(0, 2, 300, dtype=np.uint8)  # (300,), not a power of two: the padding must not matter
    gamma = b.binomial_transform(values)  # (300,)
    for n in range(300):
        subset = sum(int(values[t]) for t in range(n + 1) if t & n == t) % 2
        binomial = sum(comb(n, t) * int(values[t]) for t in range(n + 1)) % 2
        difference = int(direct_differences(values[: n + 1], n)[0])  # the n-th difference at 0, Newton's form
        assert gamma[n] == subset == binomial == difference


def test_involution() -> None:
    rng = np.random.default_rng(2)
    for size in (1, 2, 37, 256, 1000):
        values = rng.integers(0, 2, size, dtype=np.uint8)  # (size,)
        assert np.array_equal(b.binomial_transform(b.binomial_transform(values)), values)


def test_shifts_and_differences_trade_places() -> None:
    # the transform of j -> diff^r f (j + s) is i -> diff^s gamma (i + r), on the indices the data determine
    rng = np.random.default_rng(3)
    values = rng.integers(0, 2, 512, dtype=np.uint8)  # (512,)
    gamma = b.binomial_transform(values)  # (512,)
    for r in range(7):
        for s in range(7):
            left = b.binomial_transform(direct_differences(values, r)[s:])  # (512 - r - s,)
            right = direct_differences(gamma, s)[r:]  # (512 - r - s,)
            assert np.array_equal(left, right)


def test_least_witnesses_agree_on_random_and_planted_sequences() -> None:
    rng = np.random.default_rng(4)
    size = 1 << 10
    for a in range(5):
        for m in range(5):
            # random data: the first mismatch is early, and must agree
            values = rng.integers(0, 2, size, dtype=np.uint8)  # (size,)
            gamma = b.binomial_transform(values)  # (size,)
            assert b.first_mismatch(values, 1 << m, 1 << a) == b.first_mismatch(gamma, 1 << a, 1 << m)
            # period 2^a from 2^m: the transform has period 2^m from 2^a, with no mismatch at all
            block = rng.integers(0, 2, 1 << a, dtype=np.uint8)  # (2^a,)
            periodic = np.resize(block, size - (1 << m))  # (size - 2^m,)
            values = np.concatenate([rng.integers(0, 2, 1 << m, dtype=np.uint8), periodic])  # (size,)
            gamma = b.binomial_transform(values)  # (size,)
            assert b.first_mismatch(values, 1 << m, 1 << a) is None
            assert b.first_mismatch(gamma, 1 << a, 1 << m) is None
            # a planted break at offset j0: the first mismatch moves to j0 on both sides
            for j0 in (0, 1, 5, 40, 300):
                broken = values.copy()  # (size,)
                broken[(1 << m) + j0 + (1 << a)] ^= 1
                assert b.first_mismatch(broken, 1 << m, 1 << a) == j0
                assert b.first_mismatch(b.binomial_transform(broken), 1 << a, 1 << m) == j0


def series_of_quotient(numerator: list[int], denominator: list[int], size: int) -> np.ndarray:
    """The power series of numerator / denominator over GF(2), coefficient lists from the constant term, with
    denominator[0] = 1, by long division."""
    out = np.zeros(size, dtype=np.uint8)  # (size,)
    for n in range(size):
        value = numerator[n] if n < len(numerator) else 0
        for i in range(1, min(n, len(denominator) - 1) + 1):
            value ^= denominator[i] & int(out[n - i])
        out[n] = value
    return out  # (size,)


def binomial_row(q: int) -> list[int]:
    """The coefficients of (1 + x)^q over GF(2)."""
    return [comb(q, i) % 2 for i in range(q + 1)]


def test_multiples_follow_the_generating_function() -> None:
    # the transform of 1/(1 + x^q) is (1 + x)^(q - 1) / ((1 + x)^q + x^q), from Gamma(x) = C(x/(1+x)) / (1+x)
    size = 1 << 11
    for q in (1, 2, 3, 5, 6, 9, 12):
        denominator = binomial_row(q)
        denominator[q] ^= 1  # (1 + x)^q + x^q
        expected = series_of_quotient(binomial_row(q - 1), denominator, size)  # (size,)
        assert np.array_equal(b.binomial_transform(b.multiples_indicator(q, size)), expected)
    assert b.multiples_period(5, 12) == (15, 1)
    assert b.multiples_period(6, 12) == (6, 2)
    assert b.multiples_period(8, 12) == (1, 8)


def test_least_eventual_period() -> None:
    values = np.array([1, 0, 0, 1, 1] + [0, 1, 1, 0, 1, 0] * 60, dtype=np.uint8)  # (365,): period 6 from 5
    assert b.least_eventual_period(values, 100, 50) == (6, 5)
    assert b.least_eventual_period(np.ones(40, dtype=np.uint8), 10, 5) == (1, 0)


def test_center_column_numbers() -> None:
    column = center_column(1 << 16)  # (65536,)
    gamma = b.binomial_transform(column)  # (65536,)
    for n in range(512):
        assert gamma[n] == sum(int(column[t]) for t in range(n + 1) if t & n == t) % 2
    assert int(gamma.sum()) == 32657
    for bits in (8, 10):
        assert int(gamma[: 1 << bits].sum()) == (1 << bits) - monomial_profile(index_function(column, bits))[0]
    witnesses = dyadic_witnesses(12, column)
    offsets = [b.rung_offset(column, gamma, k) for k in range(1, 13)]
    assert [oc for oc, _ in offsets] == [og for _, og in offsets] == [d for _, d in witnesses]
    assert [og for _, og in offsets] == [1, 1, 0, 1, 5, 0, 4, 0, 0, 3, 2, 4]
