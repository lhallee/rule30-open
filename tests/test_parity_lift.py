"""Parity models: Walsh coefficients against a direct sum, GF(2) ranks against an independent elimination."""

from __future__ import annotations

import numpy as np

from computations import parity_lift as pl


def direct_walsh(table: np.ndarray) -> np.ndarray:
    """W[a] = sum over x of (-1)^(f(x) xor a.x) as a matrix product over all pairs (a, x)."""
    # table: (2^n,)
    size = table.shape[0]
    index = np.arange(size)  # (2^n,)
    both = index[:, None] & index[None, :]  # (2^n, 2^n)
    parity = np.zeros_like(both)  # (2^n, 2^n)
    while both.any():
        parity ^= both & 1
        both = both >> 1
    return ((1 - 2 * parity) * (1 - 2 * table.astype(np.int64))[None, :]).sum(axis=1)  # (2^n,)


def int_rank(matrix: np.ndarray) -> int:
    """GF(2) rank with Python integers as rows, reduced by their lowest set bit."""
    # matrix: (rows, cols)
    basis: dict[int, int] = {}
    for row in matrix:
        v = int("".join(str(int(b)) for b in row[::-1]), 2)
        while v:
            low = v & -v
            if low not in basis:
                basis[low] = v
                break
            v ^= basis[low]
    return len(basis)


def test_walsh_against_direct_sum() -> None:
    """The fast transform agrees with the direct sum on c_t (t <= 3) and on the restricted center (t <= 4)."""
    for t in (2, 3):
        table = pl.rule_table(t, 30)  # (2^(2t+1),)
        assert np.array_equal(pl.walsh(table), direct_walsh(table))
    for t in (2, 3, 4):
        restricted = pl.restrict(pl.rule_table(t, 30))  # (2^(2t-1),)
        w = direct_walsh(restricted)  # (2^(2t-1),)
        assert np.array_equal(pl.walsh(restricted), w)
        assert int(restricted.sum()) % 2 == 1 and np.all(w % 4 == 2)


def test_rank_against_int_elimination() -> None:
    """The packed elimination agrees with an elimination on Python integers, on lifts and on random matrices."""
    rng = np.random.default_rng(3)
    for table in (pl.rule_table(2, 30), pl.restrict(pl.rule_table(3, 30)), pl.rule_table(2, 45)):
        lift = pl.xor_lift(table)  # (2^n, 2^n)
        assert pl.gf2_rank(lift) == int_rank(lift)
    for rows, cols in ((5, 70), (70, 9), (40, 40)):
        matrix = (rng.random((rows, cols)) < 0.3).astype(np.uint8)  # (rows, cols)
        assert pl.gf2_rank(matrix) == int_rank(matrix)


def test_odd_weight_lemmas_on_random_functions() -> None:
    """Odd weight on m >= 2 cells: every Walsh coefficient is 2 mod 4, and the XOR lift squares to 1 over GF(2)."""
    rng = np.random.default_rng(5)
    for m in (2, 3, 4, 5):
        for _ in range(4):
            table = rng.integers(0, 2, 1 << m).astype(np.uint8)  # (2^m,)
            if table.sum() % 2 == 0:
                table[0] ^= 1
            assert np.all(pl.walsh(table) % 4 == 2)
            lift = pl.xor_lift(table).astype(np.int64)  # (2^m, 2^m)
            assert np.array_equal((lift @ lift) % 2, np.eye(1 << m, dtype=np.int64))
            assert pl.gf2_rank(lift) == 1 << m


def test_rule30_and_controls() -> None:
    """Rule 30's sparsities for t = 2 .. 5 and lift ranks for t <= 3; Rules 90 and 150 have sparsity 1 and rank 2."""
    assert [pl.sparsity(pl.rule_table(t, 30)) for t in (2, 3, 4, 5)] == [8, 44, 202, 878]
    assert [pl.table_row(t, 30, rank=True)["rank_full"] for t in (2, 3)] == [8, 32]
    assert pl.table_row(3, 45, rank=True)["rank_full"] == 24
    for rule in (90, 150):
        row = pl.table_row(3, rule, rank=True)
        assert row["sparsity"] == 1 and row["rank_full"] == 2 and row["weight_parity"] == 0
