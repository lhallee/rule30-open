"""Tests for computations/two_index.py, each against an independent computation."""

from __future__ import annotations

import math

import numpy as np

from computations.two_index import (
    compose,
    cycle_lengths,
    diagonal_array,
    doubling_levels,
    longest_flat_run,
    mahler_coefficients,
    mahler_degree,
    phi_cycle_length,
    phi_transducer,
    row_periods,
    run_transducer,
    synthetic_array,
    transducer_sizes,
    white_runs,
    white_runs_from_cycles,
    window_kernel_counts,
)


def _phi(x: np.ndarray, mask: int) -> np.ndarray:
    """Phi on an array of integers modulo mask + 1."""
    # x: (k,)
    return (x ^ ((x << 1) | (x << 2))) & mask  # (k,)


def _bsub(m: np.ndarray, t: np.ndarray) -> np.ndarray:
    """Every binary digit of m is a digit of t (binom(t, m) odd, by Lucas)."""
    return ((m & t) == m).astype(np.uint8)


def test_cycle_lengths_against_phi_and_cells() -> None:
    """Level lifting against iterating Phi until 1 returns, and against the least periods of the diagonals of a direct
    run of the single cell by the rule table; the diagonals themselves agree on one period."""
    lengths, diagonals = cycle_lengths(14)
    assert lengths == [phi_cycle_length(n) for n in range(1, 15)]
    array = diagonal_array(30, 14, 256)  # (14, 256)
    assert row_periods(array) == lengths
    for j in range(14):
        assert np.array_equal(diagonals[j], array[j, : lengths[j]])
    assert doubling_levels(cycle_lengths(20)[0]) == [2, 4, 5, 7, 8, 10, 16, 17]
    assert longest_flat_run(cycle_lengths(20)[0]) == 5


def test_white_runs() -> None:
    """W(2^m) from the integer rows, from the cycle lengths (per_iff_gap) and from the rule-table run agree."""
    from_rows = white_runs(7)
    from_cycles = white_runs_from_cycles(cycle_lengths(20)[0])
    array = diagonal_array(30, 40, 129)  # (40, 129)
    direct = [int(np.flatnonzero(array[1:, 1 << m])[0]) for m in range(8)]
    assert from_rows == from_cycles[:8] == direct == [0, 2, 3, 5, 6, 8, 14, 15]


def test_rule90_and_kernel_sections() -> None:
    """Rule 90's diagonal array is Pascal's triangle mod 2 on even rows (Lucas), and every section beyond level 0 is
    a constant times bsub(v, 2w + a), as `TwoIndex.rd90_sect_succ` states; Rule 30's windows are all distinct."""
    size = 64
    array = diagonal_array(90, size, size)  # (64, 64)
    j = np.arange(size)[:, None]  # (64, 1)
    t = np.arange(size)[None, :]  # (1, 64)
    assert np.array_equal(array, ((j % 2 == 0) & (_bsub(j // 2, t) == 1)).astype(np.uint8))
    v = np.arange(8)[:, None]  # (8, 1)
    w = np.arange(8)[None, :]  # (1, 8)
    shapes = [_bsub(v, 2 * w + a) for a in (0, 1)] + [np.zeros((8, 8), dtype=np.uint8)]  # each (8, 8)
    for e in (1, 2, 3):
        for r in range(1 << e):
            for s in range(1 << e):
                window = array[np.ix_((1 << e) * np.arange(8) + r, (1 << e) * np.arange(8) + s)]  # (8, 8)
                assert any(np.array_equal(window, x) for x in shapes)
    assert window_kernel_counts(array, 8, 3) == [1, 3, 3, 3]
    assert window_kernel_counts(diagonal_array(30, 64, 64), 8, 3) == [1, 4, 16, 64]


def test_rule90_time_column_sections() -> None:
    """Rule 90 in time and column, x >= 0, against the binomial coefficient, and its sections against the borrow
    form of `TwoIndex.st90_sect_succ`."""
    size = 64
    t = np.arange(size)[:, None]  # (64, 1)
    x = np.arange(size)[None, :]  # (1, 64)
    full = diagonal_array(90, 2 * size, size)  # (128, 64), cell(t, t - j) at [j, t]
    cells = np.zeros((size, size), dtype=np.uint8)  # (64, 64), cell(t, x) at [t, x]
    for tt in range(size):
        for xx in range(tt + 1):
            cells[tt, xx] = full[tt - xx, tt]
    expected = np.array([[int(xx <= tt and (tt - xx) % 2 == 0 and math.comb(tt, (tt - xx) // 2) % 2 == 1)
                          for xx in range(size)] for tt in range(size)], dtype=np.uint8)  # (64, 64)
    assert np.array_equal(cells, expected)
    v = np.arange(8)[:, None]  # (8, 1)
    w = np.arange(8)[None, :]  # (1, 8)
    for e in (1, 2, 3):
        half = 1 << (e - 1)
        for r in range(1 << e):
            for s in range(1 << e):
                window = cells[np.ix_((1 << e) * np.arange(8) + r, (1 << e) * np.arange(8) + s)]  # (8, 8)
                beta, tau = int(r < s), r // half
                form = ((w + beta <= v) & (_bsub(np.maximum(v - w - beta, 0), 2 * v + tau) == 1)).astype(np.uint8)
                assert np.array_equal(window, form) or not window.any()


def test_kernel_lemma_controls() -> None:
    """Rows of the automatic controls have periods at most a constant times j + 1; Rule 30's do not on the range."""
    for array in (diagonal_array(150, 32, 256), synthetic_array("thue", 32, 256), synthetic_array("mod3", 32, 256)):
        assert max(p / (j + 1) for j, p in enumerate(row_periods(array))) <= 3
    lengths = cycle_lengths(30)[0]
    assert max(p / (j + 1) for j, p in enumerate(lengths)) > 100


def test_mahler_degrees() -> None:
    """The coefficients in the binomial basis rebuild each diagonal through math.comb, and at a doubling level the
    degree is half the period."""
    lengths, diagonals = cycle_lengths(12)
    for j in range(12):
        seq = diagonals[j]  # (P,)
        coeff = mahler_coefficients(seq)  # (P,)
        rebuilt = [sum(int(coeff[k]) * math.comb(t, k) for k in range(seq.size)) % 2 for t in range(seq.size)]
        assert rebuilt == seq.tolist()
        if j >= 2 and lengths[j] == 2 * lengths[j - 1]:
            assert mahler_degree(seq) == lengths[j] // 2


def test_transducers() -> None:
    """The squared transducers compute Phi^(2^k), and their state counts match the distinct sections of Phi^(2^k) on
    words of 8 bits after prefixes of at most 9 bits."""
    assert transducer_sizes(2) == [3, 7, 35]
    bits, mask = 16, (1 << 16) - 1
    machine = phi_transducer()
    rng = np.random.default_rng(0)
    xs = rng.integers(0, 1 << bits, size=50, dtype=np.int64)  # (50,)
    for k in range(3):
        ys = xs.copy()  # (50,)
        for _ in range(1 << k):
            ys = _phi(ys, mask)
        assert [run_transducer(machine, int(x), bits) for x in xs] == ys.tolist()
        sections: set[bytes] = set()
        depth = 8
        for length in range(10):
            u = np.arange(1 << length, dtype=np.int64)[:, None]  # (2^length, 1)
            z = u + (np.arange(1 << depth, dtype=np.int64)[None, :] << length)  # (2^length, 256)
            for _ in range(1 << k):
                z = _phi(z, (1 << (length + depth)) - 1)
            for row in (z >> length) & ((1 << depth) - 1):  # each (256,)
                sections.add(row.tobytes())
        assert len(sections) == [3, 7, 35][k]
        machine = compose(machine, machine)


def test_linear_transducers() -> None:
    """Rule 90's right-edge step to the power 2^k is x xor (x << 2^(k+1)) over GF(2) (Frobenius), whose minimal
    transducer keeps the last 2^(k+1) input bits; Rule 150's, x xor (x << 2^k) xor (x << 2^(k+1)), keeps as many."""
    expected = [2 ** (2 ** (k + 1)) for k in range(3)]
    assert transducer_sizes(2, 90) == expected
    assert transducer_sizes(2, 150) == expected
    for rule, shifts in ((90, (2,)), (150, (1, 2))):
        machine = phi_transducer(rule)
        for x in range(64):
            y = x
            for shift in shifts:
                y ^= x << shift
            assert run_transducer(machine, x, 8) == y & 255
