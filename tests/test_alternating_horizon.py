"""Runs of a prescribed center and the width of the forced left half, against stepping whole rows."""

from __future__ import annotations

import numpy as np

from computations.alternating_horizon import U64, brute_runs, horizon_table, psi_batch, run_length, subfunction_profile
from computations.coupled import psi


def test_batch_matches_scalar() -> None:
    """The NumPy bit slices compute the same Psi(R) as the big-integer routine of `coupled`."""
    rng = np.random.default_rng(0)
    rights = rng.integers(0, 1 << 20, size=40, dtype=np.int64).astype(U64)  # (40,)
    for word in ("0", "1", "10", "01", "0001"):
        for phase in range(2):
            rows = psi_batch(word, phase, rights, 40)  # (40,)
            for right, row in zip(rights, rows):
                assert int(row) == psi(word, phase, int(right), 40)


def test_condrey_closed_forms() -> None:
    """Condrey's Theorem 2 and 3: for the zero trace L_(2k+1) is the OR of R_1 .. R_(2k+1) and L_(2k) is R_(2k) with no
    earlier 1; for the all-one trace L_j is 1 exactly at the even j. R_j is column j of the right half."""
    depth = 12
    rights = np.arange(1 << 9, dtype=U64)  # (512,)
    zero, one = psi_batch("0", 0, rights, depth), psi_batch("1", 0, rights, depth)  # each (512,)
    for right, z, o in zip(range(1 << 9), zero, one):
        cell = lambda j: (right >> (j - 1)) & 1 if j <= 9 else 0
        for j in range(1, depth + 1):
            earlier = any(cell(i) for i in range(1, j))
            expected = int(earlier or cell(j)) if j % 2 else int(bool(cell(j)) and not earlier)
            assert (int(z) >> (j - 1)) & 1 == expected
            assert (int(o) >> (j - 1)) & 1 == (1 if j % 2 == 0 else 0)


def test_run_length_against_stepping_rows() -> None:
    """For each right half the best left half of width M keeps the word for run_length steps, over every left half."""
    for word in ("0", "1", "10"):
        for phase in range(len(word)):
            for cells, width in ((4, 4), (5, 3)):
                brute = brute_runs(word, phase, cells, width, width + 30)  # {R: run}
                rights = np.arange(1 << cells, dtype=U64)  # (2^cells,)
                runs = run_length(word, phase, rights, width, width + 30)  # (2^cells,)
                for right in range(1 << cells):
                    if word[phase] == "0" and right == 0:
                        continue  # the zero row is excluded by hand in the table
                    assert int(runs[right]) == brute[right], (word, phase, cells, width, right)


def test_table_reproduces_condrey_and_alternating_radii() -> None:
    """Condrey's w + 2: zero center w + 1 or w + 2 by parity with 2^w - 1 rows, one center the other way with 2^w rows;
    and the alternating table against stepping every row of radius 5 and 6."""
    for radius, best, count, _ in horizon_table("0", 8):
        assert best == (radius + 1 if radius % 2 == 0 else radius + 2) and count == (1 << radius) - 1
    for radius, best, count, _ in horizon_table("1", 8):
        assert best == (radius + 2 if radius % 2 == 0 else radius + 1) and count == 1 << radius
    table = {radius: best for radius, best, _, _ in horizon_table("10", 6)}
    for radius in (5, 6):
        stepped = max(max(brute_runs("10", phase, radius, radius, radius + 30).values()) for phase in range(2))
        assert table[radius] == stepped


def test_profile_width() -> None:
    """The decision diagram of a cell of Psi has at most 2 nodes per level for the constant words, 5 for the alternating
    word at depth 6; checked against grouping the subfunctions by their truth tables."""
    constant = subfunction_profile("0", 0, 8, 8)  # per depth, per k
    assert max(max(widths) for widths in constant) <= 2
    alternating = subfunction_profile("10", 0, 8, 6)
    assert max(alternating[5]) == 5
    values = [(psi("10", 0, right, 6) >> 5) & 1 for right in range(1 << 8)]  # cell at depth 6
    for k in range(9):
        distinct = {tuple(values[low + (high << k)] for high in range(1 << (8 - k))) for low in range(1 << k)}
        assert len(distinct) == alternating[5][k]
