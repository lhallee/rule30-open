"""Checks of computations/settled_phase.py: the diagonal recursion of a driven quadrant against stepping whole rows,
the causality of each diagonal in the driver, the single cell's quadrant against its own orbit, the interface
identity on random finite rows, and the latch entropy against enumeration and its two closed-form bounds."""

from __future__ import annotations

import math
import numpy as np

from computations import settled_phase as s
from computations.rule30 import center_column, spacetime


def test_quadrant_recursion_matches_row_stepping() -> None:
    rng = np.random.default_rng(3)
    for w in (0, 1, 4, 7):
        left = np.r_[1, rng.integers(0, 2, w)].astype(np.uint8)  # (w + 1,)
        driver = rng.integers(0, 2, 70).astype(np.uint8)  # (70,)
        driver[0] = left[-1]
        assert np.array_equal(s.quadrant_diagonals(left, driver, 45), s.quadrant_by_rows(left, driver, 45))


def test_diagonal_reads_driver_only_up_to_its_seed_time() -> None:
    rng = np.random.default_rng(4)
    left = np.array([1, 0, 1, 1], dtype=np.uint8)  # (4,), w = 3
    driver = rng.integers(0, 2, 80).astype(np.uint8)  # (80,)
    driver[0] = 1
    base = s.quadrant_diagonals(left, driver, 40)  # (40, 80)
    for m in (5, 12, 30):
        other = driver.copy()  # (80,)
        other[m:] ^= 1
        changed = s.quadrant_diagonals(left, other, 40)  # (40, 80)
        w = 3
        for d in range(40):
            if d - w < m:
                assert np.array_equal(base[d], changed[d])


def test_single_cell_quadrant_is_its_orbit() -> None:
    n = 60
    row = np.zeros(4 * n + 1, dtype=np.uint8)  # (4n + 1,), exact on the light cone of the center for n steps
    row[2 * n] = 1
    cells = spacetime(row, n)  # (n + 1, 4n + 1)
    diagonals = s.quadrant_diagonals(s.seed_left(), center_column(n), 30)  # (30, n)
    center = 2 * n
    for d in range(30):
        for t in range(d, n):
            assert diagonals[d, t] == cells[t, center + d - t]


def test_driven_quadrants_share_the_single_cell_periods() -> None:
    n, depth = 3000, 45
    skeleton = s.quadrant_diagonals(s.seed_left(), center_column(n), depth)  # (depth, n)
    for block in ("10", "110", "1101"):
        driven = s.quadrant_diagonals(s.seed_left(), s.periodic_driver(block, n), depth)  # (depth, n)
        for d in range(depth):
            assert s.period_and_onset(driven[d], d)[0] == s.period_and_onset(skeleton[d], d)[0]
        assert s.skeleton_shift(driven, skeleton, range(30, 45), 30, 16) is not None


def test_interface_identity_on_random_rows() -> None:
    rng = np.random.default_rng(6)
    steps = 40
    origin = steps + 12
    total = 0
    for _ in range(60):
        a = int(rng.integers(1, 1 << 10)) << (origin - 5)
        b = int(rng.integers(1, 1 << 10)) << (origin - 5)
        ok, used = s.interface_identity_holds(a, b, origin, steps)
        assert ok
        total += used
    assert total > 100


def test_latch_entropy_against_counts_and_bounds() -> None:
    for block in ("1", "10", "100", "110", "1101", "0110"):
        P = len(block)
        counts = {k: s.latch_count(block, k) for k in (16 - P, 16)}  # enumeration of 2^16 words at most
        growth = math.log(counts[16] / counts[16 - P]) / P  # (log of the count over one period) / P
        assert abs(growth - s.latch_entropy(block)) < 0.02
        assert s.latch_entropy(block) >= math.log(2) / (P if P >= 2 else 2) - 1e-12
    assert s.latch_entropy("0") == 0.0
    assert [s.latch_count("0", k) for k in range(1, 8)] == [k + 1 for k in range(1, 8)]


def test_grafted_periodic_tail_keeps_the_skeleton_on_a_small_band() -> None:
    n, depth = 1500, 40
    column = center_column(n)  # (n,)
    skeleton = s.quadrant_diagonals(s.seed_left(), column, depth)  # (depth, n)
    driver = column.copy()  # (n,)
    driver[25:] = s.periodic_driver("110", n - 25, 1)
    diagonals = s.quadrant_diagonals(s.seed_left(), driver, depth)  # (depth, n)
    assert np.array_equal(diagonals[:25], skeleton[:25])  # Lemma 1: diagonals d <= 24 never read c(25), ...
    assert column[25:28].tolist() != [1, 1, 0]  # the tail differs from the column, so the test has content
    assert not np.array_equal(diagonals[25:], skeleton[25:])
    assert s.skeleton_shift(diagonals, skeleton, range(30, 40), 30, 16) == 0


def test_shift_is_not_fixed_by_the_first_20_values_but_by_the_first_30() -> None:
    n, depth = 600, 100
    skeleton = s.quadrant_diagonals(s.seed_left(), center_column(n), depth)  # (depth, n)

    def shift(driver: np.ndarray) -> int | None:
        # driver: (n,)
        return s.skeleton_shift(s.quadrant_diagonals(s.seed_left(), driver, depth), skeleton, range(70, 100), 40, 8)

    rng = np.random.default_rng(1)
    driver = rng.integers(0, 2, n).astype(np.uint8)  # (n,)
    driver[0] = 1
    other = driver.copy()  # (n,), shares c(0..23) with driver
    other[24] ^= 1
    assert (shift(driver), shift(other)) == (6, 2)  # a shared prefix of 24 values does not fix the shift
    for seed in range(4):  # flipping c(30) or c(40) does not move it here (by the entry's sketch it reads c(0..29) only)
        rng = np.random.default_rng(seed)
        driver = rng.integers(0, 2, n).astype(np.uint8)  # (n,)
        driver[0] = 1
        for i in (30, 40):
            other = driver.copy()  # (n,)
            other[i] ^= 1
            assert shift(other) == shift(driver)
