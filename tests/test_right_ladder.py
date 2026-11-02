"""Tests for computations/right_ladder.py: the dynamic program against brute force over every free word, the beam
against the dynamic program, and the single cell as a member of every level."""

from __future__ import annotations

import itertools

import numpy as np

from computations.right_ladder import (committed, first_change, free_decided, ladder_beam, ladder_exact, level_step,
                                       runs, simulate, single_cell_column, single_cell_count, steady_rate)


def _brute(k: int, T: int) -> np.ndarray:
    """The center columns of every free word of length T, by cell-by-cell replay."""
    free = np.array(list(itertools.product((0, 1), repeat=T)), np.uint8)  # (2^T, T)
    return simulate(k, free)  # (2^T, T + 1)


def test_exact_matches_brute_force() -> None:
    for k in (0, 1, 2, 3):
        cols = _brute(k, 12)  # (4096, 13)
        for color in (0, 1):
            rows = list(ladder_exact(12, k, color))
            for row in rows:
                assert row.best == int((cols[:, :row.t + 1] == color).sum(axis=1).max())
            # the window maximum: c(7 .. 12) over every free word (every state reachable at 6 is reached by one)
            assert rows[-1].window == int((cols[:, 7:] == color).sum(axis=1).max())


def test_single_cell_is_a_member() -> None:
    T = 24
    center = single_cell_column(T, 0)  # (T + 1,)
    for k in (0, 1, 2, 5):
        free = single_cell_column(T, k + 1)[:T]  # (T,)
        assert np.array_equal(simulate(k, free[None, :])[0], center)
    for color in (0, 1):
        for k in (0, 2):
            assert list(ladder_exact(T, k, color))[-1].best >= single_cell_count(T, color)
    # at k >= T the free cell cannot reach the center by time T: the level is the single cell
    assert list(ladder_exact(8, 8, 0, window=False))[-1].best == single_cell_count(8, 0)


def test_beam_against_exact() -> None:
    for k, color in ((1, 0), (2, 1)):
        exact = list(ladder_exact(30, k, color, window=False))[-1].best
        wide = ladder_beam(30, k, color, width=1 << 20)
        assert wide.best == exact
        narrow = ladder_beam(30, k, color, width=8)
        assert narrow.best <= exact
        assert int((simulate(k, np.array([narrow.free], np.uint8))[0] == color).sum()) == narrow.best


def test_drivers_helpers() -> None:
    assert steady_rate([(100, 70), (200, 150), (300, 230)], 150) == 0.8
    assert runs(np.array([1, 1, 0, 1, 0, 0], np.uint8)) == [(1, 2), (0, 1), (1, 1), (0, 2)]
    free = single_cell_column(20, 2)[:20]  # (20,)
    first = first_change(1, free)  # (20,)
    assert np.array_equal(first >= 0, free_decided(1, free))
    assert (first[first >= 0] >= np.arange(20)[first >= 0] + 2).all()  # cell 2 needs two steps to reach the center


def test_committed_centers() -> None:
    T, t = 14, 6
    for k in (1, 3):
        free = np.random.default_rng(k).integers(0, 2, (8, T)).astype(np.uint8)  # (8, T)
        cols = simulate(k, free)  # (8, T + 1)
        B, C, R = np.zeros((8, 1), np.uint64), np.ones(8, np.uint64), np.zeros(8, np.uint64)  # (8, 1), (8,), (8,)
        for s in range(t):
            nxt = [level_step(B, C, R, k, f) for f in (0, 1)]
            pick = free[:, s].astype(bool)  # (8,)
            B = np.where(pick[:, None], nxt[1][0], nxt[0][0])
            C = np.where(pick, nxt[1][1], nxt[0][1])
            R = np.where(pick, nxt[1][2], nxt[0][2])
        assert np.array_equal(C, cols[:, t].astype(np.uint64))
        for color in (0, 1):
            assert np.array_equal(committed(B, C, R, k, color), (cols[:, t + 1:t + k + 1] == color).sum(axis=1))
    for lookahead in (False, True):
        assert ladder_beam(24, 2, 0, width=1 << 20, lookahead=lookahead).best == \
            list(ladder_exact(24, 2, 0, window=False))[-1].best
