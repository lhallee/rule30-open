"""Persistent homology of space-time windows, against connected components and cycle ranks counted directly."""

from __future__ import annotations

import numpy as np
import pytest

pytest.importorskip("ripser")  # the optional group `topology` of pyproject.toml
pytest.importorskip("sklearn")

from computations import persistence as ph  # noqa: E402
from computations import rule30


def test_bars_match_graph_counts() -> None:
    """The H0 bars that outlive 1 and sqrt 2 count the 4- and 8-connected clusters (scipy labels), and the H1 bars
    born at 1 are the cycle rank of the 4-neighbor graph, on Rule 30 windows and on coin flips, both colors."""
    windows = np.concatenate([ph.random_windows(3, 12, 8, seed=0), ph.coin_windows(3, 12, seed=1)])  # (6, 12, 12)
    for window in windows:
        for value in (0, 1):
            f = ph.features(window, value)
            assert tuple(int(v) for v in f[:3]) == ph.graph_counts(window, value)


def test_one_hole() -> None:
    """A ring of black cells around a 3 x 3 white square has one H1 bar that lives past 2, and one cluster."""
    window = np.zeros((7, 7), dtype=np.uint8)  # (7, 7)
    window[1:6, 1:6] = 1
    window[2:5, 2:5] = 0
    f = ph.features(window, 1)
    names = dict(zip(ph.FEATURES, f))
    assert names["clusters4"] == 1 and names["holes"] == 1 and names["largest_hole"] > 2


def test_windows_are_rule_30() -> None:
    """The single cell's windows read its center column (OEIS A051023) down their middle, and every random window is
    a piece of a direct run with `rule30.spacetime`."""
    w = ph.seed_windows(4, 8, 0)  # (4, 8, 8)
    assert np.array_equal(w[:, :, 4].reshape(-1), rule30.center_column(32))
    left = ph.seed_windows(2, 8, 16, edge="left")  # (2, 8, 8)
    right = ph.seed_windows(2, 8, 16, edge="right")  # (2, 8, 8)
    n = 64
    cells = np.zeros(2 * n + 1, dtype=np.uint8)  # (2n + 1,), cell 0 at index n
    cells[n] = 1
    full = rule30.spacetime(cells, 40)  # (41, 2n + 1)
    for i in range(2):
        t0 = 16 + 8 * i
        assert np.array_equal(left[i], full[t0:t0 + 8, n - t0 + 4:n - t0 + 12])
        assert np.array_equal(right[i], full[t0:t0 + 8, n + t0 - 12:n + t0 - 4])
    rng = np.random.default_rng(5)
    width = 8 + 2 * (6 + 8)
    row = rng.integers(0, 2, (1, width), dtype=np.uint8)[0]  # (width,), the draw of random_windows(1, 8, 6, 5)
    direct = rule30.spacetime(row, 14)  # (15, width)
    assert np.array_equal(ph.random_windows(1, 8, 6, seed=5)[0], direct[6:14, 14:22])


def test_two_sample_tests() -> None:
    """The energy test and the classifier find a shift in the mean and find nothing between two draws of one law."""
    rng = np.random.default_rng(0)
    a = rng.normal(size=(60, 3))  # (60, 3)
    b = rng.normal(size=(60, 3))  # (60, 3)
    assert ph.energy_test(a, b, 40)[1] > 0.05
    assert ph.energy_test(a, b + 1.0, 40)[1] < 0.05
    y = np.concatenate([np.zeros(60, dtype=np.int64), np.ones(60, dtype=np.int64)])  # (120,)
    assert ph.classifier_auc(np.concatenate([a, b + 1.0]), y, 2)[0] > 0.8
