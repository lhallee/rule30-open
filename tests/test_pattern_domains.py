"""`computations.pattern_domains` against blocks checked one by one on rows from `computations.rule30.spacetime`."""

from __future__ import annotations

import numpy as np

from computations import pattern_domains as pd
from computations.rule30 import spacetime


def brute_blocks(rows: np.ndarray, side: int, max_period: int) -> set[tuple[int, int, int]]:
    """(t, x, p) for every block of rows t - side + 1 .. t and cells x .. x + side - 1 whose rows all repeat with
    period p, checked cell by cell."""
    # rows: (T, n)
    found = set()
    steps, n = rows.shape
    for t in range(side - 1, steps):
        for x in range(n - side + 1):
            for p in range(1, max_period + 1):
                if all(rows[s, y] == rows[s, y + p] for s in range(t - side + 1, t + 1) for y in range(x, x + side - p)):
                    found.add((t, x, p))
    return found


def test_segments_against_cells() -> None:
    """A segment is periodic exactly when each cell equals the cell p places right of it."""
    rng = np.random.default_rng(3)
    for _ in range(20):
        row = rng.integers(0, 2, 40).astype(bool)  # (40,)
        row[10:30] = np.tile(row[10:13], 7)[:20]
        got = pd.periodic_segments(row, 8, 4)  # (4, 40)
        for p in range(1, 5):
            for x in range(40):
                expected = x + 8 <= 40 and all(row[y] == row[y + p] for y in range(x, x + 8 - p))
                assert got[p - 1, x] == expected


def test_census_against_cells() -> None:
    """The single cell's census over 48 steps, blocks of 5 cells and periods up to 3, is the cell-by-cell census inside
    the light cone."""
    steps, side, max_period = 48, 5, 3
    result = pd.domain_census(steps, side, max_period)
    n = 2 * steps + 1
    cells = np.zeros(n, dtype=np.uint8)  # (n,)
    cells[steps] = 1
    rows = spacetime(cells, steps - 1).astype(bool)  # (steps, n), exact on this range since the cone stays inside
    expected = {(t, x - steps, p) for t, x, p in brute_blocks(rows, side, max_period)
                if abs(x - steps) <= t - side + 1 and abs(x + side - 1 - steps) <= t - side + 1}
    assert set(result["blocks"]) == expected
    assert result["left"] == len({(t, x) for t, x, _ in expected if x + side <= 0})
    assert result["right"] == len({(t, x) for t, x, _ in expected if x > 0})
    assert result["right"] > 0


def test_fixed_background() -> None:
    """The alternating row is fixed by Rule 30, so away from the ends every block of it is a domain of period 2."""
    row = np.tile([True, False], 60)  # (120,)
    for t, current, blocks in pd.stream(row, 30, 6, 3, "test"):
        if t >= 5:
            assert blocks[1, t + 1: 120 - t - 7].all()
            assert not blocks[0, t + 1: 120 - t - 7].any()
