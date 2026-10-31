"""The block-size search against the full minimum, and the growth rates the finding quotes."""

from __future__ import annotations

import math

from computations import space_window


def test_search_matches_full_minimum() -> None:
    """The ternary search is within 0.1% of the minimum over all block sizes, in both forms, for small n."""
    for n in [50, 1000, 4096, 100_000]:
        for weak in [False, True]:
            space = space_window.weak_tree_space if weak else space_window.tree_space
            full = min(space(n, block) for block in range(1, n + 1))
            assert full <= space_window.best_block(n, weak=weak)[1] <= 1.001 * full


def test_growth_rates() -> None:
    """The best space over sqrt(n log2 n) settles near 2.5 while the ratio to sqrt(n) keeps growing, and the weak form
    is larger by a factor that grows."""
    rows = {row["k"]: row for row in space_window.table([20, 60, 120, 240])}
    assert rows[240]["over_sqrt_n_log_n"] < rows[20]["over_sqrt_n_log_n"] < 3.0
    assert all(abs(row["over_sqrt_n_log_n"] - 2.5) < 0.3 for row in rows.values())
    assert rows[20]["over_sqrt_n"] < rows[60]["over_sqrt_n"] < rows[240]["over_sqrt_n"]
    assert rows[20]["weak_over_space"] < rows[240]["weak_over_space"]
    assert math.isclose(space_window.tree_space(4, 2), 3 * 2 + 2 * math.log2(6))
