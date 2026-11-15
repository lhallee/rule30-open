"""right_edge_density against a direct rule 30 run of the single cell and the bounds of the entry."""

from __future__ import annotations

import numpy as np

from computations.right_edge_density import right_step, seed_rows, step_slack, strip_counts


def test_codes_are_rule30_rows() -> None:
    steps, n = 40, 10
    rows = seed_rows(n, steps)  # (steps, n)
    width = 2 * steps + 3
    x = np.zeros(width, dtype=np.uint8)  # (width,)
    c = steps + 1
    x[c] = 1
    for t in range(steps):
        for e in range(n):
            assert rows[t, e] == (x[c + t - e] if c + t - e >= 0 else 0)
        left = np.concatenate(([0], x[:-1]))  # (width,)
        right = np.concatenate((x[1:], [0]))  # (width,)
        x = left ^ (x | right)


def test_slack_and_bounds() -> None:
    assert [step_slack(J) for J in range(1, 10)] == [-2] * 9  # the Lean bound 3W + 2W' >= 2J - 2, attained
    assert right_step(1, 4) == 0b111
    for J, L, k, black, white in strip_counts(12):
        assert black + white == J * L
        assert 2 * black >= L * (2 + k) and 2 * white >= L * k  # doubling diagonals, half black each
        assert 5 * white >= (2 * J - 2) * L  # periodic_white
