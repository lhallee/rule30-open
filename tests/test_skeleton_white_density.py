"""skeleton_white_density against a direct rule 30 step of padded rows, and the slack constant on small rows."""

from __future__ import annotations

import numpy as np

from computations.skeleton_white_density import left_step, skeleton_white, step_slack


def test_left_step_is_rule30() -> None:
    # the row R read from its frame cell, two white cells to its left; one rule 30 step, frame moved one cell left
    for x in range(1 << 7):
        row = [(x >> d) & 1 for d in range(7)]
        cells = [0, 0, 0] + row + [0, 0]
        new = [(cells[i - 1] if i else 0) ^ (cells[i] | (cells[i + 1] if i + 1 < len(cells) else 0))
               for i in range(len(cells))]
        assert new[2:9] == left_step(row)  # the frame cell moves from index 3 to index 2


def test_slack() -> None:
    # the Lean bound 3W + 2W' >= 2J - 4 is attained for 2 <= J <= 10 (computed here; J <= 12 in the entry)
    assert [step_slack(J) for J in range(1, 11)] == [-2] + [-4] * 9


def test_skeleton_white_small() -> None:
    # direct simulation of the single cell; left diagonal j at time t is the cell -t + j
    depth, steps, lo = 20, 300, 5
    row = {0: 1}
    diag = []
    for t in range(steps):
        diag.append([row.get(-t + j, 0) for j in range(depth + 1)])
        row = {i: row.get(i - 1, 0) ^ (row.get(i, 0) | row.get(i + 1, 0)) for i in range(-t - 1, t + 2)}
    d = np.array(diag)  # shape (steps, depth + 1)
    wt = d[steps - 128: steps - 112].sum(axis=0)  # shape (depth + 1,): black cells over 16 aligned times
    whites = np.cumsum(16 - wt)  # shape (depth + 1,)
    J = np.arange(1, depth + 2)  # shape (depth + 1,)
    ratio = (5 * whites[2:] / ((2 * J[2:] - 4) * 16)).min()
    frac, r = skeleton_white(depth, steps, lo)
    assert abs(frac - (1 - wt[lo:].mean() / 16)) < 1e-12
    assert abs(r - ratio) < 1e-12
