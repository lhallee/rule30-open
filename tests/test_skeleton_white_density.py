"""skeleton_white_density against a direct rule 30 step of padded rows, and the slack constant on small rows."""

from __future__ import annotations

from computations.skeleton_white_density import left_step, step_slack


def test_left_step_is_rule30() -> None:
    # the row R read from its frame cell, two white cells to its left; one rule 30 step, frame moved one cell left
    for x in range(1 << 7):
        row = [(x >> d) & 1 for d in range(7)]
        cells = [0, 0, 0] + row + [0, 0]
        new = [(cells[i - 1] if i else 0) ^ (cells[i] | (cells[i + 1] if i + 1 < len(cells) else 0))
               for i in range(len(cells))]
        assert new[2:9] == left_step(row)  # the frame cell moves from index 3 to index 2


def test_slack() -> None:
    # the Lean bound 3W + 2W' >= 2J - 4 is attained from J = 2 on
    assert [step_slack(J) for J in range(1, 11)] == [-2] + [-4] * 9
