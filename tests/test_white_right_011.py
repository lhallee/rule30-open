"""Tests for computations/white_right_011.py: the loops that the Lean module runs against the big-integer Psi of
`computations.coupled`, the gap check against a direct scan of windows, the theorem against direct runs of whole
finite rows, and the census section against the Lean module."""

from __future__ import annotations

from pathlib import Path

import numpy as np

from computations import coupled
from computations import white_right_011 as wr

MODULE = Path(__file__).resolve().parent.parent / "Rule30Open" / "Columns" / "WhiteRightHalf011.lean"


def center_column(left: int, width: int, center: int, steps: int) -> list[int]:
    """The center column at times 0 .. steps - 1 of the row with `left` at depths 1 .. width (bit d the depth d),
    `center` at cell 0 and a white right half, by stepping the whole row as one integer."""
    offset = width + steps + 2  # bit offset + x is cell x
    state = center << offset
    for d in range(1, width + 1):
        state |= ((left >> d) & 1) << (offset - d)
    column = []
    for _ in range(steps):
        column.append((state >> offset) & 1)
        state = (state << 1) ^ (state | (state >> 1))  # new cell x = cell x - 1 xor (cell x or cell x + 1)
    return column


def test_loops_match_coupled() -> None:
    """Column 1, the center and the rebuilt row agree with `coupled.drive_column`, `coupled.center` and
    `coupled.psi`, for 011 and for words of other periods, in every phase."""
    for word in ("011", "01", "0001", "00101"):
        for phase in range(len(word)):
            assert wr.column_one(word, phase, 400) == coupled.drive_column(word, phase, 0, 400)
            assert wr.centers(word, phase, 401) == coupled.center(word, phase, 401)
            row = wr.psi_bits(word, phase, 400)
            assert row >> 1 == coupled.psi(word, phase, 0, 400)
            assert row & 1 == int(word[phase % len(word)])


def test_gaps_check_against_windows() -> None:
    """`gaps_check` says the same as a scan of every window, on random rows and on the rows of 011."""
    rng = np.random.default_rng(5)
    rows = [int(rng.integers(0, 1 << 62)) | (int(rng.integers(0, 1 << 62)) << 62) for _ in range(40)]
    rows += [wr.psi_bits(wr.WORD, phase, 120) for phase in range(3)]
    for row in rows:
        for gap in (2, 4, 6, 9, 16):
            starts = 120 - gap
            scan = all(any((row >> d) & 1 for d in range(w + 1, w + gap + 1)) for w in range(starts))
            assert wr.gaps_check(row, 120, gap, starts) == scan


def test_runs_of_011() -> None:
    """At depth 4,096 the longest white runs of the rows of 011 are below 16 in every phase, as at 32,768."""
    for phase in range(3):
        row = wr.psi_bits(wr.WORD, phase, 4096)
        assert wr.longest_white_run(row, 4096) < wr.GAP
        assert wr.gaps_check(row, 4096, wr.GAP, 4096 - wr.GAP)


def test_rows_leave_011() -> None:
    """A row with a white right half and its left half within depth W leaves 011 by time W + 16: the truncation of the
    rebuilt row at W leaves exactly at its first black depth beyond W, and random left halves leave no later."""
    rng = np.random.default_rng(7)
    for phase in range(3):
        row = wr.psi_bits(wr.WORD, phase, 200)
        c = [wr.letter(wr.WORD, phase, t) for t in range(200)]
        for width in range(120):
            truncated = row & ((1 << (width + 1)) - 2)  # depths 1 .. width
            first_black = next(d for d in range(width + 1, 200) if (row >> d) & 1)
            column = center_column(truncated, width, c[0], first_black + 1)
            leaves = next(t for t in range(first_black + 1) if column[t] != c[t])
            assert leaves == first_black <= width + wr.GAP
            for _ in range(3):
                left = int(rng.integers(0, 1 << 62)) << 1 & ((1 << (width + 1)) - 2)
                column = center_column(left, width, c[0], width + wr.GAP + 1)
                assert any(column[t] != c[t] for t in range(width + wr.GAP + 1))


def test_lean_section_matches_module() -> None:
    """The census section of the Lean module is the one `lean_section` prints."""
    text = MODULE.read_text()
    for line in wr.lean_section().splitlines():
        assert line in text
