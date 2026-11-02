"""`computations.tail_families` against the relation form of `limit_windows` and the Lean module's pieces."""

from __future__ import annotations

import re
from pathlib import Path

from computations import limit_windows as lw
from computations import tail_families as tf

LEAN = Path(__file__).resolve().parent.parent / "Rule30Open" / "Columns" / "TailFamilies14.lean"


def test_white_cycle_sets_against_relation() -> None:
    """One window at a time gives the preperiod and period of the powers of the white relation as whole bit sets."""
    for width in (5, 8):
        assert tf.white_cycle_sets(width) == lw.white_cycle(width)


def test_threshold() -> None:
    """The threshold is the start of the last run of good q; the good q before it are sporadic."""
    assert tf.threshold([False, True, False, True, True]) == (4, [2])
    assert tf.threshold([True, True]) == (1, [])
    assert tf.threshold([True, False]) == (None, [1])


def test_tail_table_against_limit_windows() -> None:
    """`tail_table` with the set-based cycle gives the thresholds of `limit_windows.tail_thresholds`."""
    tails = ["1", "111"]
    table = tf.tail_table(tails, 8, *tf.white_cycle_sets(8))
    expected = lw.tail_thresholds(tails, 8)
    assert {t: v[:2] for t, v in table.items()} == expected


def test_certificate_implies_good() -> None:
    """A cycle certificate of a single word (step 0) is found exactly where the limit sets are good, here; one of
    period 4 implies goodness along its class, and the union check of the kit's main branch implies goodness from its
    start (and fails where the start is not good)."""
    moves = lw.window_moves(10)
    for tail, q in (("1", 12), ("11", 9), ("101", 7), ("1", 6)):
        good = lw.is_good(lw.block_of(q, tail), moves)
        assert (tf.least_periods(tail, q, 0, moves, 4) is not None) == good
    assert tf.cycle_certificate("11", 9, 4, 2, moves)
    assert all(lw.is_good(lw.block_of(9 + 4 * m, "11"), moves) for m in range(3))
    assert any(tf.union_certificate("11", 9, periods, moves) for periods in (1, 2))
    assert all(lw.is_good(lw.block_of(q, "11"), moves) for q in range(9, 15))
    assert not lw.is_good(lw.block_of(9, "111"), moves)
    assert not any(tf.union_certificate("111", 9, periods, moves) for periods in (1, 2))


def test_lean_pieces_in_module() -> None:
    """The theorem of the tail 111011 in the Lean module is `lean_section` of its pieces, and two of its pieces pass
    the check in Python at 14 cells."""
    text = LEAN.read_text(encoding="utf-8")
    match = re.search(r"theorem cert_111011 : tailCert 14 \[[^\]]*\] (\d+) (\d+)\n    \[([^\]]*)\]", text)
    assert match is not None
    pieces = [tuple(int(v) for v in item.split(",")) for item in re.findall(r"\(([^)]*)\)", match.group(3))]
    assert tf.lean_section("111011", int(match.group(1)), int(match.group(2)), pieces) in text
    moves = lw.window_moves(14)
    for start, step, periods in (pieces[1], pieces[-1]):
        assert tf.cycle_certificate("111011", start, step, periods, moves)
