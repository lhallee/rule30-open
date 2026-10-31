"""The one-tape machine of `Rule30Open.Complexity.QuadraticTime`, run in Python against the center column and the step
count the Lean module proves."""

from __future__ import annotations

import re

from pathlib import Path

from computations import one_tape
from computations.rule30 import center_column


ROOT = Path(__file__).resolve().parents[1]


def test_answers_and_steps() -> None:
    """On every input up to 80 the machine halts with c(n), after exactly 2 n^2 + 2 n l + 7 n + 3 l + 6 steps, which is
    at most 6 (n + 1)^2, with equality only at n = 0."""
    column = center_column(81)  # (81,)
    for n in range(81):
        answer, steps = one_tape.run(n)
        assert answer == bool(column[n]), n
        assert steps == one_tape.time(n), (n, steps)
        assert steps <= 6 * (n + 1) ** 2
    assert one_tape.time(0) == 6 == 6 * (0 + 1) ** 2
    assert all(one_tape.time(n) < 6 * (n + 1) ** 2 for n in range(1, 81))


def test_matches_lean_statements() -> None:
    """The Lean module states the same time formula, bound and table sizes: 17 states and 7 symbols."""
    source = (ROOT / "Rule30Open" / "Complexity" / "QuadraticTime.lean").read_text(encoding="utf-8")
    assert "2 * n * n + 2 * n * len n + 7 * n + 3 * len n + 6" in source
    assert "fun n => 6 * (n + 1) ^ 2" in source
    assert "q := 16" in source and "s := 4" in source
    # the sweep writes Rule 30 of the two cells left of the head and the cell under it, in both tables
    assert re.search(r"\.sweep a b m, \.row v k => \.inr \(\.sweep b v k, \.row \(rule30 a b v\) m, \.right\)", source)
    state = one_tape.State("sweep", a=True, b=False, mark=True)
    assert one_tape.transition(state, one_tape.row_symbol(True, False)) == (
        one_tape.State("sweep", False, True, False), one_tape.row_symbol(one_tape.rule30(True, False, True), True), 1)


def test_tape_layout() -> None:
    """After the run on n the tape holds the digits of 0 flipped to ones, the separator, and row n with its center
    marked at cell l + 1 + n: the layout the Lean tapes describe."""
    n = 13
    tape: dict[int, int] = {}
    i = 0
    while (1 << i) <= n:
        tape[i] = one_tape.D1 if (n >> i) & 1 else one_tape.D0
        i += 1
    state, head = one_tape.State("init0"), 0
    while True:
        result = one_tape.transition(state, tape.get(head, one_tape.BLANK))
        if len(result) == 1:
            break
        state, symbol, move = result
        tape[head] = symbol
        head += move
    ell = n.bit_length()
    assert head == ell + 1 + n
    row = 1 << n  # bit n is cell 0, as in computations.rule30
    for _ in range(n):
        row = (row << 1) ^ (row | (row >> 1))
    for x in range(-n, n + 1):
        black = bool((row >> (n + x)) & 1)
        assert tape[ell + 1 + n + x] == one_tape.row_symbol(black, x == 0), x
    assert tape.get(ell, one_tape.BLANK) == one_tape.BLANK and tape.get(ell + 2 * n + 2, one_tape.BLANK) == one_tape.BLANK
