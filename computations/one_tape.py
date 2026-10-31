"""The one-tape machine of `Rule30Open.Complexity.QuadraticTime`, run in Python: it computes the center cell c(n) from the
binary digits of n in the kit's model (`Rule30Problem3`), and this module checks its answer and its exact step count.

The machine keeps the input digits as a binary counter on the cells 0 .. l - 1 (l digits, least significant first), the
blank at cell l as a separator, and row t of the single black cell on the cells l + 1 .. l + 1 + 2t, cell x of the row
at l + 1 + t + x, the center marked. One iteration decrements the counter, walks to the row, rewrites it in place as
row t + 1 (shifted one cell right, so the region never grows left), and walks back. When the counter is zero the
machine finds the marked cell and halts with its color. Its step count on the input n, with l the number of digits, is

    time(n) = 2 n^2 + 2 n l + 7 n + 3 l + 6,

which is at most 6 (n + 1)^2.

    python -m computations.one_tape --max-n 64     # answers and step counts against c(n) and the formula
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from typing import Literal

from computations.rule30 import center_column

# Tape symbols: the kit's blank (0) and digits (1 for 0, 2 for 1), then row cells by color and mark.
BLANK, D0, D1 = 0, 1, 2


def row_symbol(black: bool, marked: bool) -> int:
    """The symbol of a row cell: 3 white, 4 black, 5 white marked, 6 black marked."""
    return 3 + int(black) + 2 * int(marked)


def rule30(left: bool, center: bool, right: bool) -> bool:
    """Rule 30: the new cell is the left neighbor xor (the cell or the right neighbor)."""
    return left ^ (center or right)


Move = Literal[-1, 0, 1]


@dataclass(frozen=True, slots=True)
class State:
    """A state: its phase and, for the sweep, the two row cells left of the head and whether the next cell is the
    center."""

    phase: str
    a: bool = False
    b: bool = False
    mark: bool = False


def transition(state: State, symbol: int) -> tuple[bool] | tuple[State, int, Move]:
    """The transition table: `(answer,)` halts, `(state, symbol, move)` writes and moves. Row symbols never meet the
    phases that read digits, and digits never meet the sweep; those cases halt with `False` and are never reached."""
    phase = state.phase
    is_row = symbol >= 3
    black, marked = bool((symbol - 3) & 1), symbol >= 5
    if phase == "init0":  # right over the digits to the separator
        return (State("init1"), symbol, 1) if symbol == BLANK else (state, symbol, 1)
    if phase == "init1":  # write the single black cell, marked, one cell right of the separator
        return (State("backRow"), row_symbol(True, True), -1)
    if phase == "backRow":  # left over the row to the separator
        return (State("backDigits"), symbol, -1) if symbol == BLANK else (state, symbol, -1)
    if phase == "backDigits":  # left over the digits to the blank before cell 0
        return (State("scan"), symbol, 1) if symbol == BLANK else (state, symbol, -1)
    if phase == "scan":  # decrement: zeros become ones up to the lowest one, which becomes zero
        if symbol == D0:
            return (state, D1, 1)
        if symbol == D1:
            return (State("toRow"), D0, 1)
        return (State("find"), symbol, 1)  # every digit was zero: the counter is spent
    if phase == "toRow":  # right over the remaining digits and the separator
        return (State("sweep"), symbol, 1) if symbol == BLANK else (state, symbol, 1)
    if phase == "sweep":  # in place, one cell right: new cell = rule30 of the old cells two left, one left, here
        if is_row:
            return (State("sweep", state.b, black, marked), row_symbol(rule30(state.a, state.b, black), state.mark), 1)
        return (State("last", state.b), row_symbol(rule30(state.a, state.b, False), state.mark), 1)
    if phase == "last":  # the second new cell past the old right edge, then back
        return (State("backRow"), row_symbol(rule30(state.a, False, False), False), -1)
    if phase == "find":  # right over the row to the marked cell: its color is the answer
        if is_row and marked:
            return (black,)
        if is_row:
            return (state, symbol, 1)
    return (False,)


def run(n: int, max_steps: int | None = None) -> tuple[bool, int]:
    """Run the machine on the input n: the answer and the number of steps, the step that halts included."""
    assert n >= 0
    tape: dict[int, int] = {}
    i = 0
    while (1 << i) <= n:
        tape[i] = D1 if (n >> i) & 1 else D0
        i += 1
    state, head, steps = State("init0"), 0, 0
    while max_steps is None or steps < max_steps:
        result = transition(state, tape.get(head, BLANK))
        steps += 1
        if len(result) == 1:
            return result[0], steps
        state, symbol, move = result
        tape[head] = symbol
        head += move
    raise RuntimeError(f"no halt within {max_steps} steps on input {n}")


def digits(n: int) -> int:
    """The number of binary digits of n, 0 for n = 0."""
    return n.bit_length()


def time(n: int) -> int:
    """The exact step count the Lean module proves: 2 n^2 + 2 n l + 7 n + 3 l + 6 with l the number of digits."""
    ell = digits(n)
    return 2 * n * n + 2 * n * ell + 7 * n + 3 * ell + 6


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-n", type=int, default=64)
    args = parser.parse_args()
    column = center_column(args.max_n + 1)  # (max_n + 1,)
    print("  n  c(n)  answer   steps  formula  6(n+1)^2")
    for n in range(args.max_n + 1):
        answer, steps = run(n)
        assert answer == bool(column[n]) and steps == time(n), (n, answer, steps)
        print(f"{n:3d}  {int(column[n])}     {int(answer)}     {steps:7d}  {time(n):7d}  {6 * (n + 1) ** 2:8d}")
    print(f"every input up to {args.max_n}: the answer is c(n) and the step count is the formula")


if __name__ == "__main__":
    main()
