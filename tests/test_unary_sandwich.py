"""The converters and composite machines of `computations.unary_sandwich` against the closed forms of the unary sandwich
(findings/complexity/unary-sandwich.md), the input layouts of the kit's two models, the center column of
`computations.rule30`, and the step counts of `computations.one_tape`."""

from __future__ import annotations

from computations import one_tape
from computations import unary_sandwich as us
from computations.rule30 import center_column


def test_converters() -> None:
    """For n <= 128 each converter leaves exactly the other model's input with the head on cell 0, every pass of u2b
    and every round of b2u takes the time the proof gives, and the totals are the closed forms, which equal the
    expanded forms the finding also quotes."""
    for n in range(129):
        counts, tape, head = us.convert("u2b", n)
        assert tape == us.binary_input(n) and head == 0, n
        assert counts == us.u2b_pass_times(n) and sum(counts) == us.u2b_time(n), n
        counts, tape, head = us.convert("b2u", n)
        assert tape == us.unary_input(n, us.ONE) and head == 0, n
        assert counts == us.b2u_round_times(n) and sum(counts) == us.b2u_time(n), n
        ell = n.bit_length()
        s = sum((n >> i) & 1 for i in range(ell))  # the digit sum, digit by digit
        assert us.u2b_time(n) == 2 * n * (ell + 1) + ell * ell + 3 * ell + 2
        assert us.b2u_time(n) == (2 * n * ell + 6 * n - 2 * s + 2 * ell + 2 if n else 2)
    assert us.convert("u2b", 3)[0] == [10, 12, 8] and us.convert("b2u", 3)[0] == [7, 9, 7, 9]


def test_closed_form_bounds() -> None:
    """The bounds the sandwich uses, u2b(n) <= 3(n + 1)(l + 1) and b2u(n) + 1 <= 6(n + 1)(l + 1), for n < 2^16, and
    Legendre's count of trailing zeros that sums the rounds of b2u."""
    trailing = 0
    for n in range(1 << 16):
        ell = n.bit_length()
        assert us.u2b_time(n) <= 3 * (n + 1) * (ell + 1)
        assert us.b2u_time(n) + 1 <= 6 * (n + 1) * (ell + 1)
        if n:
            trailing += (n & -n).bit_length() - 1
        assert trailing == n - sum((n >> i) & 1 for i in range(ell))


def test_unary_of_kit() -> None:
    """u2b, then the quadratic simulator, decides c(n) on 1^n in u2b(n) + time(n) steps for n <= 48, time(n) the
    simulator's own count; u2b, then the kit's `lowBit`, decides whether n is odd in u2b(n) + 1 steps."""
    column = center_column(49)  # (49,)
    unary, parity = us.unary_of_kit(us.SIMULATOR), us.unary_of_kit(us.LOW_BIT)
    for n in range(49):
        answer, steps = one_tape.run(n)
        assert (answer, steps) == (bool(column[n]), one_tape.time(n))
        assert us.run_kit(us.SIMULATOR, n) == (answer, steps)
        assert us.run_unary(unary, n) == (bool(column[n]), us.u2b_time(n) + steps), n
        assert us.run_kit(us.LOW_BIT, n) == (n % 2 == 1, 1)
        assert us.run_unary(parity, n) == (n % 2 == 1, us.u2b_time(n) + 1), n


def test_kit_of_unary() -> None:
    """The kit's `periodicTM` decides a sequence with period 3 from 2 in n + 1 steps, and b2u, then it, computes the
    sequence on the kit's input in b2u(n) + n + 2 steps, for n <= 100."""

    def f(n: int) -> bool:
        return n in (0, 1) or n % 3 == 1

    unary = us.periodic_tm(f, 2, 3)
    binary = us.kit_of_unary(unary)
    for n in range(101):
        assert us.run_unary(unary, n) == (f(n), n + 1), n
        assert us.run_kit(binary, n) == (f(n), us.b2u_time(n) + n + 2), n


def test_round_trip() -> None:
    """b2u, u2b and the simulator, built as the kit machine made of the unary machine made of the simulator, compute
    c(n) in b2u(n) + u2b(n) + time(n) + 1 steps for n <= 32: the unary halting state costs the one extra step."""
    column = center_column(33)  # (33,)
    binary = us.kit_of_unary(us.unary_of_kit(us.SIMULATOR))
    parity = us.kit_of_unary(us.unary_of_kit(us.LOW_BIT))
    for n in range(33):
        expected = us.b2u_time(n) + us.u2b_time(n)
        assert us.run_kit(binary, n) == (bool(column[n]), expected + one_tape.time(n) + 1), n
        assert us.run_kit(parity, n) == (n % 2 == 1, expected + 2), n
