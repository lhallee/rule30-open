"""The cycle means and potentials behind Rule30Open.Foundations.StripWhiteDensity, and the period-five orbit that
attains 2/5 on every strip."""

from __future__ import annotations

from fractions import Fraction
from itertools import product

from computations.strip_cycle_mean import cycle_mean, potential


def rule(a: int, b: int, c: int) -> int:
    return a ^ (b | c)


def test_cycle_means() -> None:
    assert cycle_mean(4, 0) == Fraction(3, 8)
    for J in (5, 6, 7):
        assert cycle_mean(J, 0) == Fraction(2, 5)


def test_potential_step_width_five() -> None:
    # the table the Lean module uses for width 5, checked directly on every strip and both outside cells
    J = 5
    phi = potential(J, 0, 2, 5)
    assert max(phi.values()) == 2 * J
    for cells in product((0, 1), repeat=J + 2):
        s = cells[1:J + 1]
        n = [rule(cells[i - 1], cells[i], cells[i + 1]) for i in range(1, J + 1)]
        idx = lambda w: sum(b << (J - 1 - i) for i, b in enumerate(w))  # noqa: E731
        assert phi[idx(n)] + 2 * J <= phi[idx(s)] + 5 * (J - sum(s))


def test_period_five_orbit_attains_two_fifths() -> None:
    row = [1, 1, 0, 0, 1] * 8  # (40,) periodic
    rows = []
    for _ in range(10):
        rows.append(row)
        row = [rule(row[i - 1], row[i], row[(i + 1) % 40]) for i in range(40)]
    for J in range(1, 12):
        for a in range(5):
            whites = sum(1 - r[a + j] for r in rows for j in range(J))
            assert whites == 2 * J * 10 // 5
