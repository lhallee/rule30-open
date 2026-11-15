"""Pseudo-measure linear programs for Rule 30, against the known 2/5 bound and the single cell's actual cycle."""

from __future__ import annotations

from fractions import Fraction

from computations.edge_pseudo_measures import (
    black_mass,
    check_pair_potential,
    cycle_rows,
    empirical_pseudo_measure,
    left_edge_bound,
    ordinary_white_bound,
    verify_pseudo_measure,
    white_end_feasible,
)


def test_ordinary_frame_reproduces_two_fifths() -> None:
    """The ordinary-frame LP gives exactly the white bound 2/5 that the pair potential certifies."""
    assert check_pair_potential() == Fraction(2, 5)
    for k in (1, 2):
        assert abs(ordinary_white_bound(k) - 0.4) < 1e-9


def test_cycle_is_a_pseudo_measure_and_bounds_hold() -> None:
    """The actual cycle's empirical measure passes the exact check, so every LP value is at most its count."""
    n = 14
    cyc = cycle_rows(n)
    assert len(cyc) == 4
    for k in (1, 2):
        J = n - k + 1
        mu = empirical_pseudo_measure(n, J, k)
        assert verify_pseudo_measure(mu, k)
        assert not verify_pseudo_measure(mu, k, white_end=True)
        blacks = sum(r[d] for r in cyc for d in range(J))
        assert black_mass(mu, k) == Fraction(blacks, len(cyc))
        assert left_edge_bound(J, k, 1) <= float(black_mass(mu, k)) + 1e-9
        assert left_edge_bound(J, k, 0) <= J - float(black_mass(mu, k)) + 1e-9


def test_monotone_in_depth_and_no_white_end() -> None:
    """Restricting a pseudo-measure to fewer diagonals keeps it feasible, and none ends on the white word."""
    vals = [left_edge_bound(J, 1, 1) for J in (4, 8, 12, 16)]
    assert all(a <= b + 1e-9 for a, b in zip(vals, vals[1:], strict=False))
    assert abs(vals[0] - 2.5) < 1e-9
    assert not any(white_end_feasible(J, k) for J in (3, 5, 9) for k in (1, 2))
