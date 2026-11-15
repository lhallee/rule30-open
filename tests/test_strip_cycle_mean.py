"""strip_cycle_mean against a brute-force Bellman-Ford check and the Lean table of PairWhiteDensity."""

from __future__ import annotations

from fractions import Fraction
from itertools import product

from computations.strip_cycle_mean import cycle_mean, extends_right, potential


LEAN_TAB = [2, 2, 6, 6, 4, 4, 8, 8, 0, 0, 8, 0, 8, 8, 0, 8, 10, 10, 18, 10, 18, 18, 14, 14, 18, 18, 18, 18, 16, 12,
            12, 12]


def rule(a: int, b: int, c: int) -> int:
    """Rule 30 on a cell and its two neighbors, written out as the independent check."""
    return a ^ (b | c)


def test_cycle_means() -> None:
    assert cycle_mean(3, 0) == Fraction(1, 3)
    assert cycle_mean(2, 0) == Fraction(1, 4)
    assert cycle_mean(2, 4) == Fraction(5, 18)


def test_lean_potential_certifies_five_eighteenths() -> None:
    # the table, read on cells a + 1 .. a + 5, satisfies the step inequality of pair_step over all 128 cases
    for p in product((0, 1), repeat=7):
        p0, p1, p2, p3, p4, p5, r = p
        now = LEAN_TAB[16 * p1 + 8 * p2 + 4 * p3 + 2 * p4 + p5]
        n = [rule(p0, p1, p2), rule(p1, p2, p3), rule(p2, p3, p4), rule(p3, p4, p5), rule(p4, p5, r)]
        nxt = LEAN_TAB[16 * n[0] + 8 * n[1] + 4 * n[2] + 2 * n[3] + n[4]]
        assert nxt + 10 <= now + 18 * ((1 - p0) + (1 - p1))
    phi = potential(2, 4, 5, 18)
    assert [phi[i] for i in range(32)] == LEAN_TAB == [phi[i] for i in range(32, 64)]


def test_triple_potential() -> None:
    for p, q, r, s in product((0, 1), repeat=4):
        phi_now = 1 if (q or r) else 0
        phi_next = 1 if (rule(p, q, r) or rule(q, r, s)) else 0
        assert phi_next + 1 <= phi_now + (1 - p) + (1 - q) + (1 - r)


def test_extends_right() -> None:
    # the fixed point (10): columns 1, 0 constant extend; the 9-step cycle of the over-approximation does not
    assert extends_right(1, "1", "0")
    assert not extends_right(9, "011111111", "110101010")
