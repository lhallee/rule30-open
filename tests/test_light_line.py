"""light_line against brute-force evolution of all inputs, Python against C, and the numbers the entries quote."""

from __future__ import annotations

import itertools
from fractions import Fraction

import numpy as np

from computations.light_line import (RULE30, RULE45, RULE120, RULE180, all_rows, back_solutions, constant_probability,
                                     exact, law_statistics, letter_law, level_transitive, light_lines, light_words,
                                     minimal_forbidden, monte_carlo, rho_bruteforce)


def test_letter_law_against_bruteforce() -> None:
    # the transducer law gives the light-line autocorrelation that brute force over every input gives
    for tt in (RULE30, RULE120, RULE180, RULE45):
        law = letter_law(6, tt)
        for k in range(1, 7):
            marg: dict[tuple[int, ...], int] = {}
            for w, c in law.items():
                marg[w[:k]] = marg.get(w[:k], 0) + c
            r = Fraction(sum(c * (-1) ** sum(x >> 1 for x in w) for w, c in marg.items()), 4 ** 6)
            assert r == rho_bruteforce(k, tt), (tt, k)


def test_known_values() -> None:
    assert [rho_bruteforce(k) for k in range(1, 6)] == [Fraction(-1, 2), Fraction(1, 4), Fraction(-1, 4),
                                                       Fraction(5, 32), Fraction(-5, 64)]
    # Rule 180: 1 - 2^(-2^v) with v the 2-adic valuation of k
    assert [rho_bruteforce(k, RULE180) for k in (1, 2, 3, 4)] == [Fraction(1, 2), Fraction(3, 4), Fraction(1, 2),
                                                                Fraction(15, 16)]


def test_c_against_python() -> None:
    rows = exact(10, RULE30)
    for K, supp, H, r1, r2, r3 in rows:
        s, h, p1, p2, p3 = law_statistics(letter_law(K, RULE30), K)
        assert (supp, r1, r2, r3) == (s, p1, p2, p3) and abs(H - h) < 1e-9
    assert rows[9][1] == 1792 and rows[9][3] == 22280  # rho(10) = 22280 / 4^10
    K, supp, H, r1, r2, r3 = exact(8, RULE180)[-1]
    assert supp == 2 ** 9 - 1 and Fraction(r1, 4 ** 8) == 1 - Fraction(1, 256)


def test_forbidden_words() -> None:
    w5 = light_words(5)
    assert len(w5) == 30 and set(range(32)) - w5 == {0b00100, 0b11011}
    assert [len(light_words(k)) for k in range(1, 9)] == [2, 4, 8, 16, 30, 54, 96, 170]
    assert minimal_forbidden(9) == ["00100", "11011", "111000", "000111", "111110010", "000001101"]


def test_preimage_synchronization() -> None:
    # an image showing 010 at q, q+1, q+2 (q >= 1) fixes the preimage on 0..q: cell q is 1, cell q-1 is not z_{q-1}
    for z in itertools.product((0, 1), repeat=11):
        sols = back_solutions(list(z))
        for q in range(1, 9):
            if z[q:q + 3] == (0, 1, 0):
                assert all(y[q] == 1 and y[q - 1] == 1 - z[q - 1] for y in sols)
                assert len({tuple(y[:q + 1]) for y in sols}) == 1


def test_rule180() -> None:
    for T in range(1, 7):
        assert constant_probability(T) == Fraction(2, 3) + Fraction(1, 3 * 4 ** T)
    # each light line is constant on the white times of the next one, for every input, to time 5
    rows = all_rows(14)  # (2^14, 14)
    lines = [light_lines(rows, 5, j, RULE180) for j in range(2)]  # 2 x (2^14, 6)
    for a, b in itertools.combinations(range(6), 2):
        both_white = (lines[1][:, a] == 0) & (lines[1][:, b] == 0)
        assert (lines[0][both_white, a] == lines[0][both_white, b]).all()


def test_monte_carlo_small() -> None:
    res = monte_carlo(12, 40, 8, [1, 2, 13], [1, 3], seed=3, threads=1)
    for k, r in ((1, -0.5), (2, 0.25)):
        m, e = res[1, 1, k]
        assert abs(m - r) < 6 * e + 1e-3
    m, e = res[1, 3, 1]  # E (-1)^{(Gy)_0 + y_0 + y_1} = 1/2
    assert abs(m - 0.5) < 6 * e + 1e-3


def test_level_transitive() -> None:
    assert all(level_transitive(n) for n in range(1, 11))
