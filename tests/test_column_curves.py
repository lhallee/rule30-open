"""column_curves against independent checks: field axioms, factorization over F_2 by trial division at the place
s = 1, the linear rule run cell by cell, and the two criteria of the entry on small rows."""

from __future__ import annotations

import random

import numpy as np

from computations import column_curves as cc


def trial_factor_degrees(P: int) -> list[int]:
    """Degrees of the irreducible factors of the F_2 polynomial P (bit mask), with multiplicity, by trial division."""
    degrees = []
    d = 1
    while P.bit_length() > 1:
        for f in cc.irreducibles(d):
            while P.bit_length() > 1 and cc.poly_mod(P, f) == 0:
                quotient, rem = 0, P
                df = f.bit_length() - 1
                while rem and rem.bit_length() - 1 >= df:
                    shift = rem.bit_length() - 1 - df
                    quotient ^= 1 << shift
                    rem ^= f << shift
                P = quotient
                degrees.append(d)
        d += 1
        if 2 * d > P.bit_length() - 1:
            break  # a factor left of degree below 2d has no factor of degree below d, so it is irreducible
    if P.bit_length() > 1:
        degrees.append(P.bit_length() - 1)
    return sorted(degrees)


def norm_degrees(a: int, b: int, c: int, pi: int) -> list[int]:
    """Degrees of the irreducible factors over F_2 of the norm of Q modulo pi: the product of Q(theta, z) over the
    conjugates theta of the class of s in F_2[s]/pi, by polynomial arithmetic over F_2[s]/pi and trial division. The
    norm factors with degree k d for each factor of degree d over F_(2^k) whose roots do not lie in a smaller field,
    so its degrees give the Frobenius pattern without counting roots."""
    k = pi.bit_length() - 1

    def mul(x: int, y: int) -> int:
        """Product in F_2[s]/pi."""
        return cc.poly_mod(cc.clmul(x, y), pi)

    conj = [cc.poly_mod(0b10, pi)]  # the class of s and its Frobenius images
    for _ in range(k - 1):
        conj.append(mul(conj[-1], conj[-1]))
    prod = [1]  # coefficients of the norm, lowest first
    for th in conj:
        f = [th, th if c else 0, 1 ^ (th if b else 0), th if a else 0, th]
        out = [0] * (len(prod) + len(f) - 1)
        for i, x in enumerate(prod):
            for j, y in enumerate(f):
                out[i + j] ^= mul(x, y)
        prod = out
    assert all(v in (0, 1) for v in prod)  # the norm has coefficients in F_2
    return trial_factor_degrees(sum(v << i for i, v in enumerate(prod)))


def test_fields() -> None:
    # F_(2^m) for m <= 8: x^(2^m) = x for every element, and every nonzero element has an inverse
    for m in range(1, 9):
        F = cc.Field(m)
        for x in range(1 << m):
            y = x
            for _ in range(m):
                y = F.mul(y, y)
            assert y == x
        for x in range(1, 1 << m):
            assert any(F.mul(x, y) == 1 for y in range(1, 1 << m))


def test_patterns_at_s_equal_one() -> None:
    # at the place s = 1 the quartic has coefficients in F_2: the root counts agree with trial division
    for a, b, c in [(0, 0, 1), (0, 1, 1), (1, 0, 0), (1, 1, 0), (1, 0, 1), (1, 1, 1)]:
        P = 0b10001 | (a << 3) | ((1 ^ b) << 2) | (c << 1)  # z^4 + a z^3 + (1 + b) z^2 + c z + 1
        degrees = trial_factor_degrees(P)
        counts = cc.frobenius_pattern(a, b, c, 0b11)
        for d, n in zip((1, 2, 3, 4), counts):
            if len(set(degrees)) == len(degrees):  # distinct factor degrees (so squarefree): roots in F_(2^d)
                assert n == sum(e for e in degrees if d % e == 0)
    assert trial_factor_degrees(0b10111) == [1, 3]  # z^4 + z^2 + z + 1 = (z + 1)(z^3 + z^2 + 1)
    assert trial_factor_degrees(0b10011) == [4]  # z^4 + z + 1


def test_certificates_by_norms() -> None:
    # the certificates of the entry from the factor degrees of the norms: [1, 3] and [4] at s + 1, [12] (an irreducible
    # quartic over F_8) at s^3 + s + 1, and [2, 6] (a root and a cubic over F_4) at s^2 + s + 1
    for rule in ((0, 0, 1), (1, 0, 0)):
        assert norm_degrees(*rule, 0b11) == [1, 3] and norm_degrees(*rule, 0b1011) == [12]
    for rule in ((0, 1, 1), (1, 1, 0)):
        assert norm_degrees(*rule, 0b11) == [4] and norm_degrees(*rule, 0b111) == [2, 6]


def test_certificates() -> None:
    # every asymmetric rule has a 3-cycle and a 4-cycle at places of degree at most 3, the ones the entry quotes
    found = cc.certificates()
    assert found[(0, 0, 1)] == {"3-cycle": 0b11, "4-cycle": 0b1011}
    assert found[(0, 1, 1)] == {"3-cycle": 0b111, "4-cycle": 0b11}
    assert found[(1, 0, 0)] == found[(0, 0, 1)] and found[(1, 1, 0)] == found[(0, 1, 1)]


def test_run_row_cell_by_cell() -> None:
    # the convolution matches new x_i = sum_k a_k x_(i+k) applied cell by cell
    rng = random.Random(30)
    for coeffs, left, q in [([1, 0, 1], 1, 2), ([1, 1, 1], 1, 2), ([2, 1, 1], 1, 3), ([1, 0, 1, 1, 1], 2, 2)]:
        for _ in range(5):
            row = [rng.randrange(q) for _ in range(rng.randint(1, 5))]
            row[0] = row[-1] = 1
            rows, origin = cc.run_row(coeffs, left, row, q, 12)
            cells = {i: v for i, v in enumerate(row)}  # cell index -> value
            for t in range(12):
                got = {i - origin: int(v) for i, v in enumerate(rows[t]) if v}
                assert got == {i: v for i, v in cells.items() if v}
                span = range(min(cells) - 3, max(cells) + 4)
                cells = {i: sum(coeffs[k + left] * cells.get(i + k, 0) for k in range(-left, len(coeffs) - left)) % q
                         for i in span}


def test_radius_two_criterion() -> None:
    # result 3 of the entry on rows of up to 5 cells: the eventually periodic columns of the four rules are all white
    for a, b, c in cc.ASYMMETRIC:
        found = cc.ep_columns([1, a, b, c, 1], 2, 2, 5, 4, 512, 16)
        assert found and all(not col.any() for _, _, col in found)


def test_radius_one_criterion() -> None:
    # result 2 of the entry on rows of up to 3 cells over F_3 and up to 6 cells over F_2: periodic exactly at the axes
    for q, width in [(3, 3), (2, 6)]:
        for a in range(1, q):
            for b in range(q):
                for c in range(1, q):
                    found = {(tuple(row), p) for row, p, _ in cc.ep_columns([a, b, c], 1, q, width, 3, 512, 16)}
                    for row in cc.rows_up_to_translation(width, q):
                        for p in range(-3, len(row) + 3):
                            assert ((tuple(row), p) in found) == cc.twisted_symmetric(row, p, a, c, q), (q, a, b, c, row, p)


def test_twisted_symmetric_examples() -> None:
    # over F_2 the criterion is mirror symmetry; over F_3 with a = c it is antisymmetry
    assert cc.twisted_symmetric([1, 0, 1], 1, 1, 1, 2) and not cc.twisted_symmetric([1, 1], 0, 1, 1, 2)
    assert cc.twisted_symmetric([1, 0, 2], 1, 1, 1, 3) and not cc.twisted_symmetric([1, 0, 1], 1, 1, 1, 3)
    assert np.array_equal(cc.run_row([1, 0, 1], 1, [1], 2, 3)[0][:, 3], np.array([1, 0, 0]))
