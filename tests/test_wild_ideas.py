"""Checks of computations/wild_ideas.py against independent computations on small cases."""

from __future__ import annotations

import itertools
import math

import numpy as np

from computations import wild_ideas as w
from computations.algebra import center_truth_table
from computations.rule30 import center_column


def numpy_rank(matrix: np.ndarray) -> int:
    """GF(2) rank by row reduction on a numpy array, a second implementation."""
    # matrix: (rows, columns)
    m = matrix.copy() % 2  # (rows, columns)
    rank = 0
    for column in range(m.shape[1]):
        pivots = np.nonzero(m[rank:, column])[0]  # (candidates,)
        if pivots.size == 0:
            continue
        p = rank + pivots[0]
        m[[rank, p]] = m[[p, rank]]
        hits = np.nonzero(m[:, column])[0]  # (hits,)
        hits = hits[hits != rank]
        m[hits] ^= m[rank]
        rank += 1
        if rank == m.shape[0]:
            break
    return rank


def poly_mul_mod(a: int, b: int, n: int) -> int:
    """Product of two GF(2) polynomials held as integers, modulo x^n."""
    result = 0
    while b:
        low = (b & -b).bit_length() - 1
        result ^= a << low
        b &= b - 1
    return result & ((1 << n) - 1)


def test_gf2_rank_matches_numpy() -> None:
    rng = np.random.default_rng(5)
    for shape in [(6, 9), (12, 12), (20, 7)]:
        matrix = rng.integers(0, 2, shape, dtype=np.uint8)  # shape
        matrix[1] = matrix[0] ^ matrix[2 % shape[0]]
        rows = [w.bits_to_int(row) for row in matrix]
        assert w.gf2_rank(rows) == numpy_rank(matrix)


def test_frobenius_power_is_squaring() -> None:
    cells = center_column(40)  # (40,)
    f = w.bits_to_int(cells)
    square = poly_mul_mod(f, f, 64)
    assert w.frobenius_power(cells, 1, 64) == square
    assert w.frobenius_power(cells, 2, 64) == poly_mul_mod(square, square, 64)


def brute_force_nullity(cells: np.ndarray, k: int, n: int, degree: int) -> int:
    """Dimension of the Ore solution space by listing every coefficient vector."""
    f = w.bits_to_int(cells[:n])
    series = [1] + [f]
    for _ in range(k):
        series.append(poly_mul_mod(series[-1], series[-1], n))
    unknowns = (k + 2) * (degree + 1)
    solutions = 0
    for choice in itertools.product((0, 1), repeat=unknowns):
        total = 0
        for i, s in enumerate(series):
            poly = sum(bit << j for j, bit in enumerate(choice[i * (degree + 1) : (i + 1) * (degree + 1)]))
            total ^= poly_mul_mod(poly, s, n)
        solutions += total == 0
    return int(round(math.log2(solutions)))


def test_ore_profile_matches_brute_force() -> None:
    cells = center_column(16)  # (16,)
    for k, degree in [(0, 3), (1, 2), (1, 3), (2, 2)]:
        n = 11
        assert w.ore_profile(cells, k, n, degree)[degree] == brute_force_nullity(cells, k, n, degree)


def test_ore_finds_thue_morse_equation() -> None:
    # (1 + x)^3 f^2 + (1 + x)^2 f + x = 0 for the Thue-Morse series: a solution at D = 3, k = 1, none for k = 0
    profile = w.ore_profile(w.thue_morse(512), 1, 512, 6)  # (7,)
    assert w.first_relation(profile) == 3
    assert w.first_relation(w.ore_profile(w.thue_morse(512), 0, 512, 40)) is None
    assert w.first_relation(w.ore_profile(center_column(512), 1, 512, 40)) is None


def test_lll_reduces_and_keeps_lattice() -> None:
    basis = [[1, 0, 0, 1_000_003], [0, 1, 0, 2_718_281], [0, 0, 1, 3_141_592]]
    reduced = w.lll(basis)
    # same lattice: determinant of the Gram matrix is unchanged
    def gram_det(rows: list[list[int]]) -> int:
        g = np.array([[sum(a * b for a, b in zip(u, v)) for v in rows] for u in rows], dtype=object)  # (3, 3)
        return (
            g[0, 0] * (g[1, 1] * g[2, 2] - g[1, 2] * g[2, 1])
            - g[0, 1] * (g[1, 0] * g[2, 2] - g[1, 2] * g[2, 0])
            + g[0, 2] * (g[1, 0] * g[2, 1] - g[1, 1] * g[2, 0])
        )
    assert gram_det(reduced) == gram_det(basis)
    # Lovasz condition on the reduced basis, by Gram-Schmidt in floats
    b = np.array(reduced, dtype=float)  # (3, 4)
    star = []
    for row in b:
        v = row.copy()
        for s in star:
            v -= (row @ s) / (s @ s) * s
        star.append(v)
    for k in range(1, 3):
        mu = (b[k] @ star[k - 1]) / (star[k - 1] @ star[k - 1])
        assert star[k] @ star[k] >= (0.75 - mu * mu) * (star[k - 1] @ star[k - 1]) - 1e-6


def test_two_adic_positive_and_negative() -> None:
    bits = 256
    root = w.two_adic_root([-4, 1, 1], 0, bits)
    assert (root * root + root - 4) % (1 << bits) == 0
    cube = w.two_adic_root([-9, 0, 0, 1], 1, bits)
    assert (cube**3 - 9) % (1 << bits) == 0
    reduced = w.lll(w.two_adic_lattice(root, 2, bits))
    best = min(reduced, key=lambda row: sum(x * x for x in row))
    assert sorted(abs(x) for x in best) == [1, 1, 4]
    first, _ = w.relation_bound(w.two_adic_lattice(w.column_integer(center_column(bits)), 3, bits))
    assert first > bits / 4 - 4


def test_real_lattice_finds_cube_root() -> None:
    bits = 300
    numerator = w._cube_root_scaled(2, bits) - (1 << bits)  # 2^(1/3) - 1: r^3 + 3r^2 + 3r - 1 = 0
    assert abs(numerator / 2**bits - (2 ** (1 / 3) - 1)) < 1e-12
    reduced = w.lll(w.real_lattice(numerator, 3, bits))
    best = min(reduced, key=lambda row: sum(x * x for x in row))
    assert [abs(x) for x in best[:4]] == [1, 3, 3, 1]


def test_scaled_constants() -> None:
    bits = 80
    assert abs(w.pi_scaled(bits) / 2**bits - math.pi) < 1e-15
    assert abs(w.e_scaled(bits) / 2**bits - math.e) < 1e-15
    assert abs(w.log2_scaled(bits) / 2**bits - math.log(2)) < 1e-15


def test_cut_rank_matches_direct_matrix() -> None:
    t = 4
    table = w.cone_table(t)  # (2^9,)
    assert np.array_equal(table, center_truth_table(t))
    for left in range(1, 2 * t + 1):
        matrix = table.reshape(1 << (2 * t + 1 - left), 1 << left)  # (rows, columns)
        assert w.cut_rank(table, t, left) == numpy_rank(matrix)
        assert w.cut_rank(table, t, left) <= w.distinct_lines(table, t, left)


def test_rule_cone_table_and_control() -> None:
    t = 4
    assert np.array_equal(w.rule_cone_table(t, 30), w.cone_table(t))
    # Rule 150 is linear: c_t is a parity, of rank at most 2 at every cut
    assert max(w.rank_profile(w.rule_cone_table(t, 150), t)) <= 2
    control = w.structured_control(t, 0)  # (2^9,)
    assert all(w.cut_rank(control, t, a) <= w.cap(t, a) for a in range(1, 2 * t + 1))
    assert [w.cut_rank(w.cone_table(6), 6, a) for a in range(1, 5)] == [w.left_cut_formula(a) for a in range(1, 5)]
