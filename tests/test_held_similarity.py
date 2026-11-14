"""The held map's similarities, its nonaffinity on classes, and the iterated function system of K, against direct
stepping of integers."""

from __future__ import annotations

import random

from computations.held_shift import forced_halves, held, itinerary
from computations.held_similarity import (affinity_defect, boundaryless, boundaryless_power, held_power,
                                          ifs_point, inverse_branch, similarity_holds, survivors_below,
                                          survivors_with_bits, valuation)


def test_boundaryless_is_held_far_from_zero() -> None:
    for x in range(1, 200):
        for m in range(1, 6):
            assert held(x << m) == boundaryless(x) << (m - 1)


def test_held_power_exact() -> None:
    rng = random.Random(1)
    for _ in range(200):
        U, n, bits = rng.getrandbits(40), rng.randrange(1, 8), rng.randrange(1, 20)
        V = U
        for _ in range(n):
            V = held(V)
        assert held_power(U, n, bits) == V % (1 << bits)  # U is a finite integer: exact


def test_similarity_by_brute_force() -> None:
    # every pair below 2^8 in the same class modulo 2^n, with the images computed exactly on integers
    for n in range(1, 4):
        for U in range(1 << 8):
            for V in range(U + 1, 1 << 8):
                if (U - V) % (1 << n):
                    continue
                k = valuation(U - V, 64)
                a, b = U, V
                for _ in range(n):
                    a, b = held(a), held(b)
                assert valuation(a - b, 64) == k - n
    assert similarity_holds(5, 30, 300, seed=3)


def test_inverse_branch_is_inverse() -> None:
    rng = random.Random(2)
    for _ in range(300):
        U = rng.getrandbits(30)
        bits = 24
        assert inverse_branch(held(U), U & 1, bits) == U % (1 << bits)


def test_no_class_is_affine() -> None:
    for n in range(1, 6):
        e1, e3 = boundaryless_power(1, n), boundaryless_power(3, n)
        assert e3 < (1 << (2 * n + 2)) <= 3 * e1  # the size argument of the proof
        for k in range(5):
            for a in range(1 << k):
                m, d1, d3 = affinity_defect(n, k, a)
                assert d1 == e1 << (m - n) and d3 == e3 << (m - n)
                assert d3 != 3 * d1


def test_ifs_gives_the_points_of_k() -> None:
    depth = 12
    residues = {int(r) for r in forced_halves(depth)}  # every residue of K modulo 2^12
    found = set()
    for word in range(1 << (depth // 2)):
        beta = [(word >> s) & 1 for s in range(depth // 2)]
        U = ifs_point(beta)
        assert itinerary(U, depth // 2) == beta
        found.add(U % (1 << depth))
    assert found == residues


def test_survivor_density_is_exact() -> None:
    # the density 2^(-ceil(T / 2)) of the integers passing the odd steps up to T, for T < N
    for N in range(1, 10):
        for T in range(1, N):
            assert survivors_below(N, T) == 1 << (N - (T + 1) // 2)


def test_survivors_with_exactly_m_bits() -> None:
    # exact for T <= M - 2; at T = M - 1 the power of 2 holds only for odd M (the top bit is already 1)
    def passes(U: int, T: int) -> bool:
        return all(held_power(U, t, 1) & 1 for t in range(1, T + 1, 2))
    for M in range(2, 11):
        for T in range(1, M):
            assert survivors_with_bits(M, T) == sum(passes(U, T) for U in range(1 << (M - 1), 1 << M))
        for T in range(1, M - 1):
            assert survivors_with_bits(M, T) == 1 << (M - 1 - (T + 1) // 2)
        if M % 2 == 1:
            assert survivors_with_bits(M, M - 1) == 1 << ((M - 1) // 2)
    assert [survivors_with_bits(M, M - 1) for M in (4, 6, 8, 10)] == [1, 5, 5, 19]
