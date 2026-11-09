"""Tests for computations/right_edge_runs.py, each against an independent computation: Python integers stepped one at
a time, Phi inverted bit by bit, the level lifting and full Mahler transform of computations/two_index.py, a direct run
of the rule table, and binomial coefficients."""

from __future__ import annotations

import functools
import math

import numpy as np

import computations.right_edge_runs as rer

from computations.two_index import (cycle_lengths, diagonal_array, doubling_levels, longest_flat_run,  # noqa: E402
                                    mahler_degree, white_runs, white_runs_from_cycles)


@functools.cache
def _small_runs() -> rer.Runs:
    """The C helper's run to time 2^16, shared by the tests."""
    return rer.runs(16)


@functools.cache
def _h(tau: int, bits: int = 64) -> int:
    """h(tau) modulo 2^bits by Python integers, backward by inverting Phi bit by bit."""
    return rer.orbit(tau, bits)


def test_runs_against_python_and_level_lifting() -> None:
    """The C helper's rows at 2^k and 2^16 - 2^k equal those of Python integers stepped one at a time, its white runs
    equal the white runs read off the cycle lengths of level lifting (and the unbounded integer rows of two_index for
    k <= 12), and the cycle exponents read off the white runs equal the cycle lengths."""
    c, py = _small_runs(), rer.runs_python(16)
    assert c.white == py.white and c.rows == py.rows and c.back == py.back
    assert c.white[:13] == white_runs(12)
    lengths = cycle_lengths(42)[0]
    assert c.white == white_runs_from_cycles(lengths)[:17]
    exps = rer.cycle_exponents(c.white)
    assert len(exps) == c.white[-1] + 1 == 41
    assert [1 << a for a in exps] == lengths[:41]
    assert doubling_levels(lengths[:41]) == [2, 4, 5, 7, 8, 10, 16, 17, 25, 26, 28, 30, 35, 37, 38, 40]
    assert rer.longest_flat_stretch(lengths[:41]) == (longest_flat_run(lengths[:41]), 18) == (7, 18)
    assert c.stalls == [2, 1, 2, 1, 2, 6, 1, 8, 1, 2, 2, 5, 2, 1, 2, 2]


def test_agreement_identity() -> None:
    """Theorem C: the backward rows of the C helper are h(-2^k) inverted bit by bit,
    v_2(h(2^k) - h(-2^k)) = J_(k+1) + 1, and v_2(h(a) - h(b)) = J_(v_2(a - b)) + 1 for every pair of times in
    [-24, 24]."""
    c = _small_runs()
    bits = c.white[-1] + 1  # 41: the back rows are h(-2^k) modulo 2^41
    for k in range(9):
        assert c.back[k] % (1 << bits) == _h(-(1 << k), bits)
    assert c.agreement() == [c.white[k + 1] + 1 for k in range(15)]
    for a in range(-24, 25):
        for b in range(-24, a):
            assert rer.v2(_h(a) - _h(b)) == c.white[rer.v2(a - b)] + 1


def _phi_k_at(k: int, nu: int, x: int, width: int) -> int:
    """phi_k(x) modulo 2^width by Python integers: (Phi^(2^k)(1 + 2^nu x) - 1) / 2^nu."""
    mask = (1 << (nu + width)) - 1
    z = (1 + (x << nu)) & mask
    for _ in range(1 << k):
        z = rer.phi(z, mask)
    return ((z - 1) >> nu) & ((1 << width) - 1)


def test_phi_and_renormalization() -> None:
    """phi_k modulo 16 from the C helper equals Python integers; v_2(phi_k^2(0)) = d_k; and the renormalization
    phi_(k+1)(y) = 2^(-d_k) phi_k^2(2^(d_k) y) holds modulo 16 for k < 10."""
    table = rer.phis(10, 4)
    stalls = _small_runs().stalls
    for k in range(11):
        assert table[k] == rer.phi_python(k, 4)
    for k in range(10):
        nu, d = table[k][0], stalls[k]
        assert table[k + 1][0] == nu + d
        assert rer.v2(_phi_k_at(k, nu, _phi_k_at(k, nu, 0, d + 4), d + 4), 99) == d
        for y in range(16):
            twice = _phi_k_at(k, nu, _phi_k_at(k, nu, y << d, d + 4), d + 4)
            assert twice % (1 << d) == 0 and (twice >> d) == table[k + 1][1][y]
    assert not any(rer.is_affine(v, 4) for _, v in table)
    assert rer.is_affine([(5 * y + 3) % 16 for y in range(16)], 4)


def test_lift_and_mahler_top() -> None:
    """Level lifting equals the diagonals of two_index, each array is the least period, and the top-bit decomposition
    gives the degree of the full Mobius transform, on the diagonals and on random words."""
    lengths, diagonals = cycle_lengths(26)
    lifted = list(rer.lift(26))
    assert [d.size for _, d, _ in lifted] == lengths
    for (j, d, _), ref in zip(lifted, diagonals):
        assert np.array_equal(d, ref) and rer.least_period(d) == d.size
        assert rer.mahler_top(d) == mahler_degree(ref)
    rng = np.random.default_rng(3)
    for e in range(9):
        for _ in range(20):
            f = (rng.random(1 << e) < 0.3).astype(np.uint8)  # (2^e,)
            assert rer.mahler_top(f) == mahler_degree(f)
    g = rng.integers(0, 2, size=64).astype(np.uint8)  # (64,)
    s = rer.antiderivative(g)  # (64,)
    assert [int(s[t]) for t in range(64)] == [sum(int(x) for x in g[:t]) % 2 for t in range(64)]


def test_stall_laws() -> None:
    """The laws hold at every diagonal j <= 46 (period 2^18); the degrees and doublings agree with two_index; Theorem
    A(ii)
    recomputed from those degrees; and the candidates fail where the entry says."""
    laws = rer.stall_laws(47, 18)
    assert len(laws.diagonals) == 47
    for name in rer.LAW_NAMES:
        assert laws.checks[name].count > 0 and laws.checks[name].failures == [], name
    lengths, diagonals = cycle_lengths(26)
    degrees = [mahler_degree(d) for d in diagonals]
    assert [x.top for x in laws.diagonals[:26]] == degrees
    assert [x.period for x in laws.diagonals[:26]] == lengths
    for n in range(2, 25):
        if lengths[n] == 2 * lengths[n - 1] and lengths[n + 1] == lengths[n]:
            assert degrees[n + 1] == lengths[n] // 2 + degrees[n - 1] + 1
    assert laws.or_failures == [(2, True), (12, True), (13, True), (14, True), (19, True), (21, True), (22, True),
                                (23, True), (32, True), (33, True), (46, False)]
    assert laws.checks["max inequality"].failures == [2, 12, 13, 14, 19, 21, 22, 32, 33, 46]
    assert laws.second_diagonal == [(11, 1), (18, 2), (31, 1), (45, 2)]
    for stall in laws.stalls:
        if stall.length is not None and stall.predicted != "?":
            assert stall.predicted == (str(stall.length) if stall.length <= 2 else ">= 3")


def test_weight_features_and_rules() -> None:
    """The weights against sums over one period cell by cell; at a diagonal j that does not double, |g_j| = 2 |R_j g_j|
    and
    |R_j| has the parity of the black input cells at odd times; and the defining identity (the input's weight parity)
    among the rules found on 3 <= j <= 28."""
    lifted = [(d, doubled) for _, d, doubled in rer.lift(16)]
    for j in range(3, 16):
        (r0, doubled), (r1, _), (r2, _) = lifted[j], lifted[j - 1], lifted[j - 2]
        size = r0.size
        a = [int(r0[t]) for t in range(size)]
        b = [int(r1[t % r1.size]) for t in range(size)]
        c = [int(r2[t % r2.size]) for t in range(size)]
        o = [t % 2 for t in range(size)]
        direct = [sum(a), sum(b), sum(x * y for x, y in zip(a, b)), sum(x * y for x, y in zip(a, c)),
                  sum(x * y for x, y in zip(b, c)), sum(x * y * z for x, y, z in zip(a, b, c)),
                  sum(x * y for x, y in zip(a, o)), sum(x * y for x, y in zip(b, o)),
                  sum(x * y * z for x, y, z in zip(a, b, o))]
        assert rer.weight_features(r0, r1, r2) == direct
        if not doubled:
            g = [x | y for x, y in zip(b, c)]
            assert sum(g) == 2 * sum(x * y for x, y in zip(a, g))
            assert sum(a) % 2 == sum(g[1::2]) % 2
    tested, rules = rer.weight_rules(30, 20)
    assert tested == list(range(3, 29))
    assert ("|R_j| mod 2", "|R_j-1| mod 2", "|R_j R_j-1| mod 2") in rules


def test_barriers() -> None:
    """Phi swaps 1/3 and -1/3, whose cycles modulo 2^n have length 2 for n >= 2; the lifted diagonals of Rules 150 and
    90 equal a direct run of their rule tables and the binomial formulas, with K_j = j for Rule 150, K_(2m) = m for
    Rule 90, and white runs 2^k - 1 and 2^(k+1) - 1."""
    assert rer.seeds_swap(128) and rer.seeds_swap(16)
    assert rer.seed_cycle_lengths(pow(3, -1, 1 << 10), 10) == [1] + [2] * 9
    for rule, gate in ((150, "xor"), (90, "older")):
        array = diagonal_array(rule, 32, 64)  # (32, 64)
        for j, d, _ in rer.lift(32, 40, gate):
            assert np.array_equal(array[j], np.resize(d, 64))
    periods, tops = rer.linear_tops(40, "xor")
    assert tops == list(range(40)) and periods == [1 << j.bit_length() for j in range(40)]
    assert rer.white_runs_of(periods, 4) == [0, 1, 3, 7, 15]
    for j, d, _ in rer.lift(12, 40, "xor"):
        assert [int(d[t % d.size]) for t in range(40)] == [
            sum(math.comb(t, i) * math.comb(i, j - i) for i in range(j + 1)) % 2 for t in range(40)]
    periods, tops = rer.linear_tops(40, "older")
    assert tops == [j // 2 if j % 2 == 0 else -1 for j in range(40)]
    assert rer.white_runs_of(periods, 4) == [1, 3, 7, 15, 31]
