"""Adversary routes for the query depth: the C sums, the OR of the corner, NPN equivalence and covering pairs."""

from __future__ import annotations

import itertools

import numpy as np

from computations import query_adversary as qa
from computations import query_depth as qd
from computations.cone_screening import cone_table


def plain_center(cells: tuple[int, ...]) -> int:
    """c_t from the 2t + 1 cone cells by running the rule on a list."""
    row = list(cells)  # (2t + 1,)
    while len(row) > 1:
        row = [row[i - 1] ^ (row[i] | row[i + 1]) for i in range(1, len(row) - 1)]  # (len - 2,)
    return row[0]


def test_kernel_against_subcube_sums() -> None:
    """The C program gives the sums of `query_depth.subcube_sums`, with and without fixed cells inside and outside the
    bit-sliced block."""
    for t, fixed in ((5, {}), (6, {}), (6, {0: 1, 7: 0, 11: 1}), (7, {3: 1, 12: 1, 13: 0})):
        nu, sums = qa.kernel_sums(t, fixed, threads=2, split=3)
        nu_ref, sums_ref = qd.subcube_sums(t, fixed)
        assert nu == nu_ref
        assert (sums == sums_ref).all()


def test_corner_or_against_plain_runs() -> None:
    """The center sees x_{t-1}, x_t only through their OR, by running the rule on every row for t <= 3, and on the
    truth table for t <= 6."""
    for t in range(1, 4):
        for rest in itertools.product((0, 1), repeat=2 * t - 1):
            values = {plain_center(rest + pair) for pair in ((0, 1), (1, 0), (1, 1))}
            assert len(values) == 1
    assert all(qa.corner_or_holds(t) for t in range(1, 7))
    for t in (5, 6):
        nu, left, right = qa.corner_restrictions(t)
        assert left == right == (nu, 0)


def test_npn_equivalence() -> None:
    """A random function with its cells permuted and negated and its value negated is found equivalent, OR is
    equivalent to AND, and a single cell is not."""
    rng = np.random.default_rng(3)
    n = 5
    index = np.arange(1 << n)  # (2^n,)
    g = rng.integers(0, 2, 1 << n).astype(np.uint8)  # (2^n,)
    perm = rng.permutation(n)
    neg = rng.integers(0, 2, n)
    y = np.zeros(1 << n, dtype=np.int64)  # (2^n,)
    for k in range(n):
        y |= (((index >> k) & 1) ^ neg[k]) << perm[k]
    f = g[y] ^ np.uint8(1)  # (2^n,)
    found = qa.npn_equivalent(f, g, n)
    assert found is not None
    p, s, out = found
    z = np.zeros(1 << n, dtype=np.int64)  # (2^n,)
    for k in range(n):
        z |= (((index >> k) & 1) ^ s[k]) << p[k]
    assert (f == (g[z] ^ np.uint8(out))).all()
    conj = (index == (1 << n) - 1).astype(np.uint8)  # (2^n,), the AND of the five cells
    disj = (index != 0).astype(np.uint8)  # (2^n,), the OR, its dual
    assert qa.npn_equivalent(disj, conj, n) is not None
    assert qa.npn_equivalent((index & 1).astype(np.uint8), conj, n) is None


def plain_depth(table: tuple[int, ...], n: int) -> int:
    """The least decision-tree depth by plain recursion: 0 if constant, else 1 + min over cells of the larger half."""
    if len(set(table)) == 1:
        return 0
    best = n
    for i in range(n):
        halves = [tuple(v for u, v in enumerate(table) if (u >> i) & 1 == b) for b in (0, 1)]
        best = min(best, 1 + max(plain_depth(h, n - 1) for h in halves))
    return best


def test_restriction_isomorphisms_small() -> None:
    """Route (i) for t = 1, 2: ten two-cell restrictions of c_2 are equivalent to c_1 and none of c_3 to c_2; at t = 1
    the count of restrictions that need all three cells agrees with a plain recursion on rows run by the rule."""
    total, ev, found = qa.restriction_isomorphisms(1)
    assert (total, ev, len(found)) == (40, 25, 10)
    plain = 0
    for i, j in itertools.combinations(range(5), 2):
        for a, b in itertools.product((0, 1), repeat=2):
            rows = [r for r in itertools.product((0, 1), repeat=5) if r[i] == a and r[j] == b]
            table = tuple(plain_center(r) for r in sorted(rows, key=lambda r: sum(
                v << p for p, v in enumerate(c for k, c in enumerate(r) if k not in (i, j)))))
            plain += plain_depth(table, 3) == 3
    assert plain == ev
    total, ev, found = qa.restriction_isomorphisms(2)
    assert (total, ev, found) == (84, 49, [])


def test_covering_pairs_mod_four() -> None:
    """nu(g_t) = 2 P (mod 4) with nu from the direct signed sum, and P equal to a plain count over pairs of monomials
    at t = 2."""
    for t in range(2, 7):
        nu = qd.signed_sum(cone_table(t), 2 * t + 1) // 2
        assert nu % 4 == 2 * qa.covering_pairs(t) % 4
    n = 4
    g = cone_table(2)[0::2]  # (16,)
    monos = [s for s in range(1 << n)
             if sum(int(g[u]) for u in range(1 << n) if u & ~s == 0) % 2]  # Moebius sum over the subsets of s
    plain = sum(1 for a, b in itertools.combinations(monos, 2) if a | b == (1 << n) - 1)
    assert qa.covering_pairs(2) == plain
