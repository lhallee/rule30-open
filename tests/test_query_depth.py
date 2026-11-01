"""Query depth of the cone function: exact depths, the top real coefficient, and the restriction certificates."""

from __future__ import annotations

import itertools
from functools import lru_cache

import numpy as np

from computations import query_depth as qd
from computations.cone_screening import cone_table


def plain_center(cells: tuple[int, ...]) -> int:
    """c_t from the 2t + 1 cone cells by running the rule on a list, one cell at a time."""
    row = list(cells)  # (2t + 1,)
    while len(row) > 1:
        row = [row[i - 1] ^ (row[i] | row[i + 1]) for i in range(1, len(row) - 1)]  # (len - 2,)
    return row[0]


def tree_depth(f: dict[tuple[int, ...], int], n: int) -> int:
    """The least decision-tree depth of f by plain recursion over partial assignments (None = free)."""

    @lru_cache(maxsize=None)
    def depth(partial: tuple[int | None, ...]) -> int:
        free = [i for i, v in enumerate(partial) if v is None]
        values = {f[tuple(int(b) for b in full)] for full in completions(partial, free)}
        if len(values) == 1:
            return 0
        return 1 + min(max(depth(partial[:i] + (b,) + partial[i + 1:]) for b in (0, 1)) for i in free)

    def completions(partial: tuple[int | None, ...], free: list[int]) -> list[tuple[int, ...]]:
        out = []
        for bits in itertools.product((0, 1), repeat=len(free)):
            full = list(partial)
            for i, b in zip(free, bits):
                full[i] = b
            out.append(tuple(full))
        return out

    return depth((None,) * n)


def test_exact_depth_against_recursion() -> None:
    """The subcube program agrees with a plain recursion on Rule 30 (t <= 2) and on random functions."""
    rng = np.random.default_rng(1)
    for t in (1, 2):
        n = 2 * t + 1
        f = {cells: plain_center(cells) for cells in itertools.product((0, 1), repeat=n)}
        assert qd.exact_depth(cone_table(t), n) == tree_depth(f, n) == n
    for _ in range(20):
        n = int(rng.integers(1, 5))
        table = rng.integers(0, 2, 1 << n).astype(np.uint8)  # (2^n,)
        f = {cells: int(table[sum(b << i for i, b in enumerate(cells))])
             for cells in itertools.product((0, 1), repeat=n)}
        assert qd.exact_depth(table, n) == tree_depth(f, n)


def test_rule30_evasive_and_rule90_sparse() -> None:
    """Rule 30 needs every cone cell for t <= 4; Rule 90 needs 2^popcount(t)."""
    for t in range(1, 5):
        n = 2 * t + 1
        assert qd.exact_depth(cone_table(t), n) == n
        assert qd.exact_depth(qd.rule90_table(t), n) == 2 ** bin(t).count("1")


def test_top_coefficient_against_direct_sum() -> None:
    """mu(c_t) from the bit-sliced chunks, for several chunk sizes, equals the direct signed sum over the cone."""
    for t in range(1, 9):
        direct = qd.signed_sum(cone_table(t), 2 * t + 1)
        for inner in (6, 9, 24):
            nu, _ = qd.subcube_sums(t, {}, inner)
            assert 2 * nu == direct


def test_restricted_sums_against_direct() -> None:
    """The restricted sums of g from the chunks equal those of the table with x_{-t} = 0, with and without fixings."""
    for t in (3, 4, 5):
        g = cone_table(t)[0::2]  # (2^(2t),)
        assert np.array_equal(qd.subcube_sums(t, {}, 7)[1], qd.restricted_sums(g, 2 * t))
        n = 2 * t
        for fixed in ({0: 1}, {n - 1: 0}, {1: 0, n - 2: 1}):
            index = np.arange(1 << n)  # (2^n,)
            keep = np.ones(1 << n, dtype=bool)  # (2^n,)
            for k, b in fixed.items():
                keep &= ((index >> k) & 1) == b
            free = [k for k in range(n) if k not in fixed]
            nu, sums = qd.subcube_sums(t, fixed, 7)
            sign = -1 if sum(fixed.values()) % 2 else 1
            parity = np.array([bin(int(i)).count("1") % 2 for i in index])  # (2^n,)
            weights = (1 - 2 * parity) * g.astype(np.int64)  # (2^n,)
            assert nu == sign * int(weights[keep].sum())
            for k in free:
                for b in (0, 1):
                    part = keep & (((index >> k) & 1) == b)
                    assert sums[k, b] == sign * (-1) ** b * int(weights[part].sum())


def test_certificates_small() -> None:
    """Every certificate found for t <= 6 agrees with the exact depth 2t + 1."""
    for t in range(1, 7):
        mu, level, _ = qd.certificate(t, inner=10)
        assert level == 0 and mu == qd.signed_sum(cone_table(t), 2 * t + 1) != 0


def test_evasive_recursion_against_exact_depth() -> None:
    """At t = 3, wherever a certificate of level 1 or 2 holds for g with two cells fixed and top coefficient 0, the
    exact depth of that restriction is its number of free cells; the recursion is exercised at least once."""
    t, n = 3, 6
    g = cone_table(t)[0::2]  # (2^6,), the rows with x_{-t} = 0
    index = np.arange(1 << n)  # (2^6,)
    used = 0
    for ks in itertools.combinations(range(n), 2):
        for bs in itertools.product((0, 1), repeat=2):
            fixed = dict(zip(ks, bs))
            if qd.subcube_sums(t, fixed, 7)[0] != 0 or not qd.evasive(t, fixed, 2, 7):
                continue
            keep = np.ones(1 << n, dtype=bool)  # (2^6,)
            for k, b in fixed.items():
                keep &= ((index >> k) & 1) == b
            free = [k for k in range(n) if k not in fixed]
            packed = sum(((index >> k) & 1) << pos for pos, k in enumerate(free))  # (2^6,)
            table = g[keep][np.argsort(packed[keep])]  # (2^4,)
            assert qd.exact_depth(table, len(free)) == len(free)
            used += 1
    assert used > 0
