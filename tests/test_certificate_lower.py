"""The combs, maximal monomials, windows and capped searches of certificate_lower against plain enumerations."""

from __future__ import annotations

import itertools
from math import comb

import numpy as np

from computations import certificate_lower as cl
from computations import min_certificate as mc


def plain_table(t: int) -> np.ndarray:
    """c_t at every row of the cone, by running Rule 30 on a list of cells (bit i of the index is x_{-t+i})."""
    n = 2 * t + 1
    out = np.zeros(1 << n, dtype=np.uint8)  # (2^n,)
    for index in range(1 << n):
        row = [(index >> i) & 1 for i in range(n)]  # (n,)
        while len(row) > 1:
            row = [row[i - 1] ^ (row[i] | row[i + 1]) for i in range(1, len(row) - 1)]  # (len - 2,)
        out[index] = row[0]
    return out


def test_comb_derivative_is_binomial() -> None:
    """The mixed derivative over the comb B_j(t), summed over the flips of a plain table, is C(t, j + 1) mod 2."""
    for t in (2, 3, 4):
        table = plain_table(t)
        for j in range(t):
            cells = cl.comb_cells(t, j)
            if cells[-1] > t:
                break
            values = set()
            for index in range(1 << (2 * t + 1)):
                total = 0
                for flips in itertools.product((0, 1), repeat=len(cells)):
                    total ^= int(table[index ^ sum(f << (c + t) for f, c in zip(flips, cells))])
                values.add(total)
            assert values == {comb(t, j + 1) % 2} == cl.comb_derivative(t, j)


def test_maximal_monomials_and_hitting_number() -> None:
    """The maximal monomials of c_3 from the definition of the coefficients (the xor over the subsets of the
    monomial), and the hitting number from a listing of all sets of cells."""
    t, n = 3, 7
    table = plain_table(t)
    coef = {s: 0 for s in range(1 << n)}
    for s in range(1 << n):
        sub = s
        while True:
            coef[s] ^= int(table[sub])
            if sub == 0:
                break
            sub = (sub - 1) & s
    monomials = [s for s in range(1, 1 << n) if coef[s]]
    maximal = [s for s in monomials if not any(o != s and o & s == s for o in monomials)]
    assert sorted(cl.maximal_monomials(t)) == sorted(maximal)
    least = min(len(c) for size in range(1, n + 1) for c in itertools.combinations(range(n), size)
                if all(m & sum(1 << i for i in c) for m in maximal))
    assert cl.hitting_number(t)[0] == least == 3


def test_window_lengths_and_bound() -> None:
    """W(4, k) from a listing of every assignment outside the window, and the window bound below m(4)."""
    t, n = 4, 9
    table = plain_table(t)
    expected: list[int | None] = []
    for k in range(1, 2 * t + 1):
        found = None
        for length in range(1, n - k + 1):
            window = range(k, k + length)
            outside = [i for i in range(n) if i not in window and i != 0]
            screened = any(
                len({int(table[base | sum(b << i for b, i in zip(inner, window))])
                     for inner in itertools.product((0, 1), repeat=length)}) == 1
                for base in (sum(b << i for b, i in zip(bits, outside))
                             for bits in itertools.product((0, 1), repeat=len(outside))))
            if not screened:
                found = length
                break
        expected.append(found)
    lengths = cl.window_lengths(t)
    assert lengths == expected
    assert cl.window_bound(lengths) <= mc.least_constant_subcube(t)[0]


def test_capped_search_and_right_free() -> None:
    """The capped search agrees with m(5) = 5, and the least subcubes with x_2 .. x_t free agree with a listing of
    partial rows of x_{-t} .. x_1 at t = 5."""
    assert cl.no_small_subcube(5, 3, split=2, progress=False)
    assert not cl.no_small_subcube(5, 4, split=2, progress=False)
    t, r = 5, 1
    n = 2 * t + 1
    table = plain_table(t)
    index = np.arange(1 << n)  # (2^n,)
    best = None
    for partial in itertools.product((0, 1, None), repeat=t + r + 1):
        match = np.ones(1 << n, dtype=bool)  # (2^n,)
        for i, v in enumerate(partial):
            if v is not None:
                match &= ((index >> i) & 1) == v
        if table[match].min() == table[match].max():
            size = sum(v is not None for v in partial)
            best = size if best is None else min(best, size)
    least, rows = cl.right_free_least(t, r, inner=8, progress=False)
    assert least == best
    for row in rows:
        match = np.ones(1 << n, dtype=bool)  # (2^n,)
        for i, ch in enumerate(row):
            if ch != "*":
                match &= ((index >> i) & 1) == int(ch)
        assert table[match].min() == table[match].max() and sum(ch != "*" for ch in row) == least


def test_stripe_grows() -> None:
    """StripeGrowth's step, by a direct run: with the odd stripe on -1 .. -10, after nine steps cells 0 and 1 are
    white and black for all 2^11 values of the cells 0 .. 10 that reach them; the far stripe fixes c_18 on 2,000
    sampled completions (the reproduce command runs all 2^21), and `far_stripe_values` agrees at small t."""
    right = np.arange(1 << 11)  # (2^11,)
    row = [np.full(1 << 11, j % 2, dtype=np.uint8) for j in range(10, 0, -1)]  # cells -10 .. -1
    row += [((right >> i) & 1).astype(np.uint8) for i in range(11)]  # cells 0 .. 10
    for _ in range(9):
        row = [row[i - 1] ^ (row[i] | row[i + 1]) for i in range(1, len(row) - 1)]  # (len - 2) x (2^11,)
    assert set(row[10 - 9].tolist()) == {0} and set(row[11 - 9].tolist()) == {1}
    rng = np.random.default_rng(0)
    rows = rng.integers(0, 2, size=(2000, 37), dtype=np.uint8)  # (2000, 2t + 1), cells -18 .. 18
    for i in range(3, 19):
        rows[:, 18 - i] = i % 2
    for _ in range(18):
        rows = rows[:, :-2] ^ (rows[:, 1:-1] | rows[:, 2:])  # (2000, len - 2)
    assert set(rows[:, 0].tolist()) == {0}
    assert cl.far_stripe_values(9, 0) == {0} and cl.far_stripe_values(10, 1) == {0, 1}
