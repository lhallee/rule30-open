"""The left-cut rank: the windowed rows through Phi, the full and packed ranks, the stripe basis and the closure."""

from __future__ import annotations

import numpy as np

from computations import cone_screening as cs
from computations import left_cut_rank as lr


def plain_center(cells: list[int]) -> int:
    """c_t from the 2t + 1 cone cells x_{-t} .. x_t by running the rule on a list."""
    row = list(cells)  # (2t + 1,)
    while len(row) > 1:
        row = [row[i - 1] ^ (row[i] | row[i + 1]) for i in range(1, len(row) - 1)]  # (len - 2,)
    return row[0]


def test_window_identity() -> None:
    """On rows white right of the window, c_t is the top bit of Phi^t: against the truth table for t <= 6 and every
    window inside the cone, and against plain runs at t = 9."""
    for t in (3, 5, 6):
        table = cs.cone_table(t)  # (2^(2t+1),)
        for a in range(1, t + 1):
            for length in range(1, 2 * t + 2 - a):
                values = lr.window_values(a, length, [t])[t]  # (2^a, 2^length)
                expected = table[: 1 << (a + length)].reshape(1 << length, 1 << a).T  # (2^a, 2^length)
                assert np.array_equal(values, expected)
    rng = np.random.default_rng(0)
    values = lr.window_values(4, 6, [9])[9]  # (16, 64)
    for _ in range(40):
        u, w = int(rng.integers(16)), int(rng.integers(64))
        cells = [(u >> i) & 1 for i in range(4)] + [(w >> i) & 1 for i in range(6)] + [0] * 9  # (19,)
        assert values[u, w] == plain_center(cells)
        n = lr.window_number(u, w, 4, 6)
        assert all((n >> (9 - i)) & 1 == cells[i] for i in range(10))


def test_ranks_against_counts() -> None:
    """rank(t, a) is at most N_L(t, a) of `cone_screening`, the windowed rank at most rank(t, a), the packed table
    gives the same ranks, and rank(t, a) = rho(a) for a <= t - 2 at t = 5, 6."""
    for t in (5, 6):
        table = cs.cone_table(t)  # (2^(2t+1),)
        counts = cs.left_counts(t)
        packed = lr.packed_center(t)  # (2^(2t+1) / 64,)
        for a in range(1, t + 1):
            r = lr.full_rank(t, a, table)
            assert r <= counts[a - 1]
            assert r == lr.packed_rank(packed, t, a)
            if a <= t - 2:
                assert r == lr.rho(a)
            if 2 * a + 2 <= 2 * t + 1:
                assert lr.window_rank(a, a + 2, [t])[t] <= r


def test_stripe_basis() -> None:
    """The stripe basis has rho(a) members, is closed under turning black cells white, and its rows are independent
    at t = 6 for a <= 4 (the rows of x_{-t} flipped are complements, a second check of the rank)."""
    for a in range(1, 11):
        basis = lr.stripe_basis(a)
        assert len(basis) == lr.rho(a)
        members = set(basis)
        assert all(u & ~(1 << i) in members for u in basis for i in range(a))
    assert lr.stripe_basis(4) == [0, 1, 2, 4, 8, 10, 12]  # 0000 1000 0100 0010 0001 0101 0011
    table = cs.cone_table(6)  # (2^13,)
    for a in range(1, 5):
        matrix = lr.cut_matrix(table, 6, a)  # (2^a, 2^(13-a))
        assert np.array_equal(matrix[1], 1 - matrix[0])
        rows = lr.packed_rows(matrix)
        assert lr.subset_rank(rows, lr.stripe_basis(a)) == lr.rho(a)


def test_closure_against_products() -> None:
    """The closure dimension equals the span of the top bits of every product of at most 8 section maps, for a <= 4,
    and bounds rank(6, a)."""
    table = cs.cone_table(6)  # (2^13,)
    for a in range(1, 5):
        maps = lr.section_maps(a)
        u = np.arange(1 << a)  # (2^a,)
        layer = {tuple(u.tolist())}
        products = set(layer)
        for _ in range(8):
            layer = {tuple(np.asarray(p)[h].tolist()) for p in layer for h in maps}
            products |= layer
        tops = np.array([[(v >> (a - 1)) & 1 for v in p] for p in products], dtype=np.uint8)  # (count, 2^a)
        assert lr.closure_dimension(a) == lr.rows_rank(tops)
        assert lr.full_rank(6, a, table) <= lr.closure_dimension(a)
    assert [lr.closure_dimension(a) for a in range(1, 7)] == [2, 3, 5, 8, 14, 25]


def test_window_two_pow_and_lift() -> None:
    """At t = 2^j the window of j + 1 cells reads x_{-t} (`center_two_pow`), so its rank is 1; and the lift of the
    greedy family reaches rho(a) for a = 3, 4."""
    for a, length in ((1, 3), (2, 2), (3, 1)):
        values = lr.window_values(a, length, [8])[8]  # (2^a, 2^length)
        u = np.arange(1 << a)  # (2^a,)
        assert np.array_equal(values, np.broadcast_to((u & 1)[:, None], values.shape))
        assert lr.window_floor(a, length, 5)[0] == 1
    for a in (3, 4):
        result = lr.lift_test(a, a + 2, span=4)
        assert result["uniform"] == lr.rho(a) and result["base"] == lr.rho(a - 1)
