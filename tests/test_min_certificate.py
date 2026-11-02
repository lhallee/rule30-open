"""The least certificate of the center cell: the breadth-first pass against plain enumerations of partial rows."""

from __future__ import annotations

import itertools

import numpy as np

from computations import min_certificate as mc
from computations.cone_screening import cone_table, step_slices, variable_slices


def plain_center(cells: tuple[int, ...], rule: int = 30) -> int:
    """c_t from the 2t + 1 cone cells by running the rule on a list, one cell at a time."""
    row = list(cells)  # (2t + 1,)
    while len(row) > 1:
        row = [(rule >> (4 * row[i - 1] + 2 * row[i] + row[i + 1])) & 1 for i in range(1, len(row) - 1)]  # (len - 2,)
    return row[0]


def brute_minimum(t: int, rule: int = 30, listing: list[str] | None = None) -> tuple[int, int]:
    """(m(t), number of minimum subcubes) by listing every partial row of the cone and every completion of it; the
    least partial rows are appended to `listing` as strings x_{-t} .. x_t."""
    n = 2 * t + 1
    value = {cells: plain_center(cells, rule) for cells in itertools.product((0, 1), repeat=n)}
    sizes = []
    rows = []
    for partial in itertools.product((0, 1, None), repeat=n):
        free = [i for i, v in enumerate(partial) if v is None]
        seen = set()
        for bits in itertools.product((0, 1), repeat=len(free)):
            full = list(partial)
            for i, b in zip(free, bits):
                full[i] = b
            seen.add(value[tuple(full)])
        if len(seen) == 1:
            sizes.append(n - len(free))
            rows.append("".join("*" if v is None else str(v) for v in partial))
    least = min(sizes)
    if listing is not None:
        listing += [r for r, s in zip(rows, sizes) if s == least]
    return least, sizes.count(least)


def brute_implicant(table: np.ndarray, n: int, right_determined: bool, from_top: bool = False) -> int | None:
    """The least size by listing: subcubes (fixed cells) or sets of cells chosen as functions of the cells of smaller
    index (of larger index, from_top), evaluated as a game read from the lowest index up (from the highest down)."""
    # table: (2^n,), entry i is the value at the index i
    best = None
    for chosen in itertools.product((0, 1, 2), repeat=n):  # 0, 1: fixed (or chosen, if right_determined), 2: free
        if right_determined and 1 in chosen:
            continue

        def wins(i: int, index: int) -> bool:
            if i in (-1, n):
                return bool(table[index])
            options = [wins(i - 1 if from_top else i + 1, index | (b << i)) for b in (0, 1)]
            if chosen[i] == 2:
                return all(options)
            if right_determined:
                return any(options)
            return options[chosen[i]]

        size = sum(c != 2 for c in chosen)
        if wins(n - 1 if from_top else 0, 0) and (best is None or size < best):
            best = size
    return best


def test_minimum_against_partial_rows() -> None:
    """m(t) and the number of minimum subcubes for t <= 3 agree with the listing of all partial rows; Rule 90
    gives 2^popcount(t) for t <= 3."""
    for t in (1, 2, 3):
        listing: list[str] = []
        assert mc.least_constant_subcube(t) == brute_minimum(t, listing=listing)
        assert sorted(mc.least_subcubes(t)) == sorted(listing)
        assert mc.ternary_minimum(t) == brute_minimum(t)
        assert mc.least_constant_subcube(t, 90)[0] == brute_minimum(t, 90)[0] == 2 ** bin(t).count("1")
    assert [mc.least_constant_subcube(t)[0] for t in range(1, 6)] == [2, 3, 4, 5, 5]
    assert [mc.least_constant_subcube(t, 90)[0] for t in (4, 5)] == [2, 4]
    assert mc.least_constant_subcube(4, 150)[0] == 3


def test_shortest_implicant_on_random_functions() -> None:
    """The pass agrees with a listing of all subcubes, and of all choices of right-determined cells, on random
    functions of 3 variables."""
    rng = np.random.default_rng(3)
    for _ in range(12):
        table = (rng.random(8) < 0.7).astype(np.uint8)  # (8,)
        for rd in (False, True):
            assert mc.shortest_implicant(mc.as_integer(table), 3, right_determined=rd)[0] == brute_implicant(
                table, 3, rd)


def test_packed_table_against_cone_table() -> None:
    """The packed words, chunked or not, give the bit-sliced table of `cone_table` at t = 4."""
    assert mc.packed_table(4) == mc.packed_table(4, inner=6) == mc.as_integer(cone_table(4))
    assert (mc.unpacked_table(3) == cone_table(3)).all()


def test_routing_against_partial_rows() -> None:
    """R(3, k) by the pass agrees with a listing of the partial rows with x_u free and every cell left of u fixed, and
    its right-determined form with a game in which each chosen cell sees the cells to its right."""
    t, n = 3, 7
    table = cone_table(t)  # (2^7,), bit i of the index is x_{-t+i}
    for k in range(1, t + 1):
        m = n - k - 1
        games = []
        for prefix in range(1 << k):
            rows = np.arange(1 << m) << (k + 1) | prefix  # (2^m,), x_u = 0
            games.append(brute_implicant(1 - (table[rows] ^ table[rows | (1 << k)]), m, True, from_top=True))
        assert mc.routing(t, right_determined=True)[k - 1] == min(g for g in games if g is not None)
        best = None
        for partial in itertools.product((0, 1, None), repeat=n - k - 1):
            for prefix in itertools.product((0, 1), repeat=k):
                free = [i for i, v in enumerate(partial) if v is None]
                zero = True
                for bits in itertools.product((0, 1), repeat=len(free)):
                    right = list(partial)
                    for i, b in zip(free, bits):
                        right[i] = b
                    rows = [list(prefix) + [x] + right for x in (0, 1)]
                    a, b = (int(table[sum(c << i for i, c in enumerate(r))]) for r in rows)
                    zero &= a == b
                if zero:
                    size = len(partial) - len(free)
                    best = size if best is None else min(best, size)
        assert mc.routing(t)[k - 1] == best


def derivative_vanishes(t: int, u: int, fixed: dict[int, int]) -> tuple[bool, bool]:
    """(D_u c_t is 0 on the subcube, c_t is constant on it), over every completion at once by bit slicing."""
    free_cells = [u] + [j for j in range(-t, t + 1) if j not in fixed and j != u]  # x_u is bit 0
    slices = variable_slices(len(free_cells))  # (free,) x (2^free,)
    row = [np.bool_(fixed[j]) if j in fixed else slices[free_cells.index(j)] for j in range(-t, t + 1)]
    center = step_slices(row, t)[0]  # (2^free,)
    pairs = center.reshape(-1, 2)  # (2^(free-1), 2): the two values of x_u
    return bool((pairs[:, 0] == pairs[:, 1]).all()), bool(center.all() or not center.any())


def test_one_step_reduction() -> None:
    """With x_{u+1} = 1 and x_{u-1} = 1, D_u c_t at a row is D_{u+1} c_{t-1} at the row one step later."""
    rng = np.random.default_rng(7)
    t = 6
    for _ in range(40):
        x = [int(b) for b in rng.integers(0, 2, 2 * t + 1)]  # x_{-t} .. x_t
        k = int(rng.integers(1, 2 * t - 1))  # u = -t + k, u + 1 <= t
        x[k + 1] = 1
        x[k - 1] = 1
        flip = list(x)
        flip[k] ^= 1
        later = [x[i - 1] ^ (x[i] | x[i + 1]) for i in range(1, 2 * t)]  # x'_{-t+1} .. x'_{t-1}
        later_flip = list(later)
        later_flip[k] ^= 1  # cell u + 1 = -(t - 1) + k
        assert plain_center(tuple(x)) ^ plain_center(tuple(flip)) == (
            plain_center(tuple(later)) ^ plain_center(tuple(later_flip)))


def test_stripe_and_routing_witness() -> None:
    """The stripe makes c_9 constant with x_{-1} free (checked against the plain run on sampled rows), and on the
    subcube x_{-12} = 0, x_{-7} .. x_1 alternating with x_1 = 1, every other cell free, D_u c_12 vanishes at
    u = -11 although c_12 is not constant: 9 fixed cells right of u, one fewer than the routing lemma needs. The same
    holds for the odd stretch x_{-9} .. x_{-1}, and at t = 13 for x_{-13} = x_{-12} = 0 and x_{-10} .. x_{-2}
    alternating with x_{-2} = 1."""
    zero, one = mc.stripe_values(9)  # (2^11,) each
    assert set(zero.tolist()) == {1} and set(one.tolist()) == {0}
    rng = np.random.default_rng(5)
    for index in rng.integers(0, 1 << 11, 8):
        free = [(int(index) >> i) & 1 for i in range(11)]  # x_{-1} .. x_9
        left = [0] + [int(j % 2 == 0) for j in range(8, 1, -1)]  # x_{-9} .. x_{-2}
        assert plain_center(tuple(left + free)) == zero[index]
    assert derivative_vanishes(12, -11, {-12: 0} | {j: int(j % 2 != 0) for j in range(-7, 2)}) == (True, False)
    assert derivative_vanishes(12, -11, {-12: 1} | {j: int(j % 2 != 0) for j in range(-9, 0)}) == (True, False)
    assert derivative_vanishes(13, -11, {-13: 0, -12: 0} | {j: int(j % 2 == 0) for j in range(-10, -1)}) == (
        True, False)
