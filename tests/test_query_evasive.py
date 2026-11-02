"""Routes to the evasiveness of G_t: the derivative along u, the games on the other cells, gates and other measures."""

from __future__ import annotations

import itertools
from functools import cache

import numpy as np

from computations import query_adversary as qa
from computations import query_depth as qd
from computations import query_evasive as qe


def run(cells: tuple[int, ...], steps: int) -> list[list[int]]:
    """The rows 0 .. steps of the rule on a list of cells, each row two cells shorter."""
    rows = [list(cells)]  # (2t + 1,)
    for _ in range(steps):
        row = rows[-1]
        rows.append([row[i - 1] ^ (row[i] | row[i + 1]) for i in range(1, len(row) - 1)])  # (len - 2,)
    return rows


def test_derivative_is_the_diagonal_parity() -> None:
    """Flipping x_{-t+1} changes c_t by t + the parity of the cells (s, -t + 2 + s), s < t, by plain runs on every
    row for t <= 3; the table of Q_t from G_t equals the diagonal parity computed on the cone of (t - 1, 1), t <= 6;
    Q_t flips with x_{-t+2} on every row for odd t and ignores it for even t; Q'_t xor G_{t-1} ignores x_t."""
    for t in range(1, 4):
        for cells in itertools.product((0, 1), repeat=2 * t + 1):
            rows = run(cells, t)
            flipped = list(cells)
            flipped[1] ^= 1
            diagonal = sum(rows[s][2] for s in range(t))  # cell -t + 2 + s sits at index 2 of row s
            assert run(tuple(flipped), t)[t][0] ^ rows[t][0] == (t + diagonal) % 2
    for t in range(2, 7):
        assert (qe.derivative_table(t) == qe.diagonal_table(t)).all()
        profile = qe.derivative_profile(t)
        assert profile["flips_with_left"] == profile["depends_on_left"] == (t % 2 == 1)
        assert profile["depth_reduced"] == 2 * t - 3
        assert t < 3 or qe.previous_level_split(t)


def test_derivative_sums_against_table() -> None:
    """The C program gives the signed sum of Q'_t from the truth table at t = 7, 8, with the Gray-code walk over 5 and 3
    cells at t = 8 (the default split fixes every walked cell there), and the small values quoted."""
    assert qe.derivative_sums(7) == -10 == qe.derivative_profile(7)["mu_reduced"]
    table = qd.signed_sum(qe.derivative_table(8)[0::2], 13)
    assert qe.derivative_sums(8, split=0) == qe.derivative_sums(8, split=2) == table == -6
    assert [qe.derivative_sums(t) for t in range(3, 7)] == [0, -2, 2, -2]


def plain_games(p0: np.ndarray, p1: np.ndarray, n: int) -> tuple[bool, bool]:
    """(u-last game, GF(2) game) at the root by a recursion over partial rows of S, with parities and constancy taken
    from the rows directly. p0, p1: (2^n,) each, the restrictions u = 0 and u = 1."""

    def rows_of(partial: tuple[int | None, ...]) -> list[int]:
        free = [i for i, v in enumerate(partial) if v is None]
        base = sum(v << i for i, v in enumerate(partial) if v is not None)
        return [base + sum(b << i for i, b in zip(free, bits))
                for bits in itertools.product((0, 1), repeat=len(free))]

    @cache
    def u_last(partial: tuple[int | None, ...]) -> bool:
        rows = rows_of(partial)
        free = [i for i, v in enumerate(partial) if v is None]
        if not free:
            return bool(p0[rows[0]] != p1[rows[0]])
        if len({(int(p0[r]), int(p1[r])) for r in rows}) == 1:
            return False
        return all(any(u_last(partial[:i] + (b,) + partial[i + 1:]) for b in (0, 1)) for i in free)

    @cache
    def gf2(partial: tuple[int | None, ...]) -> bool:
        free = [i for i, v in enumerate(partial) if v is None]
        if not free:
            return False
        for i in free:
            zero = rows_of(partial[:i] + (0,) + partial[i + 1:])
            if sum(int(p0[r] ^ p1[r]) for r in zero) % 2 == 1:
                continue  # Q has full GF(2) degree after this query
            b = 0 if sum(int(p0[r]) for r in zero) % 2 == 1 else 1
            if not gf2(partial[:i] + (b,) + partial[i + 1:]):
                return False
        return True

    return u_last((None,) * n), gf2((None,) * n)


def test_games_against_plain_recursion() -> None:
    """The u-last game and the GF(2) game for t = 2, 3 against `plain_games`."""
    for t in (2, 3):
        g = qa.reduced_table(t)  # (2^(2t-1),)
        n = 2 * t - 2
        u_last, gf2 = plain_games(g[0::2], g[1::2], n)
        games = qe.u_last_games(t)
        assert games["u_last"] == u_last is True
        assert games["gf2_game"] == gf2 == (t == 2)
    games = qe.u_last_games(3)
    assert games["derivative_evasive"] and games["joint_root"] and not games["joint_game"]


def test_structure_and_second_corner() -> None:
    """`structure` against `query_adversary.pair_gates` and a direct flip check on G_t, t = 3, 4; the second corner
    on the truth table for 3 <= t <= 6 and by plain runs on every row for t = 3, 4."""
    for t in (3, 4):
        g = qa.reduced_table(t)
        n = 2 * t - 1
        flips, gates = qe.structure(g, n)
        index = np.arange(1 << n)  # (2^n,)
        assert flips == [i for i in range(n) if (g != g[index ^ (1 << i)]).all()]
        assert gates == qa.pair_gates(g, n)
        r = qa.restrict_table(g, n, {qe.cell_names(t).index(t - 3): 1})
        assert any(c == (0, 0, 0, 1) for _, _, c in qe.structure(r, n - 1)[1])
    assert all(qe.second_corner_holds(t) for t in range(3, 7))
    for t in (3, 4):
        for cells in itertools.product((0, 1), repeat=2 * t + 1):
            x = dict(zip(range(-t, t + 1), cells))
            if x[t - 1] or not x[t - 3]:
                continue
            same = dict(x)
            same[t - 2], same[t] = x[t - 2] & x[t], 1
            assert run(cells, t)[t][0] == run(tuple(same[j] for j in range(-t, t + 1)), t)[t][0]


def test_other_measures() -> None:
    """Approximate degree, automorphisms and the rank of the subcube indicators on functions with known values."""
    index = np.arange(8)  # (8,)
    parity = (np.bitwise_count(index) % 2).astype(np.uint8)  # (8,)
    majority = (np.bitwise_count(index) >= 2).astype(np.uint8)  # (8,)
    assert qe.approximate_degree(parity, 3) == 3
    assert qe.approximate_degree((index & 1).astype(np.uint8), 3) == 1
    assert qe.automorphisms(majority, 3) == 6
    assert qe.automorphisms(parity, 3) == 24  # every permutation, with an even number of negated cells
    assert qe.automorphisms(qa.reduced_table(3), 5) == 1
    assert qe.linear_certificate_rank(3) == 7
    assert qe.monotone_cells(majority, 3) == [0, 1, 2] and qe.monotone_cells(parity, 3) == []
    assert qe.monotone_cells(qa.reduced_table(2), 3) == [2] and qe.monotone_cells(qa.reduced_table(4), 7) == []
