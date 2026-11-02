"""`computations.sheaf_sections` against Gaussian elimination over GF(2), direct enumeration of plays, and the game."""

from __future__ import annotations

import itertools

import numpy as np

from computations import game, limit_windows as lw, sheaf_sections as ss


def test_linear_limit_against_elimination() -> None:
    """The annihilator kept as disjoint sets has the dimension and the vectors of the limit found by elimination."""
    for width in (3, 4):
        moves = lw.window_moves(width)  # (2, n, 2)
        n = 1 << width
        for period in range(1, 6):
            for block in game.necklaces(period):
                for labels, basis in zip(ss.linear_limit(block, moves), ss.dense_linear_limit(block, moves)):
                    rows = ss.annihilator_rows(labels) if (labels >= 0).any() else np.zeros((0, n), np.uint8)
                    assert basis.shape[0] + rows.shape[0] == n
                    assert not ((basis.astype(np.int64) @ rows.T.astype(np.int64)) % 2).any()


def reachable_by_plays(block: str, width: int, periods: int) -> list[set[int]]:
    """The windows at each phase after `periods` periods from every window, by enumerating plays one step at a time
    with Rule 30 written out cell by cell."""
    current = set(range(1 << width))
    out: list[set[int]] = []
    for _ in range(periods):
        out = []
        for ch in block:
            out.append(current)
            nxt = set()
            for window, free in itertools.product(current, (0, 1)):
                cells = [int(ch)] + [(window >> j) & 1 for j in range(width)] + [free]
                nxt.add(sum((cells[i - 1] ^ (cells[i] | cells[i + 1])) << (i - 1) for i in range(1, width + 1)))
            current = nxt
    return out


def test_exact_limit_inside_linear_limit() -> None:
    """Every window that plays reach after many periods is in the exact limit, whose obstruction vanishes."""
    width = 5
    moves = lw.window_moves(width)  # (2, n, 2)
    for block in ("0001", "011", "00000011", "0"):
        plays = reachable_by_plays(block, width, 12)
        for reached, exact, labels in zip(plays, ss.exact_limit(block, moves), ss.linear_limit(block, moves)):
            assert set(np.flatnonzero(exact).tolist()) == reached
            assert (labels[exact] < 0).all()


def test_component_sides() -> None:
    """The windows after a step that lie in one component share their first width - 1 cells."""
    width = 6
    moves = lw.window_moves(width)  # (2, n, 2)
    for col in (0, 1):
        _, after, _ = ss.step_components(moves, col)
        for component in np.unique(after[after >= 0]):
            members = np.flatnonzero(after == component)
            assert len(members) <= 2 and len({m & ((1 << (width - 1)) - 1) for m in members}) == 1


def test_tests_are_nested() -> None:
    """Functional, pointwise, exact one cell narrower, exact and the game exclude nested sets of blocks."""
    width = 6
    moves, narrow = lw.window_moves(width), lw.window_moves(width - 1)  # (2, n, 2), (2, n / 2, 2)
    excluded = {key: 0 for key in ("functional", "pointwise", "narrow", "exact", "game")}
    for period in range(1, 9):
        for block in game.necklaces(period):
            flags = [ss.functional_good(block, moves), ss.linear_good(block, moves), ss.exact_good(block, narrow),
                     ss.exact_good(block, moves), ss.game_good(block, width)]
            assert all(not a or b for a, b in zip(flags, flags[1:])), block
            for key, flag in zip(excluded, flags):
                excluded[key] += flag
    assert excluded["pointwise"] < excluded["exact"]


def test_one_cell_short() -> None:
    """The lemma holds on small widths and periods: widths 3 and 5, periods 1 to 6 (period 7 takes 0.2 s more)."""
    for width in (3, 5):
        for period in range(1, 7):
            assert all(ss.one_cell_short(block, width) for block in game.necklaces(period))
