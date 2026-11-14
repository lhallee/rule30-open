"""edge_periodic_full against independent checks: the live states of the full graph against bi-infinite rows built by
brute force for L = 2, the block weight 3L/4 against its formula, and the non-antiperiodic column 10101000."""

from __future__ import annotations

import functools

from computations import edge_periodic_full as ef


def test_full_live_small() -> None:
    live2, reach2 = ef.full_live_count(2)
    live4, reach4 = ef.full_live_count(4)
    assert reach2 == 5 and reach4 == 5
    assert live2 == 9 and live4 == 99


def test_full_live_two_by_hand() -> None:
    # L = 2: a state (u, v) is live iff the column pair recurrence never meets an odd input; with two-bit words the
    # input u or v has even weight iff it is 00 or 11, so check the count against a direct depth-16 search
    def succ(u: int, v: int) -> list[tuple[int, int]]:
        g = u | v
        if g in (1, 2):
            return []
        if g == 0:
            return [(v, 0), (v, 3)]
        return [(v, 0b10), (v, 0b01)]

    @functools.cache
    def alive(s: tuple[int, int], depth: int) -> bool:
        return depth == 0 or any(alive(x, depth - 1) for x in succ(*s))

    # a walk of 16 edges among 16 states repeats a state, so alive to depth 16 means live
    assert sum(alive((u, v), 16) for u in range(4) for v in range(4)) == 9


def test_dead_square_weight() -> None:
    for L in (4, 8, 16, 32):
        assert ef.dead_square_weight(L) == 3 * L // 4


def test_non_antiperiodic_column() -> None:
    bad = ef.non_antiperiodic_columns(8)
    assert int("00010101", 2) in bad or int("10101000", 2) in bad
    assert ef.non_antiperiodic_columns(4) == []
