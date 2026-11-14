"""Tests for the block algebra of an elementary rule: the operation against direct simulation, the Schreier-Sims order
against brute-force closure, the translations of Rule 30 against the states of the kit's automaton group 2369, and the
rank bound behind the solvability theorem against the monoid itself."""

from __future__ import annotations

import random

from computations.block_algebra import (
    block_table,
    closure,
    group_order,
    idempotent_groups,
    is_solvable,
    large_rank_groups,
    left_translations,
    phi_state,
    right_translations,
)


def step(rule: int, cells: list[int]) -> list[int]:
    """One step of an elementary rule on a finite list; the result is two cells shorter (cells 1..n-2)."""
    return [(rule >> (4 * cells[i - 1] + 2 * cells[i] + cells[i + 1])) & 1 for i in range(1, len(cells) - 1)]


def test_block_table_matches_simulation() -> None:
    rng = random.Random(1)
    for rule in (30, 90, 110):
        for k in (2, 3, 4):
            table = block_table(rule, k)  # (2^k, 2^k)
            for _ in range(40):
                a, b = rng.randrange(1 << k), rng.randrange(1 << k)
                cells = [(a >> m) & 1 for m in range(k)] + [(b >> m) & 1 for m in range(k)]
                new = step(rule, cells)[:k]  # cells 1..k, the k cells one place right of a's first cell
                assert int(table[a, b]) == sum(c << m for m, c in enumerate(new))


def test_group_order_matches_closure() -> None:
    for rule in (30, 45, 90, 150):
        for k in (2, 3, 4):
            gens = [p for p in right_translations(block_table(rule, k)) if len(set(p)) == len(p)]
            assert group_order(gens) == len(closure(gens))


def test_rule30_orders() -> None:
    expected = {2: 2**3, 3: 2**7, 4: 2**13, 5: 2**25}
    for k, order in expected.items():
        assert group_order(right_translations(block_table(30, k))) == order


def test_rule30_translations_are_group_2369() -> None:
    for k in (2, 3, 4, 5):
        states = sorted({phi_state(s, k) for s in (0, 1, 3)})
        assert states == right_translations(block_table(30, k))


def test_rule30_rank_bound() -> None:
    """Every left translation of a left-permutive rule has rank at most 4 (Rule 30: at most 3), and every right
    translation is a bijection, so every non-unit of the monoid has rank at most that bound."""
    for rule, bound in ((30, 3), (45, 3), (90, 4), (150, 4)):
        for k in (3, 4, 5, 6):
            table = block_table(rule, k)  # (2^k, 2^k)
            assert all(len(set(p)) == len(p) for p in right_translations(table))
            assert max(len(set(p)) for p in left_translations(table)) <= bound
    monoid = closure(right_translations(block_table(30, 3)) + left_translations(block_table(30, 3)))
    ranks = {len(set(s)) for s in monoid}
    assert ranks == {1, 2, 3, 8}


def test_idempotent_groups_rule30_and_110() -> None:
    for rule in (30, 110):
        table = block_table(rule, 3)  # (8, 8)
        monoid = closure(right_translations(table) + left_translations(table))
        groups = idempotent_groups(monoid)
        assert all(is_solvable(g) for g in groups.values())
        assert max(len(x) for x in groups) <= 4
        assert large_rank_groups(monoid, 5) == {}
        assert any(len(g) == 6 for g in groups.values())  # S_3 occurs, so C_3 divides the monoid


def test_is_solvable_detects_a5() -> None:
    a5 = closure([(1, 2, 0, 3, 4), (0, 1, 3, 4, 2), (1, 0, 3, 2, 4)])
    assert len(a5) == 60 and not is_solvable(a5)
    s4 = closure([(1, 0, 2, 3), (1, 2, 3, 0)])
    assert len(s4) == 24 and is_solvable(s4)


def test_left_permutive_units_are_triangular() -> None:
    """Coordinate m of a right translation of Rule 30 is a_m xor (a function of higher coordinates): the units lie in
    the iterated wreath product of order 2^(2^k - 1), checked here as order dividing it."""
    for k in (2, 3, 4):
        order = group_order(right_translations(block_table(30, k)))
        assert (2 ** (2**k - 1)) % order == 0
