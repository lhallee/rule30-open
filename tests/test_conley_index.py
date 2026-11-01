"""`computations.conley_index` against elimination on Python integers, integer matrix powers and direct evolution."""

from __future__ import annotations

import itertools

import numpy as np

from computations import conley_index as ci, space_time_periodic
from computations.game import game_moves


def int_rank(rows: list[int]) -> int:
    """Rank over GF(2) of rows held as Python integers."""
    basis: dict[int, int] = {}
    for row in rows:
        while row:
            top = row.bit_length() - 1
            if top not in basis:
                basis[top] = row
                break
            row ^= basis[top]
    return len(basis)


def int_power_rank(adjacency: np.ndarray, exponent: int) -> int:
    """Rank over GF(2) of A^exponent, the power taken in exact integers."""
    # adjacency: (n, n)
    power = np.eye(adjacency.shape[0], dtype=object)  # (n, n)
    base = adjacency.astype(object)  # (n, n)
    for _ in range(exponent):
        power = power.dot(base)
    return int_rank([int("".join(str(int(v) % 2) for v in row) or "0", 2) for row in power])


def test_rank_against_integers() -> None:
    """Packed elimination agrees with elimination on Python integers."""
    rng = np.random.default_rng(1)
    for shape in ((5, 9), (17, 17), (30, 12), (40, 40)):
        for density in (0.1, 0.5):
            m = (rng.random(shape) < density).astype(np.uint8)  # (r, c)
            assert ci.gf2_rank(m) == int_rank([int("".join(map(str, row)), 2) for row in m])


def test_index_of_small_graphs() -> None:
    """A cycle keeps its whole space, a graph with no cycle has none, and two looped vertices joined both ways have a
    nilpotent matrix over GF(2) although they hold cycles of every length."""
    cycle = np.roll(np.eye(3, dtype=np.uint8), 1, axis=1)  # (3, 3)
    assert ci.index_dimension(cycle) == 3
    assert ci.index_dimension(np.triu(np.ones((4, 4), dtype=np.uint8), 1)) == 0
    looped = np.ones((2, 2), dtype=np.uint8)  # (2, 2)
    assert ci.index_dimension(looped) == 0
    assert int_power_rank(looped, 2) == 0 and np.trace(np.linalg.matrix_power(looped.astype(np.int64), 2)) > 0


def test_components_split_the_index() -> None:
    """The dimensions over the components add up to the rank of a high power of the whole game's matrix."""
    for block, width in (("01", 3), ("001", 3), ("0001", 2)):
        source, target, column = game_moves(block, width)
        nodes = column.size
        whole = np.zeros((nodes, nodes), dtype=np.int64)  # (nodes, nodes)
        np.add.at(whole, (source, target), 1)
        total = sum(d for _, d in ci.component_indices(source, target, nodes))
        assert total == int_power_rank((whole > 0).astype(np.int64), nodes)


def test_transfer_matrix_splits() -> None:
    """With multiplicities the dimensions over the components add up to the rank of a high power of the whole transfer
    matrix, and for 001111 at 8 cells, where the relation's index is trivial, the transfer matrix's is not."""
    for block, width in (("01", 3), ("001", 3), ("0001", 2), ("011", 3)):
        source, target, column = game_moves(block, width)
        nodes = column.size
        whole = np.zeros((nodes, nodes), dtype=np.int64)  # (nodes, nodes), the transfer matrix
        np.add.at(whole, (source, target), 1)
        total = sum(d for _, d in ci.component_indices(source, target, nodes, transfer=True))
        assert total == int_power_rank(whole, nodes)
    source, target, column = game_moves("001111", 8)
    assert sum(d for _, d in ci.component_indices(source, target, column.size, transfer=True)) > 0


def test_nilpotent_component_with_cycles() -> None:
    """The game of 0 at width 3 has a component of three windows with two cycles through one of them and a nilpotent
    matrix over GF(2)."""
    source, target, column = game_moves("0", 3)
    small = [a for a in ci.cyclic_components(source, target, column.size) if a.shape[0] == 3]
    assert len(small) == 1 and ci.index_dimension(small[0]) == 0
    exact = small[0].astype(np.int64)  # (3, 3)
    assert not (np.linalg.matrix_power(exact, 3) % 2).any()
    assert all(np.trace(np.linalg.matrix_power(exact, 2 * k)) > 0 for k in range(1, 4))


def test_trivial_index_on_a_background_block() -> None:
    """At width 8 every component of the game of 001111 holds a cycle and has a nilpotent matrix over GF(2), although
    a background of period 6 has a column that repeats 001111, so its right windows make a closed walk there."""
    source, target, column = game_moves("001111", 8)
    found = ci.component_indices(source, target, column.size)
    assert found and all(d == 0 for _, d in found)
    assert "001111" in set().union(*(blocks for _, _, blocks in space_time_periodic.backgrounds(6)))


def test_two_sided_moves_by_cells() -> None:
    """The two-sided moves are the windows of 5 cells, center held, with each edge cell free, written out cell by
    cell."""
    radius, width = 2, 5
    for block in ("01", "001", "1"):
        source, target, nodes = ci.two_sided_moves(block, radius)
        got = set(zip(source.tolist(), target.tolist()))
        expected = set()
        for phase, cells in itertools.product(range(len(block)), itertools.product((0, 1), repeat=width)):
            if cells[radius] != int(block[phase]):
                continue
            inner = [cells[i - 1] ^ (cells[i] | cells[i + 1]) for i in range(1, width - 1)]
            for left, right in itertools.product((0, 1), repeat=2):
                after = [left] + inner + [right]
                nxt = (phase + 1) % len(block)
                if after[radius] == int(block[nxt]):
                    x = sum(b << i for i, b in enumerate(cells))
                    y = sum(b << i for i, b in enumerate(after))
                    expected.add((phase * (1 << width) + x, nxt * (1 << width) + y))
        assert got == expected and nodes == len(block) << width


def test_small_survey() -> None:
    """Every block of period at most 3 keeps a nontrivial index in the game of 4 cells and with windows of 5 cells."""
    result = ci.survey(3, [4], [2])
    for row in result.values():
        assert row["trivial"] == [] and row["acyclic"] == []
    assert set(result["game 4"]["excluded"]) == {"0", "1"}
