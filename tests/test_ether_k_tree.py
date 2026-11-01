"""Tests for computations/ether_k_tree.py: the tree against a run of every head on whole halves, the leaf test against
direct runs of the held map that carry the ether far past the defect, the counts of points of K that reach a
periodic point against the tail census, and the census section against the Lean module."""

from __future__ import annotations

from pathlib import Path

import numpy as np

from computations import ether_k_tree as ek
from computations.ether_certificate import closed_bits, eth

MODULE = Path(__file__).resolve().parent.parent / "Rule30Open" / "PeriodTwo" / "EtherKTree.lean"
CELLS = 200  # cells of a whole half in the direct runs


def ether_half(a: int, o: int, head: int, cells: int = CELLS) -> int:
    """The ether at the alignment (a, o) in the cells head .. cells - 1, cell by cell, and 0 below."""
    return sum(int(eth(a, j + o)) << j for j in range(head, cells))


def held_rows(rows: np.ndarray) -> np.ndarray:
    """One step of the held map on each row of cells (0/1 bytes, (n, cells)), cell -1 held at 0; the top cell reads a 0
    above it, so cell j is right after t steps while j + t < cells: (n, cells)."""
    up = np.zeros_like(rows)
    up[:, :-1] = rows[:, 1:]
    down = np.zeros_like(rows)
    down[:, 1:] = rows[:, :-1]
    return up ^ (rows | down)


def as_rows(values: list[int], cells: int = CELLS) -> np.ndarray:
    """Integers as rows of cells, bit j the cell j: (len(values), cells)."""
    return np.array([[(v >> j) & 1 for j in range(cells)] for v in values], dtype=np.uint8)


def test_tree_against_every_head() -> None:
    """At a head of 8 cells, the leaves of the tree are exactly the heads whose whole half has no odd break up to step
    7, at four alignments, one of each phase."""
    head = 8
    for a, o in [(0, 0), (1, 3), (2, 5), (3, 6)]:
        leaves, _ = ek.tree_leaves(head, a, o)
        tail = ether_half(a, o, head)
        rows = as_rows([h | tail for h in range(1 << head)])  # (256, CELLS)
        alive = np.ones(1 << head, dtype=bool)  # (256,)
        for t in range(1, head):
            rows = held_rows(rows)
            if t % 2 == 1:
                alive &= rows[:, 0] == 1
        assert sorted(n & ((1 << head) - 1) for n in leaves) == [h for h in range(1 << head) if alive[h]]
        assert all(n >> head == ek.ether_tail(head, a, o) >> head for n in leaves)


def test_leaf_test_against_direct_runs() -> None:
    """At heads of 16 cells and 12 alignments, sampled leaves and every leaf that does not break K: a break of the test is the first odd step with cell 0 white in a direct
    run, and a leaf the test settles has no break within 120 steps and keeps every cell from the bound on equal to
    the ether at every one of them."""
    bits = closed_bits()
    head, bound = 16, 23
    rng = np.random.default_rng(11)
    for a in range(4):
        for o in range(0, 7, 3):
            leaves, _ = ek.tree_leaves(head, a, o)
            picked = [leaves[i] for i in rng.choice(len(leaves), size=4, replace=False)]
            settled = [n for n in leaves if ek.leaf_ok(n, head, a, o, bits, bound=bound)["how"] > 0]
            for n in picked + settled:
                r = ek.leaf_ok(n, head, a, o, bits, bound=bound)
                assert r["ok"]
                row = as_rows([(n & ((1 << head) - 1)) | ether_half(a, o, head)])  # (1, CELLS)
                first = -1
                for t in range(1, 121):
                    row = held_rows(row)
                    if t % 2 == 1 and row[0, 0] == 0 and first < 0:
                        first = t
                    if r["how"] > 0:
                        assert all(row[0, j] == int(eth(a + t, j + o)) for j in range(bound, CELLS - t))
                assert first == (r["step"] if r["how"] == 0 else -1)


def test_census_counts() -> None:
    """Every leaf passes at heads of 12 and 16 cells, and the leaves that do not break K are the heads of the ether
    that the tail census finds reaching a periodic point of K: 26 of 12 cells and 34 of 16 cells."""
    r12 = ek.census(12, bound=19)
    r16 = ek.census(16, bound=23)
    assert r12["failed"] == r16["failed"] == 0
    assert r12["leaves"] == 28 * 2 ** 6 and r16["leaves"] == 28 * 2 ** 8
    assert r12["strip"] + r12["repeat"] == 26 and r16["strip"] + r16["repeat"] == 34
    assert 2 * ek.ROUNDS <= 64 and ek.BOUND <= 126


def test_lean_section_matches_module() -> None:
    """The census section of the Lean module is the one `lean_section` prints."""
    text = MODULE.read_text()
    for line in ek.lean_section().splitlines():
        assert line in text
