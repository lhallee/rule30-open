"""skeleton_tree against direct evolution: the single cell's branch word by word and its front walk, a cell flipped
behind a white diagonal on the rows themselves, and the word helpers against plain runs on the rows."""

from __future__ import annotations

import numpy as np

from computations.diagonal_cones import diagonal_table
from computations.front_walker import walk_direct
from computations.settled_slope import alternations
from computations.skeleton_tree import (SingleWords, accumulate, alternation, follow_tree, pair_next_int,
                                        white_run)

STEPS, DEPTH, BASE = 768, 301, 512


def table_words(D: np.ndarray, base: int) -> SingleWords:
    """The aligned words of a full table D[j, t], read on the 64 times from `base` (a multiple of 64)."""
    # D: (depth, steps)
    words, periods = [], []
    for row in D[:, base:base + 64]:  # (64,)
        s = "".join(str(int(c)) for c in row)
        P = next(p for p in (1, 2, 4, 8, 16, 32, 64) if s[p:] == s[:-p])
        words.append(int(s[:P][::-1], 2))
        periods.append(P)
    return SingleWords(words, periods, base)


def test_single_branch_against_evolution() -> None:
    D = diagonal_table(STEPS, DEPTH)  # (DEPTH, STEPS)
    single = table_words(D, BASE)
    # follow_tree asserts that every word of the single cell's branch is the evolved one, and picks the evolved child
    branches = follow_tree(DEPTH - 1, single, progress=False)
    assert len(branches) == 1  # the white diagonals 2, 7, 28 below depth 300 all double
    br = branches[0]
    assert [(w, d) for w, d, _ in br.whites] == [(2, True), (7, True), (28, True)]
    assert br.walk_end == int(walk_direct(D)[DEPTH - 1])
    assert [r.period for r in br.regimes] == [1, 2, 4, 8]
    # the largest alternation of each regime against settled_slope.alternations on the evolved rows
    alt = alternations(D[:, BASE:BASE + 129].T)  # (DEPTH - 1,): pair (D_j, D_{j+1})
    for r in br.regimes:
        assert r.max_alt == int(alt[r.start - 1:r.end - 1].max())


def evolve(row: int, steps: int) -> list[int]:
    """Rows of rule 30 as integers, bit k of row t the cell at position lo - t + k for the anchor lo of row 0."""
    rows = [row]
    for _ in range(steps):
        row = (row << 2) ^ ((row << 1) | row)
        rows.append(row)
    return rows


def test_flip_behind_a_white_diagonal() -> None:
    cell = evolve(1, 400)  # the single cell, lo = 0: bit j of row t is D_j(t)
    for w in (2, 7):
        s = 1 + max([t for t in range(120) if (cell[t] >> w) & 1], default=-1)  # D_w white from s
        T = 200
        same, flipped = evolve(cell[s], T), evolve(cell[s] ^ (1 << (w + 1)), T)
        low = (1 << (w + 1)) - 1
        for t in range(T + 1):
            assert (same[t] ^ flipped[t]) & low == 0  # the diagonals 0 .. w do not change
            assert ((same[t] ^ flipped[t]) >> (w + 1)) & 1 == 1  # diagonal w + 1 is complemented
            assert same[t] & ((1 << (w + 3)) - 1) == cell[s + t] & ((1 << (w + 3)) - 1)  # re-anchoring


def test_word_helpers() -> None:
    rng = np.random.default_rng(3)
    for P in (4, 8, 16):
        for _ in range(20):
            a, b = (int(v) for v in rng.integers(1, 1 << P, size=2))
            # pair_next_int: the periodic solution, against a plain run of 4P steps
            c, run = 0, []
            for t in range(4 * P):
                if t >= 3 * P:
                    run.append(c)
                c = ((a >> (t % P)) & 1) ^ (((b >> (t % P)) & 1) | c)
            assert pair_next_int(a, b, P) == sum(bit << (t % P) for t, bit in zip(range(3 * P, 4 * P), run))
            # white_run and alternation against the rows of four periods
            rows = np.array([[(a >> (t % P)) & 1, (b >> (t % P)) & 1] for t in range(4 * P)], dtype=np.uint8)  # (4P, 2)
            plain = max(len(x) for x in "".join(str(int(v)) for v in rows[:, 0]).split("1"))
            assert white_run(a, P) == plain
            m, longest = alternation(a, b, P), int(alternations(rows)[0])
            assert m == longest or (m == -1 and longest == 4 * P)  # -1: the pair alternates forever
    y, Q = accumulate(0b1, 4, 0)  # odd weight: the period doubles and the word is anti-periodic
    assert Q == 8 and all(((y >> t) & 1) != ((y >> (t + 4)) & 1) for t in range(4))
    y, Q = accumulate(0b11, 4, 1)  # even weight: the period stays
    assert (y, Q) == (0b1101, 4)
