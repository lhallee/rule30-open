"""Tests for computations/no_k_tails16.py: the backgrounds against the cycles of `tail_census`, the tail words against
the cells of the background, the tree against a run of every head on whole integers at a smaller head size, the leaves
against `tail_census.in_k_steps`, the latest breaks against the tail census on four backgrounds, and the background
section against the Lean module."""

from __future__ import annotations

from pathlib import Path

import numpy as np

from computations import no_k_tails16 as nk
from computations import tail_census as tc

MODULE = Path(__file__).resolve().parent.parent / "Rule30Open" / "PeriodTwo" / "NoKTails16.lean"


def first_odd_breaks(U: np.ndarray, cells: int, steps: int) -> np.ndarray:
    """For each half (rows of `cells` cells as 0/1 bytes, (n, cells)), the first odd step t <= steps at which cell 0 of
    the held map is 0, by stepping the whole row cell by cell; -1 if there is none: (n,). Cell j of step t is right
    while j + t < cells."""
    assert steps < cells
    x = U.astype(np.uint8)  # (n, cells)
    out = np.full(U.shape[0], -1, dtype=np.int64)  # (n,)
    for t in range(1, steps + 1):
        up = np.zeros_like(x)  # (n, cells): cell j + 1
        up[:, :-1] = x[:, 1:]
        down = np.zeros_like(x)  # (n, cells): cell j - 1, with cell -1 held at 0
        down[:, 1:] = x[:, :-1]
        x = up ^ (x | down)
        if t % 2 == 1:
            new = (x[:, 0] == 0) & (out < 0)
            out[new] = t
    return out


def test_backgrounds_are_the_tail_census() -> None:
    """The 12 backgrounds are those of `tail_census.ring_backgrounds(12)` without the stripes and the ether, in its
    order, each a cycle of the ring map of period P on L cells."""
    rings = [(r.name, r.bg.length, r.bg.period) for r in tc.ring_backgrounds(12)]
    rings = [r for r in rings if r[0] not in ("10", "1000000")]
    assert [(n, length, p) for n, length, p, _ in nk.BACKGROUNDS] == rings
    for name, length, period, _ in nk.BACKGROUNDS:
        states = nk.states_of(name, length)
        assert len(states) == period and nk.ring_step_ok(states, length)
        assert tc.Background(tuple(states), length).name() == name


def test_tail_words_hold_the_background() -> None:
    """The tail word of each alignment holds the background's cells 16 .. 63 in place and nothing else, the index
    points at it, and the distinct words are as many as the distinct alignments of `tail_census`."""
    for name, length, _, _ in nk.BACKGROUNDS[:8]:
        states = nk.states_of(name, length)
        bg = tc.Background(tuple(states), length)
        words, index = nk.tail_words(states, length)
        assert len(set(words)) == len(words) == len(tc.alignments(bg))
        for a in range(len(states)):
            for o in range(length):
                w = words[index[length * a + o]]
                assert w >> 64 == 0 and w & 0xFFFF == 0
                assert w == bg.word(a, o, 16, 48) << 16


def test_tree_against_every_head() -> None:
    """At a head of 8 cells, the tree's leaves are exactly the heads with no odd break up to step 7, its latest break is
    the latest first break over all 256 heads, and both come from stepping each whole half of 160 cells, at a sample of
    alignments of every background."""
    rng = np.random.default_rng(5)
    head = 8
    heads = np.arange(1 << head)  # (256,)
    for name, length, period, _ in nk.BACKGROUNDS:
        states = nk.states_of(name, length)
        bg = tc.Background(tuple(states), length)
        for _ in range(2):
            a, o = int(rng.integers(period)), int(rng.integers(length))
            tail = bg.word(a, o, head, 160 - head)
            word = sum(((tail >> (j - head)) & 1) << j for j in range(head, 64))
            latest, leaves, _ = nk.tree_run(word, nk.ROUNDS, head)
            rows = np.array([[(h >> j) & 1 for j in range(head)] + [(tail >> i) & 1 for i in range(160 - head)]
                             for h in heads], dtype=np.uint8)  # (256, 160)
            breaks = first_odd_breaks(rows, 160, 47)  # (256,)
            assert (breaks > 0).all()
            assert leaves == [int(h) for h in heads[breaks > head]]
            assert latest == int(breaks.max())


def test_census_against_tail_census() -> None:
    """On the four backgrounds with the fewest alignments every leaf breaks, the latest breaks are those of the tail
    census for heads of 16 cells (31, 37, 37, 39), and the first break of sampled leaves is `tail_census.in_k_steps`;
    every background takes 256 leaves per word, and the rounds reach step 47."""
    picked = [b for b in nk.BACKGROUNDS if b[3] in ("L1P1", "L4P8", "L5P5", "L12P3")]
    lasts = []
    for name, length, _, _ in picked:
        states = nk.states_of(name, length)
        rows = nk.census(states, length)
        assert all(r["last"] > 0 and r["leaves"] == 256 for r in rows)
        lasts.append(max(r["last"] for r in rows))
        bg = tc.Background(tuple(states), length)
        words, index = nk.tail_words(states, length)
        a, o = tc.alignments(bg)[-1]
        _, leaves, _ = nk.tree_run(words[index[length * a + o]])
        for h in leaves[::37]:
            step, _ = nk.break_run(h | words[index[length * a + o]], nk.ROUNDS)
            # tail_census takes the head as the defect against the background: cells 0 .. 15 are h xor B_0
            assert step == tc.in_k_steps(bg, a, o, h ^ bg.word(a, o, 0, 16), 48)
    assert lasts == [31, 37, 37, 39]
    assert 2 * nk.ROUNDS - 1 == 47 and 2 * nk.ROUNDS <= 64


def test_lean_section_matches_module() -> None:
    """The background section of the Lean module is the one `lean_section` prints."""
    text = MODULE.read_text()
    for line in nk.lean_section().splitlines():
        assert line in text
