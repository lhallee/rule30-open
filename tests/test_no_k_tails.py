"""Tests for computations/no_k_tails.py: the backgrounds against the cycles of `tail_census` and an independent ring
step, the tail words against the cells of the background, the checker against direct runs of the held map on whole
integers that carry the background far past cell 63, the latest breaks against `tail_census.in_k_steps`, and the
background section against the Lean module."""

from __future__ import annotations

from pathlib import Path

import numpy as np

from computations import no_k_tails as nk
from computations import tail_census as tc

MODULE = Path(__file__).resolve().parent.parent / "Rule30Open" / "PeriodTwo" / "NoKTails.lean"


def ring_step(word: int, length: int) -> int:
    """One step of the held map on a ring, cell by cell: new cell j is cell j + 1 xor (cell j or cell j - 1)."""
    cells = [(word >> j) & 1 for j in range(length)]
    new = [cells[(j + 1) % length] ^ (cells[j] | cells[(j - 1) % length]) for j in range(length)]
    return sum(b << j for j, b in enumerate(new))


def first_odd_break(U: int, cells: int, steps: int) -> int:
    """The first odd step t <= steps at which bit 0 of H^t(U) is 0, by the held map on the whole integer U whose cells
    0 .. cells - 1 are those of the half; cell j of H^t is right while j + t < cells. -1 if there is none."""
    assert steps < cells
    x = U
    for t in range(1, steps + 1):
        x = ((x >> 1) ^ (x | (x << 1))) & ((1 << (cells - t)) - 1)
        if t % 2 == 1 and x & 1 == 0:
            return t
    return -1


def test_backgrounds_are_cycles() -> None:
    """Each list of states is a cycle of the ring map of period P, of least spatial period L, named by its least
    rotation, as `tail_census` names it."""
    for name, length, period, _ in nk.BACKGROUNDS:
        states = nk.background(name, length)
        assert len(states) == period and len(set(states)) == period
        for a in range(period):
            assert ring_step(states[a], length) == states[(a + 1) % period]
        assert nk.ring_step_ok(states, length)
        bg = tc.Background(tuple(states), length)
        assert bg.name() == name
        assert tc.least_spatial_period(states[0], length) == length


def test_tail_words_hold_the_background() -> None:
    """The tail word of each alignment holds the background's cells 12 .. 63 in place and nothing else, and the index
    points at it."""
    for name, length, _, _ in nk.BACKGROUNDS:
        states = nk.background(name, length)
        bg = tc.Background(tuple(states), length)
        words, index = nk.tail_words(states, length)
        assert len(set(words)) == len(words)
        for a in range(len(states)):
            for o in range(length):
                w = words[index[length * a + o]]
                assert w >> 64 == 0 and w & 0xFFF == 0
                assert all((w >> j) & 1 == bg.cell(a, j + o) for j in range(12, 64))


def test_checker_against_whole_integers() -> None:
    """The checker on the truncation to 64 cells finds the same first odd break as the held map run on a half that
    carries the background over 160 cells, for random heads at every alignment."""
    rng = np.random.default_rng(3)
    for name, length, period, _ in nk.BACKGROUNDS:
        states = nk.background(name, length)
        bg = tc.Background(tuple(states), length)
        words, index = nk.tail_words(states, length)
        for a in range(period):
            for o in range(length):
                for h in rng.integers(0, 1 << 12, size=6):  # (6,) heads
                    h = int(h)
                    U = h | (bg.word(a, o, 12, 148) << 12)  # cells 0 .. 159
                    expected = first_odd_break(U, 160, 41)
                    step, _ = nk.first_break(h | words[index[length * a + o]], nk.ROUNDS)
                    assert step == expected != -1


def test_census_against_tail_census() -> None:
    """Every head breaks K, the latest breaks are those of the tail census (29, 31, 33, 33 over heads of 12 cells),
    and the first break of sampled heads is `tail_census.in_k_steps`, whose head is the defect against the
    background."""
    lasts = []
    for name, length, _, _ in nk.BACKGROUNDS:
        states = nk.background(name, length)
        rows = nk.census(states, length)
        assert all(r["last"] > 0 for r in rows)
        lasts.append(max(r["last"] for r in rows))
        bg = tc.Background(tuple(states), length)
        words, index = nk.tail_words(states, length)
        for a, o in tc.alignments(bg):
            for h in range(0, 1 << 12, 97):
                step, _ = nk.first_break(h | words[index[length * a + o]], nk.ROUNDS)
                # tail_census takes the head as the defect against the background: cells 0 .. 11 are h xor B_0
                assert step == tc.in_k_steps(bg, a, o, h ^ bg.word(a, o, 0, 12), 40)
    assert lasts == [29, 31, 33, 33]
    assert 2 * nk.ROUNDS - 1 >= max(lasts) and 2 * nk.ROUNDS <= 64


def test_lean_section_matches_module() -> None:
    """The background section of the Lean module is the one `lean_section` prints."""
    text = MODULE.read_text()
    for line in nk.lean_section().splitlines():
        assert line in text
