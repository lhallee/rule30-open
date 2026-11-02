"""The backgrounds at the edges of the walls, and their truncations, against direct runs of the rule."""

from __future__ import annotations

from computations import background_prefix as bp
from computations import lock_chain as lc


def direct_step(row: list[int]) -> list[int]:
    """One step of Rule 30 on a ring, cell by cell: left xor (center or right)."""
    n = len(row)
    return [row[i - 1] ^ (row[i] | row[(i + 1) % n]) for i in range(n)]


def test_ring_is_an_orbit() -> None:
    """The background of period 10 on 155 cells: each row, stepped on its ring cell by cell, is the next label's row,
    and the row returns after 10 steps; the chain of the wall is periodic from distance 0."""
    bg = bp.background("trap0000010001")
    assert (bg.start, bg.period, bg.modulus) == (0, 155, 10)
    for label in range(10):
        assert direct_step(bp.ring_row(bg, label)) == bp.ring_row(bg, (label + 1) % 10)


def test_prepending_and_inside() -> None:
    """T_(1 + 155) is T_1 with the 155 background columns in front, and the background half beside column 1, driven by
    the block and stepped as an integer, stays the background and is a state of T_1 at each of 10 steps; beside
    column 18 it is a state at none."""
    bg = bp.background("trap0000010001")
    assert bp.sibling_identity(bg, 1)
    t = lc.carried("trap0000010001", 1)
    states = bp.state_set(t)
    for x, inside in ((1, True), (18, False)):
        _, phase = bp.block_phase(bg, x, 0)
        half = bp.half_bits(bg, x, 0, 60)
        for s in range(10):  # cells 1 .. 40 are exact for 20 steps
            assert half & ((1 << 40) - 1) == bp.half_bits(bg, x, s, 40)
            assert (((phase + s) % 10, half & ((1 << t["cells"]) - 1)) in states) == inside
            half = ((half << 1) | int(t["word"][(phase + s) % 10])) ^ (half | (half >> 1))


def plain_entry(word: str, states: set[tuple[int, int]], cells: int, half: int, phase: int, steps: int) -> int:
    """The first step at which the half, driven by `word` from `phase` and stepped as an integer, has its first
    `cells` cells in a state at the block's phase, or -1."""
    for s in range(steps):
        q = (phase + s) % len(word)
        if (q, half & ((1 << cells) - 1)) in states:
            return s
        half = ((half << 1) | int(word[q])) ^ (half | (half >> 1))
    return -1


def test_truncation_entry() -> None:
    """Truncations of 1 to 6 cells beside the wall's column, with a tail of at most one cell, from label 0: the
    vectorized run agrees with a plain run on integers, and those of at least 16 cells are in the wall at step 0."""
    bg = bp.background("trap0000010001")
    t = lc.carried("trap0000010001", 0)
    states = bp.state_set(t)
    _, phase = bp.block_phase(bg, 0, 0)
    e = bp.truncation_entry(bg, 0, 0, 0, 6, 1, 400)
    for k, n, u, entry in zip(e.k.tolist(), e.length.tolist(), e.u.tolist(), e.entry.tolist()):
        half = (bp.half_bits(bg, 0, 0, k)) | (u << k)
        assert entry == plain_entry(t["word"], states, t["cells"], half, phase, 400)
    assert (e.entry >= 0).sum() > 0
    long = bp.half_bits(bg, 0, 0, 16)
    assert plain_entry(t["word"], states, 16, long, phase, 1) == 0


def test_sibling_apart() -> None:
    """For the wall of period 9, whose chain reaches its background after 10 columns, the background half beside every
    column repeating the block of `nine8` is in that trap at no label, and the sibling at distance 64 is apart from
    it by `apart_closed`."""
    bg = bp.background("trap001011111")
    assert (bg.start, bg.period) == (10, 135)
    counts = bp.inside_counts(bg, 8)
    assert counts and all(h == 0 for _, h in counts)
    x = min((c for c, _ in counts), key=lambda c: bp.sibling(bg, 8, c))
    assert bp.sibling(bg, 8, x) == 64 and bp.sibling_apart(bg, 8, x)
