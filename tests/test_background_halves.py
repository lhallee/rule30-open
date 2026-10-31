"""The right halves beside a period-four column of a background, against direct runs of the rule."""

from __future__ import annotations

import numpy as np

from computations import absorption
from computations import background_halves as bh
from computations.rule30 import step


def test_eighty_cell_background() -> None:
    """The background of period 8 on 80 cells: its ring satisfies the rule, stepped as a whole ring with `step`; it has
    columns repeating 0001 and none repeating 0011 or 0111; the half beside each, driven by 0001 and stepped with
    `step`, keeps the background's columns and is in the family at none of its 8 phases, by `family_depth` on its 64
    columns read from the run itself, with an ether prefix far below 51 columns."""
    wall = absorption.kit_wall()
    [ring] = [r for r in bh.rings(8) if len(r) == 80][:1]
    size = len(ring)
    for ph in range(8):  # the ring at phase ph, stepped once, is the ring at phase ph + 1
        row = sum(((ring[x] >> ph) & 1) << x for x in range(size))
        wide = row | row << size | row << 2 * size  # three copies, the middle one exact after a step
        after = (step(wide) >> size) & ((1 << size) - 1)
        assert after == sum(((ring[x] >> ((ph + 1) % 8)) & 1) << x for x in range(size))
    found = [(r, x, ph) for r, x, ph in bh.word_columns(8, "0001") if len(r) == 80]
    assert found and not [r for r, *_ in bh.word_columns(8, "0011") + bh.word_columns(8, "0111") if len(r) == 80]
    r, x, ph = found[0]
    assert bh.never_enters("0001", r, x, ph, 8, wall) == "outside"
    half = bh.background_half(r, x, ph, 64 + 8 * 2 + 2)
    for t in range(16):  # driven by 0001 the half stays the background, and stays out of the family
        low = half & ((1 << 64) - 1)
        assert low == bh.background_half(r, x, (ph + t) % 8, 64)
        assert absorption.family_depth("0001", np.array([low], dtype=np.uint64), t % 4, wall)[0] < 0
        assert bh.ether_prefix("0001", low, t % 4, 64) < 20
        half = ((half << 1) | int("0001"[t % 4])) ^ (half | (half >> 1))


def test_truncation_entry() -> None:
    """A truncation of the half to 80 cells, white beyond, enters the family at step 228 by `entry_time`, and a direct
    run with integer rows and `family_depth` at each step agrees; the ether's own half never enters."""
    wall = absorption.kit_wall()
    r, x, ph = next((r, x, ph) for r, x, ph in bh.word_columns(8, "0001") if len(r) == 80)
    candidates = [(r2, x2, ph2) for r2, x2, ph2 in bh.word_columns(8, "0001") if len(r2) == 80]
    times = {bh.entry_time("0001", bh.background_half(r2, x2, ph2, 80), 80, 400, wall) for r2, x2, ph2 in candidates}
    assert times == {228, 261}
    half, first = bh.background_half(r, x, ph, 80), -1
    for t in range(400):
        if absorption.family_depth("0001", np.array([half & ((1 << 64) - 1)], dtype=np.uint64), t % 4, wall)[0] >= 0:
            first = t
            break
        half = ((half << 1) | int("0001"[t % 4])) ^ (half | (half >> 1))
    assert first == bh.entry_time("0001", bh.background_half(r, x, ph, 80), 80, 400, wall)
    ether = next((r2, x2, ph2) for r2, x2, ph2 in bh.word_columns(4, "0111"))
    assert bh.never_enters("0111", *ether, 4, wall) == "ether"


def test_wall_set() -> None:
    """`wall_set` beside the ether's B3 column at 13 cells is the greatest wall set of `absorption`, 605, 433, 533 and
    344 strips at the four phases, which a direct closure with the rule cell by cell confirms on a sample; beside every
    column of the background of 80 cells no strip of 10 cells is kept."""
    ether = next(r for r in bh.rings(4) if len(r) == 7)
    found = [(a, bh.wall_set(ether, 4, a, 13)) for a in range(7)]
    [(a, kept)] = [(a, k) for a, k in found if k.any()]
    assert sorted(int(k.sum()) for k in kept) == sorted([605, 433, 533, 344])
    for ph, strip in [(ph, int(s)) for ph in range(4) for s in np.flatnonzero(kept[ph])[:20]]:
        left = (ether[a] >> ph) & 1
        for beyond in (0, 1):
            cells = [left] + [(strip >> j) & 1 for j in range(13)] + [beyond]
            new = sum((cells[j - 1] ^ (cells[j] | cells[j + 1])) << (j - 1) for j in range(1, 14))
            assert kept[(ph + 1) % 4][new]
    eighty = next(r for r in bh.rings(8) if len(r) == 80)
    assert not any(bh.wall_set(eighty, 8, a, 10).any() for a in range(80))


def test_glide_symmetry() -> None:
    """The background of 80 cells is its own image one step later shifted 10 cells: B(j + 10, phase) = B(j, phase + 1)
    for every cell and phase, so its 0001 columns, each read from two phases, give one driven half up to a time shift."""
    ring = next(r for r in bh.rings(8) if len(r) == 80)
    assert all(((ring[(j + 10) % 80] >> ph) & 1) == ((ring[j] >> ((ph + 1) % 8)) & 1) for j in range(80) for ph in range(8))
