"""Tests of computations.absorption: the ether, the wall and the kit's family against direct runs with `step`,
checks column by column and the kit's Lean source."""

from __future__ import annotations

import numpy as np

from computations import absorption, game
from computations.rule30 import step
from references import ROOT, lean_states


def test_c3_ether() -> None:
    """For each word, the ether's left half, read from an ether column aligned with the word, keeps the kit's C3
    pattern under the kit's effective boundary: a 400-cell truncation is exact at cell -1 for 100 steps, and the ether
    repeats every 4, so each C3 has this infinite solution."""
    for word, j0, shift in (("0001", 6, 0), ("0011", 0, 0), ("0011", 1, 3), ("0111", 2, 2)):
        assert absorption.aligned(word, j0, shift)
        boundary = {"0001": "0000", "0011": "0010", "0111": "0110"}[word]
        pattern = {"0001": "0*01", "0011": "*001", "0111": "*001"}[word]
        U = sum(absorption.ether(j0 - 1 - j, shift) << j for j in range(400))
        for t in range(100):
            assert pattern[t % 4] in ("*", str(U & 1)), (word, j0, t)
            U = ((U >> 1) ^ (U | (U << 1) | int(boundary[t % 4]))) & ((1 << 400) - 1)
            assert U & ((1 << 200) - 1) == sum(absorption.ether(j0 - 1 - j, t + 1 + shift) << j for j in range(200))


def test_ether_and_walls(certificate: np.ndarray) -> None:
    """The ether table is a Rule 30 orbit on a ring and every listed alignment holds; the greatest wall is the last 13
    columns of the core certificate of 0001 at width 16, which the core fixes to the ether's B1 B2 B3; the computed wall
    has the kit's 26, 29, 27 and 27 states, steps into itself for both cells beyond, and is the closure of any one of
    its states."""
    # certificate: (4, 2^16)
    ring = np.array([[absorption.ether(j, ph) for j in range(70)] for ph in range(4)], dtype=bool)  # (4, 70)
    for ph in range(4):
        assert np.array_equal(np.roll(ring[ph], 1) ^ (ring[ph] | np.roll(ring[ph], -1)), ring[(ph + 1) % 4])
    assert all(absorption.aligned(word, j0, shift) for word in absorption.WORDS
               for j0, shift in absorption.ALIGNMENTS[word])
    greatest, wall = absorption.greatest_wall(), absorption.kit_wall()  # (4, 2^13) each
    for ph in range(4):
        assert set((np.flatnonzero(certificate[ph]) >> 3).tolist()) == set(np.flatnonzero(greatest[ph]).tolist())
    assert wall.sum(axis=1).tolist() == [26, 29, 27, 27] and not (wall & ~greatest).any()
    states = [(ph, s) for ph in range(4) for s in np.flatnonzero(wall[ph]).tolist()]
    for ph, s in states:
        for beyond in (0, 1):
            row = absorption.ether(2, ph) | (s << 1) | (beyond << 14)  # B3 at bit 0, the wall at bits 1 .. 13
            assert wall[(ph + 1) % 4][(step(row) >> 1) & 0x1FFF]
    seen, todo = {states[0]}, [states[0]]
    while todo:
        ph, s = todo.pop()
        for beyond in (0, 1):
            nxt = ((ph + 1) % 4, (step(absorption.ether(2, ph) | (s << 1) | (beyond << 14)) >> 1) & 0x1FFF)
            if nxt not in seen:
                seen.add(nxt)
                todo.append(nxt)
    assert seen == set(states)


def in_family_slow(word: str, row: int, phase: int, wall: np.ndarray) -> bool:
    """The kit's `InFamily` for a right half held as an integer (bit j is column j + 1), checked column by column."""
    # wall: (4, 2^13), the wall states at each ether phase
    for j0, shift in absorption.ALIGNMENTS[word]:
        psi = (phase + shift) % 4
        for k in range(52):
            if (j0 + k) % 7 == 2 and wall[psi][(row >> k) & 0x1FFF] \
                    and all((row >> (p - 1)) & 1 == absorption.ether(j0 + p, psi) for p in range(1, k + 1)):
                return True
    return False


def test_absorption_census() -> None:
    """Every fifth right half of up to 6 cells, in every phase of the three words, enters the family exactly when integer
    rows stepped one at a time first meet the family checked column by column; and at 8 cells the latest entries are
    the absorption finding's 355, 521 and 295 at phase 0 (12 cells and more: the finding's reproduce command)."""
    wall = absorption.kit_wall()  # (4, 2^13)
    for word in absorption.WORDS:
        for phase in range(4):
            times = absorption.census(word, 6, phase, 600, wall)  # (64,)
            for start in range(0, 64, 5):
                row, t = start, 0
                while not in_family_slow(word, row, (t + phase) % 4, wall):
                    row = ((row << 1) | int(word[(t + phase) % 4])) ^ (row | (row >> 1))
                    t += 1
                assert times[start] == t, (word, phase, start)
    assert [int(absorption.census(word, 8, 0, 600, wall).max()) for word in absorption.WORDS] == [355, 521, 295]


def test_wall_is_the_kits() -> None:
    """The computed wall is the kit's `wallStates`, read from its source, and the kit's `S0001` is the ether's B1 B2 B3
    followed by a wall state at the same phase."""
    wall = absorption.kit_wall()  # (4, 2^13)
    computed = {(ph, s) for ph in range(4) for s in np.flatnonzero(wall[ph]).tolist()}
    assert len(computed) == 109 and lean_states("wallStates") == computed
    b123 = {ph: sum(absorption.ether(j, ph) << j for j in range(3)) for ph in range(4)}
    assert lean_states("S0001") == {(ph, b123[ph] | (s << 3)) for ph, s in computed}


def test_pure_ether() -> None:
    """Under 0001 the periodic half 0010000 is the aligned ether at phase 0, and 1110110 becomes it two steps after
    phase 1, checked on integer rows; neither enters the family, and the aligned ether is outside the family at every
    phase, checked column by column."""
    wall = absorption.kit_wall()  # (4, 2^13)
    for name, phase, when in (("0010000", 0, 0), ("1110110", 1, 2)):
        row = sum(int(name[j % 7]) << j for j in range(400))
        for t in range(when):
            row = (((row << 1) | int("0001"[(t + phase) % 4])) ^ (row | (row >> 1))) & ((1 << 400) - 1)
        assert any(all((row >> (p - 1)) & 1 == absorption.ether(j0 + p, when + phase + shift) for p in range(1, 200))
                   for j0, shift in absorption.ALIGNMENTS["0001"])
        rows = absorption.packed(np.array([[int(name[j % 7]) for j in range(4070)]], dtype=np.uint8))  # (1, 64)
        assert absorption.pure_ether("0001", rows, phase, 8).tolist() == [when]
        assert absorption.absorb("0001", rows, phase, 400, wall, 4070).tolist() == [-1]
    for j0, shift in absorption.ALIGNMENTS["0001"]:
        for phase in range(4):
            row = sum(absorption.ether(j0 + p, phase + shift) << (p - 1) for p in range(1, 120))
            assert not in_family_slow("0001", row, phase, wall)


def test_deep_depth() -> None:
    """The family at any depth: a row with the aligned ether on columns 1 .. k, a wall state from the kit's source on
    the next 13 and random cells beyond is in the family at depth k (k past the 64-column window included), and stops
    being so when one ether column is flipped; the deepest depth is at least the least one `family_depth` finds."""
    rng = np.random.default_rng(17)
    wall = absorption.kit_wall()  # (4, 2^13)
    states = sorted(lean_states("wallStates"))
    for word in absorption.WORDS:
        for j0, shift in absorption.ALIGNMENTS[word]:
            for _ in range(6):
                phase = int(rng.integers(4))
                psi = (phase + shift) % 4
                k = int(rng.choice([k for k in range(3, 140) if (j0 + k) % 7 == 2]))
                strip = rng.choice([s for ph, s in states if ph == psi])
                row = rng.integers(0, 2, 200).astype(bool)  # (200,), column p + 1 at index p
                row[:k] = [absorption.ether(j0 + p, psi) for p in range(1, k + 1)]
                row[k:k + 13] = [(strip >> q) & 1 for q in range(13)]
                assert absorption.deep_depth(word, row[None, :], phase, wall, 180)[0] >= k, (word, k)
                low = np.uint64(sum(int(row[p]) << p for p in range(64)))
                least = absorption.family_depth(word, np.array([low]), phase, wall)[0]
                assert least <= absorption.deep_depth(word, row[None, :], phase, wall, 180)[0]
                row[int(rng.integers(k))] ^= True
                assert absorption.deep_depth(word, row[None, :], phase, wall, 180)[0] < k


def test_lean_entries() -> None:
    """The entry lists of `SmallRight` in `EmptyRight.lean` are the ones `lean_entries` builds."""
    lean = (ROOT / "Rule30Open" / "Columns" / "EmptyRight.lean").read_text(encoding="utf-8")
    assert absorption.lean_entries(6, absorption.kit_wall()) in lean


def test_kit_reach() -> None:
    """`game.moves` gives the moves of `game.game_graph`; `absorption.family_cut` holds every window that
    `absorption.family_depth`, on whole rows, puts in the family at a depth whose wall ends inside the window, and the
    pure aligned ether; every node of the game of each word of period four at width 14 can reach the cut family, and
    every node of the game of 001 at width 14 the states of `t001` cut to 14 cells."""
    from computations import absorption, lock_chain
    for pattern, width in (("0001", 6), ("001", 7), ("0010111", 5)):
        source, target, *_ = game.game_graph(pattern, width)
        mine = game.moves(pattern, width)
        assert sorted(zip(source.tolist(), target.tolist(), strict=True)) == sorted(
            zip(*(m.tolist() for m in mine), strict=True))
    wall = absorption.kit_wall()
    width = 16  # a wall ends inside the window at depths 0 to 3, where every word has a member (0001 at depth 3)
    for word in absorption.WORDS:
        cut = absorption.family_cut(word, width, wall).reshape(4, 1 << width)
        windows = np.arange(1 << width, dtype=np.uint64)
        for phase in range(4):
            depth = absorption.family_depth(word, windows, phase, wall)
            members = np.flatnonzero((depth >= 0) & (depth + absorption.WALL_CELLS <= width))
            assert members.size and cut[phase][members].all()
            for j0, shift in absorption.ALIGNMENTS[word]:
                pure = sum(absorption.ether(j0 + p, phase + shift) << (p - 1) for p in range(1, width + 1))
                assert cut[phase][pure]
        assert absorption.family_reach(word, 14, wall) == 1.0
    assert lock_chain.t001_reach(14) == 1.0
