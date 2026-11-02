"""Tests for computations/forced_basin.py: the ranks against an exhaustive enumeration of the cells beyond the window
and against an independent least fixed point, the target against the family membership of `absorption.py`, and the
counts of the Lean module."""

from __future__ import annotations

import pathlib
import re
import numpy as np

from computations import absorption, forced_basin, lock_certificate

ROOT = pathlib.Path(__file__).resolve().parents[1]


def plays_enter(word: str, width: int, target: np.ndarray, phase: int, window: int, depth: int) -> tuple[bool, bool]:
    """By every sequence of `depth` cells beyond the window, stepped one cell at a time with integers: whether every
    play is in the target by step `depth`, and whether some play stays out of it at steps 0 .. depth - 1. A play that
    is in the target is not extended, since every extension of it is too."""
    # target: (4, n)
    mask = (1 << width) - 1

    def walk(ph: int, v: int, t: int) -> tuple[bool, bool]:
        if target[ph, v]:
            return True, t == depth
        if t == depth:
            return False, True
        results = [walk((ph + 1) % 4, (((v << 1) | int(word[ph])) ^ (v | (v >> 1) | (b << (width - 1)))) & mask, t + 1)
                   for b in (0, 1)]
        return all(r[0] for r in results), any(r[1] for r in results)

    return walk(phase, window, 0)


def test_ranks_by_enumeration() -> None:
    """At widths 8 to 10, with the cut family of `absorption.family_cut` as target (the family itself does not fit
    below width 13): the basin is `lock_certificate.forced_entry` of the target, a node of rank r is entered by every
    sequence of r beyond cells and missed until step r by one, a forward search gives the same ranks, and a node
    outside the basin is missed by some sequence for longer than the largest rank."""
    wall = absorption.kit_wall()  # (4, 2^13)
    rng = np.random.default_rng(16)
    for word, width in (("0001", 8), ("0011", 9), ("0111", 10)):
        target = absorption.family_cut(word, width, wall).reshape(4, 1 << width)  # (4, n)
        rank = forced_basin.basin_ranks(word, width, target)  # (4, n)
        assert np.array_equal(rank >= 0, lock_certificate.forced_entry(word, target))
        top = int(rank.max())
        assert 4 <= top <= 10
        inside = np.argwhere(rank > 0)  # (m, 2)
        for ph, v in inside[rng.choice(len(inside), 3, replace=False)].tolist():
            r = int(rank[ph, v])
            assert plays_enter(word, width, target, ph, v, r) == (True, True)
            assert forced_basin.forward_rank(word, width, target, ph, v, top + 2) == r
        outside = np.argwhere(rank < 0)  # (m, 2)
        for ph, v in outside[rng.choice(len(outside), 2, replace=False)].tolist():
            assert not plays_enter(word, width, target, ph, v, min(top + 1, 10))[0]
            assert forced_basin.forward_rank(word, width, target, ph, v, top + 2) == -1


def test_target_is_family_membership() -> None:
    """A window certifies entry exactly when `absorption.family_depth` finds the half in the family at a depth whose
    wall fits in the window, whatever the cells beyond; and below width 13 no wall fits."""
    wall = absorption.kit_wall()  # (4, 2^13)
    rng = np.random.default_rng(13)
    width = 16
    for word in absorption.WORDS:
        target = forced_basin.family_target(word, width, wall)  # (4, n)
        assert not forced_basin.family_target(word, 12, wall).any()
        for ph in range(4):
            windows = np.concatenate([np.flatnonzero(target[ph]), rng.integers(0, 1 << width, 300)])  # (m,)
            beyond = rng.integers(0, 1 << 40, windows.size, dtype=np.uint64)  # (m,)
            low = windows.astype(np.uint64) | (beyond << np.uint64(width))  # (m,)
            depth = absorption.family_depth(word, low, ph, wall)  # (m,)
            assert np.array_equal(target[ph, windows], (depth >= 0) & (depth <= width - 13))


def test_lean_counts_and_checkpoints() -> None:
    """The counts and ranks of the width-14 theorems of the Lean module are those of the computation, and a
    checkpoint of `lean_wide` holds exactly the nodes of rank at most its round."""
    wall = absorption.kit_wall()  # (4, 2^13)
    text = (ROOT / "Rule30Open" / "Columns" / "ForcedBasin.lean").read_text()
    for word in ("0011", "0111"):
        rank = forced_basin.basin_ranks(word, 14, forced_basin.family_target(word, 14, wall))  # (4, n)
        found = re.search(rf"forcedBasin_{word}_14 :\s+Covers \w+ \w+ 14 (\d+) \(basin \w+ \w+ 14 \d+\)\s+"
                          r"\[([\d, ]+)\]", text)
        assert found and int(found.group(1)) == rank.max()
        assert [int(x) for x in found.group(2).split(",")] == (rank >= 0).sum(axis=1).tolist()
    module = forced_basin.lean_wide("0111", 13, 12, wall)
    literal = int(re.search(r"def ck0111_13_1 : Nat :=\s+(0x[0-9a-f]+)", module).group(1), 16)
    rank = forced_basin.basin_ranks("0111", 13, forced_basin.family_target("0111", 13, wall))  # (4, n)
    rounds = forced_basin.chunks(int(rank.max()), 12)
    assert sum(rounds) == rank.max() and max(rounds) <= 12
    assert literal == forced_basin.compact_bits((rank >= 0) & (rank <= rounds[0]))
