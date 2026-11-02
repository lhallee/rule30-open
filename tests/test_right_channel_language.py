"""The limit set of windows beside an alternating center and the language of column 1 on it, against direct
enumeration, direct runs of right halves and the Lean module."""

from __future__ import annotations

import math
from pathlib import Path

import numpy as np

from computations import right_half
from computations.gate_census import double_step
from computations.right_channel_language import (determinize, driven_windows, image_chain, is_closed_fixpoint,
                                                 lean_bitmaps, lean_rank, limit_set, run_gate, scc_labels,
                                                 successor_index, window_components, word_counts)

ROOT = Path(__file__).resolve().parents[1]


def chain_by_sets(width: int) -> tuple[set[int], int]:
    """The image chain on Python sets with `gate_census.double_step`: the fixpoint and the number of images."""
    cur, n = set(range(1 << width)), 0
    while True:
        nxt = {double_step(w, width, a, b) for w in cur for a in (0, 1) for b in (0, 1)}
        if nxt == cur:
            return cur, n
        cur, n = nxt, n + 1


def test_limit_set_is_the_closed_fixpoint() -> None:
    """At 8 cells the chain and its fixpoint by sets equal the module's, and the fixpoint is exactly its own image."""
    fix, n = chain_by_sets(8)
    codes, chain = limit_set(8)
    assert (n, chain, len(codes)) == (3, 3, 112) and set(codes.tolist()) == fix
    assert {double_step(w, 8, a, b) for w in fix for a in (0, 1) for b in (0, 1)} == fix
    assert is_closed_fixpoint(codes, 8) and not is_closed_fixpoint(np.arange(256), 8)
    rank, _ = image_chain(8)
    assert int(rank.max()) == 3 and int((rank == 0).sum()) == 256 - len(
        {double_step(w, 8, a, b) for w in range(256) for a in (0, 1) for b in (0, 1)})


def test_word_counts_against_path_enumeration() -> None:
    """At 8 cells the number of words of length 10, 11 and 12 that the subset automaton reads equals the number of
    distinct words of column 1 along paths in the limit set, enumerated as pairs (word, last window)."""
    codes, _ = limit_set(8)
    aut = determinize(codes, successor_index(codes, 8))
    inside = set(codes.tolist())
    pairs = {((w & 1,), w) for w in inside}
    brute = {}
    for n in range(2, 13):
        pairs = {(word + (v & 1,), v) for word, w in pairs for a in (0, 1) for b in (0, 1)
                 for v in (double_step(w, 8, a, b),)}
        brute[n] = len({word for word, _ in pairs})
    assert word_counts(aut, 12)[10:] == [brute[10], brute[11], brute[12]] == [59, 79, 104]


def test_small_halves_are_read_from_step_20() -> None:
    """Every right half of up to 8 cells, in both phases: column 1 at the white steps 20 to 59, from a direct run of
    `right_half.column_one`, is read by the automaton of 10 cells, and the windows of the vectorized run match."""
    codes, _ = limit_set(10)
    aut = determinize(codes, successor_index(codes, 10))
    for phase, word in ((0, "10"), (1, "01")):
        gates = np.array([right_half.column_one(word, half, 120)[1 - phase::2][20:60]
                          for half in range(256)])  # (256, 40)
        assert run_gate(aut, gates.astype(np.int64)).all()
        wins = driven_windows(np.arange(256, dtype=np.int64), phase, 8, 120, 10)  # (256, 60)
        assert np.array_equal(wins[:, 20:60] & 1, gates)
        assert np.isin(wins[:, 20:], codes).all()
    assert not run_gate(aut, np.array([[1, 1, 1, 1, 1, 1]])).all()  # column 1 is never black twice in a row here


def test_lean_file_lists_the_ranks() -> None:
    """The bitmaps of `Rule30Open.PeriodTwo.ChannelLanguage` are the ranks of the image chain at 14 cells."""
    text = (ROOT / "Rule30Open" / "PeriodTwo" / "ChannelLanguage.lean").read_text()
    _, chain = image_chain(14)
    assert chain == 20
    assert lean_bitmaps(14) in text and lean_rank(14, chain) in text


def closed_walk_gcd(start: int, members: set[int], width: int, steps: int) -> int:
    """The gcd of the lengths up to `steps` of the closed walks from `start` inside `members`, by propagating the set
    of windows reached with `gate_census.double_step`."""
    g, reached = 0, {start}
    for k in range(1, steps + 1):
        reached = {double_step(w, width, a, b) for w in reached for a in (0, 1) for b in (0, 1)} & members
        if start in reached:
            g = math.gcd(g, k)
    return g


def test_window_components() -> None:
    """At 12 and 14 cells the components with a cycle, their sizes, gcds and flags, with each component closed under
    reachability inside it and its gcd recomputed from closed walks."""
    expected = {12: [(792, 1, True, False, False, True), (49, 1, False, False, False, False)],
                14: [(2005, 1, True, False, False, True), (9, 8, False, True, False, False)]}
    for width, want in expected.items():
        codes, _ = limit_set(width)
        comps = window_components(codes, successor_index(codes, width), width)
        assert [(c.size, c.period, c.terminal, c.locked, c.gap, c.ether) for c in comps] == want
    codes, _ = limit_set(14)
    succ_idx = successor_index(codes, 14)
    _, lab = scc_labels(np.repeat(np.arange(len(codes)), 4), succ_idx.ravel(), len(codes))
    small = {int(w) for w in codes[lab == np.flatnonzero(np.bincount(lab) == 9)[0]]}
    start = min(small)
    for direction in (0, 1):  # every window of the component reaches `start` and is reached from it, inside it
        seen, todo = {start}, [start]
        while todo:
            w = todo.pop()
            nxt = ({double_step(w, 14, a, b) for a in (0, 1) for b in (0, 1)} if direction == 0 else
                   {v for v in small if w in {double_step(v, 14, a, b) for a in (0, 1) for b in (0, 1)}})
            for v in nxt & small - seen:
                seen.add(v)
                todo.append(v)
        assert seen == small
    assert closed_walk_gcd(start, small, 14, 48) == 8
    assert len({v & 1 for v in small}) == 2  # column 1 is constant on each class, not on the component
