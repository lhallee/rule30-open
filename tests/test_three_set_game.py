"""The double-step game beside an alternating center against direct runs of Python integers and a listing of plays."""

from __future__ import annotations

import functools

import numpy as np

from computations import absorption
from computations.three_set_game import (
    COUNTS,
    ether_cycle,
    family_over,
    family_under,
    forced_basin,
    lock_over,
    make_game,
    ranks,
    reach,
    residue,
    run_periodic,
)


def next_count(d: int, black: int) -> int:
    """The count of white steps since the last black cell of column 1, written out again for the tests."""
    if black:
        return 0
    return 5 if d == 5 else min(d + 1, 4)


def two_steps(window: int, width: int, x1: int, x2: int) -> int:
    """A white step then a black step of a window, by stepping a Python integer that holds the cell beyond."""
    mask = (1 << width) - 1
    row = window | (x1 << width)
    row = ((row << 1) ^ (row | (row >> 1))) & mask  # center white
    row |= x2 << width
    return (((row << 1) | 1) ^ (row | (row >> 1))) & mask  # center black


def test_successors_match_runs() -> None:
    rng = np.random.default_rng(3)
    for width in (6, 10):
        succ = make_game(width).succ  # (4, 2^width)
        for _ in range(30):
            half = int(rng.integers(0, 1 << 40))
            row = half
            rows = []
            for t in range(16):  # the center is white at the even steps
                rows.append(row)
                row = ((row << 1) | (t % 2)) ^ (row | (row >> 1))
            for t in range(0, 14, 2):
                x1, x2 = (rows[t] >> width) & 1, (rows[t + 1] >> width) & 1
                mask = (1 << width) - 1
                assert int(succ[2 * x1 + x2, rows[t] & mask]) == rows[t + 2] & mask
        for w in range(0, 1 << width, 7):
            assert [int(v) for v in succ[:, w]] == [two_steps(w, width, a, b) for a in (0, 1) for b in (0, 1)]


def test_basin_and_reach_match_plays() -> None:
    """At 8 cells, the rank of every state in the forced basin of a target, and reach, against a recursion over the
    plays that uses only `two_steps` and `next_count`."""
    width = 8
    game = make_game(width)
    rng = np.random.default_rng(5)
    target = (family_over(width) | lock_over(width)) & np.uint8(0x3F)  # (256,)
    target |= np.where(rng.random(1 << width) < 0.08, np.uint8(1 << 3), np.uint8(0)).astype(np.uint8)
    held = {(w, d) for w in range(1 << width) for d in range(COUNTS) if (int(target[w]) >> d) & 1}

    def consistent(w: int, d: int) -> bool:
        return (d == 0) == bool(w & 1)

    def moves(w: int, d: int) -> list[tuple[int, int]]:
        return [(v, next_count(d, v & 1)) for v in (two_steps(w, width, a, b) for a in (0, 1) for b in (0, 1))]

    states = [(w, d) for w in range(1 << width) for d in range(COUNTS) if consistent(w, d)]
    forced_by = [held & set(states)]  # forced_by[r]: every play meets the target within r double steps
    some_by = [held & set(states)]  # some_by[r]: some play meets it within r double steps
    while True:
        f = forced_by[-1] | {s for s in states if all(m in forced_by[-1] for m in moves(*s))}
        g = some_by[-1] | {s for s in states if any(m in some_by[-1] for m in moves(*s))}
        if f == forced_by[-1] and g == some_by[-1]:
            break
        forced_by.append(f)
        some_by.append(g)

    @functools.cache
    def every_play(w: int, d: int, depth: int) -> bool:
        """Every play of `depth` double steps from (w, d) meets the target, by listing the plays."""
        return (w, d) in held or (depth > 0 and all(every_play(v, e, depth - 1) for v, e in moves(w, d)))

    rank = ranks(game, target)  # (256, 6)
    basin, added = forced_basin(game, target)
    seen, sweeps = reach(game, target)
    assert len(added) - 1 == int(rank.max()) and sum(added) == len(forced_by[-1])
    assert sweeps <= len(some_by) - 1
    for w in range(1 << width):
        for d in range(COUNTS):
            if not consistent(w, d):
                assert rank[w, d] == -1 and not (int(basin[w]) >> d) & 1 and not (int(seen[w]) >> d) & 1
                continue
            r = int(rank[w, d])
            assert ((w, d) in forced_by[-1]) == (r >= 0) == bool((int(basin[w]) >> d) & 1)
            if r >= 0:
                assert every_play(w, d, r) and (r == 0 or not every_play(w, d, r - 1))
            assert ((w, d) in some_by[-1]) == bool((int(seen[w]) >> d) & 1)
    comps, nodes, member = residue(game, basin)
    assert sum(c.size for c in comps) == int((member >= 0).sum())
    for state, c in zip(nodes.tolist(), member.tolist()):
        w, d = divmod(state, COUNTS)
        assert not (int(basin[w]) >> d) & 1
        if c >= 0:  # a state of a component with a cycle has a move that stays in it
            nxt = [v * COUNTS + e for v, e in moves(w, d)]
            pos = np.searchsorted(nodes, nxt)
            assert any(p < nodes.size and nodes[p] == s and member[p] == c for p, s in zip(pos, nxt))


def test_family_targets_against_rows() -> None:
    """The family under its wall cut agrees with `absorption.family_depth` on rows; the family cut with
    `absorption.family_cut` at the white phases."""
    width = 19
    under = family_under(width)  # (2^19,)
    rng = np.random.default_rng(7)
    members = np.flatnonzero(under)  # (m,)
    rows = members[rng.integers(0, members.size, 64)].astype(np.uint64)  # (64,)
    rows |= rng.integers(0, 1 << 40, 64).astype(np.uint64) << np.uint64(width)
    wall = absorption.kit_wall()  # (4, 2^13)
    for phase in (0, 2):
        depth = absorption.family_depth("0101", rows, phase, wall)  # (64,)
        assert ((depth >= 0) & (depth + absorption.WALL_CELLS <= width)).all()
    cut = absorption.family_cut("0101", 12, wall).reshape(4, -1)  # (4, 2^12)
    assert np.array_equal(family_over(12) != 0, cut[0] | cut[2])
    assert np.array_equal(cut[0], cut[2])


def test_aligned_ether_never_enters() -> None:
    """The aligned ether is periodic in time and enters none of the three sets; the white half enters the gap trap at
    step 293 in phase 0, as in the kit."""
    words = [(int("0000010"[::-1], 2), 7), (int("1001100"[::-1], 2), 7)]
    run = run_periodic(words, 1, 8, late=4)
    assert (run.gap < 0).all() and (run.family < 0).all() and (run.lock < 0).all()
    states = [int(w) & 0xFF for w, _ in run.late[0]]
    assert states[:2] in ([w for w, _ in ether_cycle(8)], [w for w, _ in ether_cycle(8)][::-1])
    assert run_periodic([(0, 1)], 0, 150, late=0).gap.tolist() == [293]
