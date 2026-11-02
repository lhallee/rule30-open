"""Tests for computations/tail_census.py: the backgrounds against the leftward column map of Rule 30, the stepping
against the held map on whole integers, the closed strips and the census against `defect_potential` on the ether, the
condition of K against direct runs, and the growing windows against direct runs with random cells below."""

from __future__ import annotations

import functools

import numpy as np
import pytest

from computations import defect_potential as dp
from computations import tail_census as tc
from computations.held_shift import cycle_class, held, ring_next
from computations.space_time_periodic import cycles, temporal_periods


@functools.lru_cache(maxsize=1)
def rings() -> list[tc.Ring]:
    """The backgrounds of the tails of up to 12 cells."""
    return tc.ring_backgrounds(12)


def backgrounds() -> dict[str, tc.Background]:
    """The backgrounds of the tails of up to 12 cells, by name."""
    return {r.name: r.bg for r in rings()}


def test_ring_backgrounds_against_cycle_class() -> None:
    rows = rings()
    for q in range(1, 9):
        counted: dict[tuple[int, int], int] = {}
        for w in range(1 << q):
            _, cycle_length, _, period = cycle_class(w, q)
            counted[(period, cycle_length)] = counted.get((period, cycle_length), 0) + 1
        mine = {(r.bg.length, r.bg.period): r.words.get(q, 0) for r in rows}
        assert {k: v for k, v in mine.items() if v} == counted


def test_spatial_and_temporal_periods_against_the_column_map() -> None:
    """A background of spatial period L and temporal period P is a cycle of length L of the leftward column map of
    words of length P (Rule 30 is the mirror of the ring map, which keeps both periods)."""
    rows = rings()
    for P in range(1, 9):
        _, label = cycles(P)  # (c,)
        exact = temporal_periods(P)
        lengths: dict[int, int] = {}
        for lab in label.tolist():
            lengths[lab] = lengths.get(lab, 0) + 1
        theirs = {lengths[lab] for lab, t in exact.items() if t == P and lengths[lab] <= 12}
        mine = {r.bg.length for r in rows if r.bg.period == P}
        assert mine == theirs, P


def test_background_cycle_and_word() -> None:
    for bg in backgrounds().values():
        for a in range(min(bg.period, 20)):
            assert ring_next(bg.states[a], bg.length) == bg.states[(a + 1) % bg.period]
            for o in (0, bg.length - 1):
                assert bg.word(a, o, 5, 40) == sum(bg.cell(a, 5 + i + o) << i for i in range(40))


def test_step_against_held_map() -> None:
    rng = np.random.default_rng(0)
    for bg in backgrounds().values():
        a, o = int(rng.integers(bg.period)), int(rng.integers(bg.length))
        heads = rng.integers(0, 1 << 12, size=4)  # (4,)
        bgw = tc.background_words(bg, o, 2)  # (P, 3)
        D = np.zeros((4, 2), dtype=np.uint64)  # (4, 2)
        D[:, 0] = heads.astype(np.uint64)
        runs = [tc.defect_run(bg, a, o, int(h), 60) for h in heads]
        for t in range(1, 61):
            D = tc.step_words(D, bgw[(a + t - 1) % bg.period], bgw[(a + t) % bg.period])
            for i in range(4):
                if runs[i][t].bit_length() <= 120:
                    assert int(D[i, 0]) | (int(D[i, 1]) << 64) == runs[i][t]


def test_defect_run_is_the_held_map_on_the_whole_integer() -> None:
    bg = backgrounds()["11100"]
    head, a, o, steps = 0b1011001, 2, 3, 30
    width = 400
    U = head ^ bg.word(a, o, 0, width)
    runs = tc.defect_run(bg, a, o, head, steps)
    for t in range(steps + 1):
        cells = width - 2 * t - 2
        assert (U ^ bg.word(a + t, o, 0, width)) & ((1 << cells) - 1) == runs[t] & ((1 << cells) - 1)
        U = held(U) & ((1 << width) - 1)


def test_closed_strips_of_the_ether() -> None:
    ether = tc.Background(tuple(dp.ETHER), 7)
    assert np.array_equal(tc.closed_strips(ether, 13), dp.closed_strips(13))
    assert not tc.closed_strips(ether, 12).any()
    assert tc.least_closed(backgrounds()["10"], 4)[0] == 1


def test_closed_strips_are_closed_under_random_cells_below() -> None:
    rng = np.random.default_rng(1)
    bg = tc.Background(tuple(dp.ETHER), 7)
    w = 13
    closed = tc.closed_strips(bg, w)
    for _ in range(40):
        a, o = int(rng.integers(4)), int(rng.integers(7))
        r = int(rng.choice(np.flatnonzero(closed[a].any(axis=1))))
        c = 35 + (r - 35 - o) % 7  # (c + o) mod 7 = r
        strip = int(rng.choice(np.flatnonzero(closed[a, r])))
        D = (strip << (c - w + 1)) | int(rng.integers(0, 1 << (c - w + 1)))
        for t, E in enumerate(tc.defect_run(bg, a, o, D, 80)):
            assert E.bit_length() - 1 <= c


def test_census_of_the_ether_against_defect_potential() -> None:
    ether = tc.Background(tuple(dp.ETHER), 7)
    closed = tc.closed_strips(ether, 13)
    heads = np.arange(1 << 7, dtype=np.int64)  # (128,)
    theirs_closed = dp.closed_strips(13)
    for a, o in [(1, 3), (3, 6)]:
        mine = tc.census(ether, a, o, heads, 400, closed, 13)
        theirs = dp.census(7, a, o, 400, theirs_closed)
        assert np.array_equal(mine["strip"] >= 0, theirs["cell"] >= 0)
        assert np.array_equal(np.where(mine["strip"] >= 0, mine["cell"], -1), theirs["cell"])
        assert np.array_equal(mine["top"], theirs["top"])


def test_repeats_against_direct_runs() -> None:
    bg = backgrounds()["1010000"]
    heads = np.arange(1 << 7, dtype=np.int64)  # (128,)
    out = tc.census(bg, 5, 2, heads, 800, None, 0)
    rep = np.flatnonzero(out["repeat"] >= 0)
    assert len(rep) > 0
    for h in rep[:10]:
        t, period = int(out["repeat"][h]), int(out["period"][h])
        run = tc.defect_run(bg, 5, 2, int(h), t)
        assert run[t] == run[t - period] and period % bg.period == 0


def test_condition_of_k_against_direct_runs() -> None:
    for name in ("0", "1000", "1000000", "1110100000"):
        bg = backgrounds()[name]
        heads = np.arange(1 << 7, dtype=np.int64)  # (128,)
        for a, o in tc.alignments(bg)[:3]:
            out = tc.census(bg, a, o, heads, 300, None, 0, in_k=True)
            for h in range(1 << 7):
                assert int(out["broke"][h]) == tc.in_k_steps(bg, a, o, h, int(out["end"][h])), (name, a, o, h)


def test_growing_windows_grow_under_random_cells_below() -> None:
    rng = np.random.default_rng(2)
    for name in ("0", "1000", "11100"):
        bg = backgrounds()[name]
        width, growing = tc.least_rising(bg, 10)
        assert growing is not None
        alive, _ = tc.rising_sets(bg, width)
        assert not (growing & ~alive).any()
        for _ in range(10):
            a, o = int(rng.integers(bg.period)), int(rng.integers(bg.length))
            r = int(rng.choice(np.flatnonzero(growing[a].any(axis=1))))
            c = 30 + (r - 30 - o) % bg.length  # (c + o) mod L = r
            window = int(rng.choice(np.flatnonzero(growing[a, r])))
            D = (window << (c - width + 1)) | int(rng.integers(0, 1 << (c - width + 1)))
            if window >> (width - 1) == 0:  # the window is read below the highest top so far, here c
                continue
            tops = [E.bit_length() - 1 for E in tc.defect_run(bg, a, o, D, 200)]
            record = np.maximum.accumulate(tops)  # (201,) the highest top so far
            assert (np.array(tops) >= record - width + 1).all()
            assert record[-1] >= c + 200 // int(growing.sum())


def test_ether_and_stripes_have_no_growing_window() -> None:
    for name in ("10", "1000000"):
        assert tc.least_rising(backgrounds()[name], 9)[1] is None


def test_alignments_are_distinct_patterns() -> None:
    bg = backgrounds()["11100"]  # travels two cells every step, so one alignment per offset
    assert len(tc.alignments(bg)) == 5
    assert len(tc.alignments(tc.Background(tuple(dp.ETHER), 7))) == 28


@pytest.mark.parametrize("name", ["0", "1000"])
def test_front_speeds(name: str) -> None:
    bg = backgrounds()[name]
    tops = tc.front_speed(bg, 0, 0, 0b101101, 400)
    speed = {"0": 1.0, "1000": 0.5}[name]
    assert abs((tops[400] - tops[200]) / 200 - speed) < 0.02


def test_front_pattern_and_survival() -> None:
    bg = backgrounds()["11100"]
    tops = tc.front_speed(bg, 1, 2, 0b110101, 300)
    assert tc.front_pattern(tops, bg.period, 60) == (15, 5)  # speed 1/3
    assert tc.front_pattern(list(range(50)) + [49] * 3, 1, 10) is None
    alive = tc.k_survival(bg, 6, 40)  # (41,)
    direct = np.zeros(41, dtype=np.int64)  # (41,)
    for a, o in tc.alignments(bg):
        for h in range(1 << 6):
            broke = tc.in_k_steps(bg, a, o, h, 40)
            direct += np.arange(41) < (broke if broke >= 0 else 41)
    assert np.array_equal(alive, direct)
