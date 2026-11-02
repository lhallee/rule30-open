"""front_walker against the space-time diagram: the walk scanned on a full table, the defect bit read directly."""

from __future__ import annotations

import numpy as np

from computations.diagonal_cones import diagonal_table
from computations.front_walker import (front_law, pair_types, phase_chi2, phase_gaps, step_pairs, step_table,
                                       walk_direct, walk_from_tail, walk_offset, window_max)
from computations.settled_slope import Diagonals, least_periods, stream, white_runs

DEPTH, STEPS, PERIOD, WINDOW = 120, 400, 16, 128


def test_walk_against_spacetime() -> None:
    d = stream(DEPTH, STEPS, period=PERIOD, window=WINDOW, progress=False)
    D = diagonal_table(STEPS, DEPTH + 1)  # (DEPTH + 1, STEPS), from rows run with `step`
    w = walk_from_tail(d.onset, d.tail, STEPS, PERIOD)  # (DEPTH + 1,)
    assert np.array_equal(w, walk_direct(D))
    assert (d.onset <= w).all()  # `pair_repeats_of_walk`
    assert np.flatnonzero(np.diff(w) == 0).tolist() == [2, 7, 28]  # the walk crosses white diagonals at once
    # each step lands just after a black cell of the diagonal it slid along
    assert all(D[j, w[j + 1] - 1] == 1 and not D[j, w[j]:w[j + 1] - 1].any() for j in range(1, DEPTH) if w[j + 1] > w[j])


def test_front_law_against_the_defect() -> None:
    d = stream(DEPTH, STEPS, period=PERIOD, window=WINDOW, progress=False)
    D = diagonal_table(STEPS, DEPTH + 1)  # (DEPTH + 1, STEPS)
    f = front_law(d.onset, d.tail, STEPS, PERIOD)
    for j in range(1, DEPTH):
        S = max(d.onset[j - 1], d.onset[j])
        black = np.flatnonzero(D[j, S:])  # (k,)
        assert f.bound[j - 1] == (S + black[0] + 1 if len(black) else S)
        # the front law: T_{j+1} = C_{j+1} exactly when the defect bit at S_j is 1 (and D_j is not white)
        if len(black):
            assert f.defect[j - 1] == (D[j + 1, S + PERIOD] != D[j + 1, S])


def test_helpers_on_small_cases() -> None:
    w = np.array([0, 1, 3, 3, 5, 9])  # (6,): w_{j+1} - ceil(2j) = 1, 1, -1, -1, 1
    assert walk_offset(w, 2, 1) == 1 and walk_offset(w, 1, 1) == 5
    assert phase_gaps(np.array([1, 0, 0, 1])).tolist() == [0, 2, 1, 0]
    assert phase_chi2(np.arange(32), 16) == 0.0 and phase_chi2(np.zeros(16, dtype=np.int64), 16) == 240.0
    steps = np.array([1, 2, 1, 3, 1])  # (5,)
    assert window_max(steps, 2) == 4 and window_max(steps, 5) == 8
    M = step_pairs(steps, 2)  # (2, 2), the 3 counted as 2
    assert M.tolist() == [[0, 2], [2, 0]]
    tail = np.zeros((4, 4), dtype=np.uint8)  # (4, 4): diagonals 0 .. 3 over a period of 4
    tail[:, 0] = [1, 0, 0, 0]
    tail[:, 1] = [0, 1, 0, 0]
    tail[:, 2] = [0, 0, 1, 0]  # (D_1, D_2) is (D_0, D_1) shifted by one time
    tail[:, 3] = [1, 1, 0, 0]
    assert pair_types(tail, 0, 2, 4) == 1 and pair_types(tail, 0, 3, 4) == 2


def test_numbers_to_depth_10000(deep_diagonals: Diagonals) -> None:
    """The numbers the entry quotes for depths up to 10,000 (the full range is the reproduce command), from the run of
    `stream` to depth 10,000 over 15,600 steps that the tests of both entries share (`deep_diagonals`)."""
    d = deep_diagonals
    w = walk_from_tail(d.onset, d.tail, 15600, d.period)  # (10001,)
    assert (d.onset <= w).all()
    assert np.flatnonzero(np.diff(w) == 0).tolist() == [2, 7, 28, 399]
    assert walk_offset(w, 41, 20) == 1 and walk_offset(w, 2, 1) == 208


def test_step_table_against_spacetime() -> None:
    """The step table against the diagonals read directly: the least period, uniform-phase gap and longest cyclic white
    run of the last 64 times of each diagonal, and the steps of `walk_direct`."""
    d = stream(DEPTH, STEPS, period=PERIOD, window=WINDOW, progress=False)
    D = diagonal_table(STEPS, DEPTH + 1)  # (DEPTH + 1, STEPS)
    w = walk_direct(D)  # (DEPTH + 1,)
    rows = step_table(w, least_periods(d.tail), white_runs(d.tail), d.tail)
    last = D[:, STEPS - 64:]  # (DEPTH + 1, 64), the settled part of every diagonal here
    expect: dict[int, list[tuple[int, float, int]]] = {}
    for j in range(1, DEPTH):
        word = last[j]  # (64,)
        if not word.any():
            continue
        p = next(q for q in (1, 2, 4, 8, 16, 32) if np.array_equal(word, np.roll(word, q)))
        twice = np.concatenate([word, word])  # (128,)
        gaps = [int(np.flatnonzero(twice[s:])[0]) for s in range(64)]
        runs = [len(r) for r in "".join(map(str, twice)).split("1")]
        expect.setdefault(p, []).append((int(w[j + 1] - w[j]), 1 + float(np.mean(gaps)), 1 + max(runs)))
    assert [r.period for r in rows] == sorted(expect)
    for r in rows:
        e = expect[r.period]
        assert r.count == len(e) and r.max_step == max(x[0] for x in e)
        assert np.isclose(r.mean_step, np.mean([x[0] for x in e]))
        assert np.isclose(r.mean_cost, np.mean([x[2] for x in e]))
        assert np.isclose(r.mean_phase_gap, np.mean([x[1] for x in e]))
