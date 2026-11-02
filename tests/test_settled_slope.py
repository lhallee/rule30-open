"""settled_slope against the space-time diagram, run_slope_routes' skeleton and window-by-window checks."""

from __future__ import annotations

import numpy as np

from computations.diagonal_cones import diagonal_table
from computations.run_slope_routes import skeleton_from_table
from computations.settled_slope import (Diagonals, alternations, black_slope, by_period, cost_offset, least_periods,
                                        pair_onset_bound, settling_offset, stream, white_runs)

DEPTH, STEPS, PERIOD, WINDOW = 120, 400, 16, 128


def brute_onset(x: np.ndarray, p: int) -> int:
    """The least T with x(t + p) = x(t) for every T <= t < len(x) - p, by scanning back from the end."""
    # x: (steps,)
    T = len(x) - p
    while T > 0 and x[T - 1 + p] == x[T - 1]:
        T -= 1
    return T


def brute_alternation(y: np.ndarray, z: np.ndarray) -> int:
    """The largest k such that some window of k consecutive times has z = not y at every time and y changing between
    consecutive times (the Lean `AntiWindow` with A = k - 1), by trying every window."""
    # y, z: (window,)
    best = 0
    for s in range(len(y)):
        for e in range(s, len(y)):
            if all(z[t] != y[t] for t in range(s, e + 1)) and all(y[t + 1] != y[t] for t in range(s, e)):
                best = max(best, e - s + 1)
    return best


def test_stream_against_spacetime() -> None:
    d = stream(DEPTH, STEPS, period=PERIOD, window=WINDOW, progress=False)
    D = diagonal_table(STEPS, DEPTH + 1)  # (DEPTH + 1, STEPS), from rows run with `step`
    assert np.array_equal(d.tail, D[:, STEPS - WINDOW:].T)
    assert [int(x) for x in d.onset] == [brute_onset(D[j], PERIOD) for j in range(DEPTH + 1)]


def test_periods_and_white_runs_against_skeleton() -> None:
    d = stream(DEPTH, STEPS, period=PERIOD, window=WINDOW, progress=False)
    sk = skeleton_from_table(d.tail.T)  # periods and white runs read from the last quarter of the rows
    assert np.array_equal(least_periods(d.tail), sk.period)
    assert np.array_equal(white_runs(d.tail), sk.white_run)


def test_alternations_against_every_window() -> None:
    d = stream(60, 200, period=PERIOD, window=40, progress=False)
    alt = alternations(d.tail)  # (60,)
    assert [int(m) for m in alt] == [brute_alternation(d.tail[:, j], d.tail[:, j + 1]) for j in range(60)]


def test_pair_onset_bound_dominates_the_onsets() -> None:
    """`pair_repeats_of_white_runs`: the pair (D_j, D_{j+1}) repeats from 1 + c_1 + ... + c_j."""
    d = stream(DEPTH, STEPS, period=PERIOD, window=WINDOW, progress=False)
    Q = pair_onset_bound(white_runs(d.tail))  # (DEPTH + 1,)
    pair = np.maximum(d.onset[:-1], d.onset[1:])  # (DEPTH,)
    assert (pair <= Q[:-1]).all()
    assert Q[:3].tolist() == [1, 2, 2]  # c_1 = 1 (D_1 black), c_2 = 0 (D_2 white)


def test_offsets_on_small_cases() -> None:
    onset = np.array([0, 2, 3, 5, 9])  # (5,)
    # ceil(3j/2) = 0, 2, 3, 5, 6: delta = 3 (at j = 4)
    assert settling_offset(onset, 3, 2) == 3
    white = np.array([0, 0, -1, 2, 1])  # (5,): c = -, 1, 0, 3, 2; sums 0, 1, 1, 4, 6
    assert cost_offset(white, 1) == 2 and cost_offset(white, 2) == 0
    assert black_slope(3, 2) == (3, 13) and black_slope(27, 20) == (21, 115) and black_slope(6, 1) == (15, 29)


def test_numbers_to_depth_10000(deep_diagonals: Diagonals) -> None:
    """The numbers the entry quotes for depths up to 10,000 (the full range is the reproduce command), from the run of
    `stream` to depth 10,000 over 15,600 steps that the tests of both entries share (`deep_diagonals`)."""
    d = deep_diagonals
    white = white_runs(d.tail)  # (10001,)
    alt = alternations(d.tail)  # (10000,)
    assert np.flatnonzero(white < 0).tolist() == [2, 7, 28, 399]
    assert settling_offset(d.onset, 3, 2) == 0 and settling_offset(d.onset, 27, 20) == 10
    assert int(alt.max()) == 8 and cost_offset(white, 6) == 0
    rows = {r.period: r for r in by_period(least_periods(d.tail), white, alt)}
    assert rows[16].max_white == 15 and rows[8].max_white == 7
