"""onset_edge and edge_game against direct simulation: the edge law on all 128 local cases, the running maximum of the
onsets from a space-time table, the background rows from the Rule 30 step, and the game's value against a linear
program built from an explicit simulation of the rows."""

from __future__ import annotations

import numpy as np

from computations.edge_game import game_value, lp_value
from computations.onset_edge import (RETREAT_MORE, background_row, background_words, edge_move, law_cases,
                                     random_edges, running_onsets, single_cell_edge, step_row)


def rule30_rows(rows: np.ndarray) -> np.ndarray:
    """One step of Rule 30 on each row, with white cells outside."""
    # rows: (n, w)
    pad = np.pad(rows, ((0, 0), (1, 1)))  # (n, w + 2)
    return pad[:, :-2] ^ (pad[:, 1:-1] | pad[:, 2:])  # (n, w)


def test_edge_law_on_all_local_cases() -> None:
    rng = np.random.default_rng(0)
    cases = law_cases()
    assert len(cases) == 128
    w, L, fills = 16, 6, 8  # cells 0 .. 15, edge at cell 6, eight random fillings of the other cells per case
    X = rng.integers(0, 2, (128 * fills, w), dtype=np.uint8)  # (n, w)
    Y = X.copy()  # (n, w): equal left of L - 2
    Y[:, L + 3:] = rng.integers(0, 2, (128 * fills, w - L - 3), dtype=np.uint8)  # independent right of L + 2
    law = np.zeros(128 * fills, dtype=np.int64)  # (n,)
    for c, (s2, s1, x, y) in enumerate(cases):
        rows = slice(c * fills, (c + 1) * fills)
        X[rows, L - 2], X[rows, L - 1], Y[rows, L - 2], Y[rows, L - 1] = s2, s1, s2, s1
        X[rows, L:L + 3], Y[rows, L:L + 3] = x, y
        law[rows] = edge_move(s1, x, y)
    nX, nY = rule30_rows(X), rule30_rows(Y)  # (n, w)
    new = np.argmax(nX != nY, axis=1)  # (n,): every pair still differs somewhere
    move = new - L
    exact = law != RETREAT_MORE
    assert (move[exact] == law[exact]).all()
    assert (move[~exact] >= 2).all()
    assert {int(m) for m in move[~exact]} != {2}  # the retreat beyond L + 1 is not always to L + 2


def test_running_onsets_against_a_table() -> None:
    depth, steps, P = 60, 260, 16
    run = single_cell_edge(depth, steps, P, progress=False)
    assert run.violations == 0
    E = running_onsets(run.edge, depth)  # (depth + 1,)
    width = 2 * steps + 3
    row = np.zeros((1, width), dtype=np.uint8)  # (1, width): cell x at index x + steps + 1
    row[0, steps + 1] = 1
    D = np.zeros((depth + 1, steps), dtype=np.uint8)  # (depth + 1, steps): D_j(t) = cell(t, j - t)
    for t in range(steps):
        D[:, t] = row[0, steps + 1 - t:steps + 1 - t + depth + 1]
        row = rule30_rows(row)
    bad = D[:, :steps - P] != D[:, P:]  # (depth + 1, steps - P)
    onset = np.array([np.flatnonzero(b)[-1] + 1 if b.any() else 0 for b in bad])  # (depth + 1,)
    assert np.array_equal(E, np.maximum.accumulate(onset))
    assert E.max() < steps - 4 * P


def test_background_rows_and_random_edges() -> None:
    rng = np.random.default_rng(1)
    D = background_words(8, 120, rng)  # (120, 8)
    row = background_row(D, 0)
    for t in range(1, 30):
        row = step_row(row, 120)
        good = ((1 << (120 - t)) - 1) >> t << t  # cells t .. 119 - t feel neither end
        assert (row ^ background_row(D, t)) & good == 0
    r = random_edges(2, 60, "flip", 3, burn=5, progress=False)
    assert r.violations == 0 and len(r.moves) == 2 * 55


def test_game_values() -> None:
    assert abs(game_value(0).upper - 0.5) < 1e-9
    g1 = game_value(1)
    assert abs(g1.upper - 0.6) < 1e-9 and g1.upper - g1.lower < 1e-9
    assert abs(lp_value(1) - 0.6) < 1e-7
