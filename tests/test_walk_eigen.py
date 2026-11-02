"""walk_eigen against independent methods: the C program's cycle means and excesses against every simple cycle and
value iteration on the numpy graph, the step against the single cell's walk, and the feature quotient on a witness."""

from __future__ import annotations

from fractions import Fraction

import numpy as np

from computations.walk_eigen import (
    Step,
    brute_cycle_mean,
    excess_graph,
    feature_graph,
    period_row,
    replay,
    run_c,
    single_cell_walk,
    state_index,
    walk_graph,
    walk_step,
    window_codes,
)


def test_cycle_means_and_excess_against_enumeration() -> None:
    for P, mu in [(2, Fraction(1)), (3, Fraction(7, 6)), (4, Fraction(7, 3)), (5, Fraction(15, 8))]:
        g = walk_graph(P)
        row = period_row(P)
        assert row.mu == brute_cycle_mean(g) == mu
        E = excess_graph(g, Fraction(5, 2))  # (4^P P,) in halves
        r = run_c(P, dump=True)
        assert r.E is not None and np.array_equal(r.E[g.cost >= 0], E[g.cost >= 0])
        assert row.R_all == Fraction(int(E.max()), 2)


def test_single_cell_walk_is_a_path_of_the_graph() -> None:
    w, tail, base = single_cell_walk(32, 160, period=16, window=64, progress=False)
    r = replay(w, tail, base, 4, 7, 27)  # the regime of period 4, from the white diagonal 7 to the doubling at 28
    assert r.mismatches == [] and r.crossings == [7] and r.exits == [27] and r.steps == 21
    s = walk_step(0b0011, 0b0110, 1, 4)  # A = 1100, B = 0110 read from time 0: d = 0, C = pair_next(A, B)
    assert s.cost == 1 and s.nexts == [(0b0110, s.nexts[0][1], 2)]


def test_feature_quotient_has_the_costly_loop() -> None:
    P = 5
    g = walk_graph(P)
    cost, s, t = feature_graph(g, window_codes(g, 2, 0), 2).loop
    # A = e_0, B = e_{P-1} at phase 2 steps to (e_{P-1}, e_0) at phase 1: cost P - 1, and every cell of the window
    # ahead of the phase is white in both states, as is the run d = P - 2
    assert cost == P - 1 and s == state_index(1, 1 << (P - 1), 2, P) and t == state_index(1 << (P - 1), 1, 1, P)
    assert walk_step(1, 1 << (P - 1), 2, P) == Step(P - 1, [(1 << (P - 1), 1, 1)])
