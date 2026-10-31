"""Tests for computations/diagonal_cones.py against independent checks."""

from __future__ import annotations

import itertools

import numpy as np

from computations.diagonal_cones import (
    alternating_window,
    diagonal_table,
    longest_open_black,
    longest_open_strip,
    settled_violations,
    longest_open_white,
    settling,
    slope_black,
    slope_white,
    white_block_window,
    white_run_violations,
)
from computations.rule30 import spacetime


def _forced_alternating_cells(run: int, layers: int) -> dict[int, np.ndarray]:
    """By enumeration: for each s <= layers, the cells (by x, center at 0) of row a - s that every s-step preimage of
    the alternating cells -(run - 1) .. 0 (black center) shares. Each s-step preimage is found by trying every choice
    of the 2 s cells right of the window and applying the rule backward through left-permutivity."""
    out: dict[int, np.ndarray] = {}
    target = [1 if (-x) % 2 == 0 else 0 for x in range(-(run - 1), 1)]  # cell x = -k is black exactly for even k
    for s in range(1, layers + 1):
        words = []
        for free in itertools.product([0, 1], repeat=2 * s):
            layer = list(target)  # cells at x = -(run - 1) .. 0 of row a
            lo = -(run - 1)
            bits = iter(free)
            for _ in range(s):
                # previous row covers lo - 1 .. hi + 1 where hi = lo + len(layer) - 1; cells hi, hi + 1 are free
                prev = [0] * (len(layer) + 2)
                prev[-1], prev[-2] = next(bits), next(bits)
                for i in range(len(layer) - 1, -1, -1):
                    # layer[i] is cell lo + i; its left neighbor is prev[i], center prev[i + 1], right prev[i + 2]
                    prev[i] = layer[i] ^ (prev[i + 1] | prev[i + 2])
                layer, lo = prev, lo - 1
            words.append((lo, layer))
        lo = words[0][0]
        grid = np.array([w for _, w in words])  # (4**s, run + 2 s)
        forced = (grid == grid[0]).all(axis=0)  # (run + 2 s,)
        out[s] = np.array([lo + i for i in np.nonzero(forced)[0]])
    return out


def test_alternating_trapezoid_is_exactly_the_forced_cells() -> None:
    run, a = 12, 40
    forced = _forced_alternating_cells(run, 3)
    for s, cells in forced.items():
        assert cells.min() == -(run - 1) - s and cells.max() == -4 * s
        assert len(cells) == cells.max() - cells.min() + 1
        # the window function agrees: diagonal j meets time a - s at x = j - a + s
        j = np.arange(0, a)
        lo, hi = alternating_window(a, run, 0, j)
        inside = (lo <= a - s) & (a - s <= hi)
        x = j - a + s
        assert np.array_equal(inside, (x >= cells.min()) & (x <= cells.max()))


def test_diagonal_table_matches_spacetime() -> None:
    steps, depth = 60, 20
    cells = np.zeros(2 * steps + 1, dtype=np.uint8)
    cells[steps] = 1
    rows = spacetime(cells, steps)  # (steps + 1, 2 steps + 1), exact on cells t .. n - 1 - t
    D = diagonal_table(steps, depth)  # (depth, steps)
    for t in range(steps):
        for j in range(depth):
            assert D[j, t] == rows[t, steps + j - t]


def test_settling_is_exact_periodicity() -> None:
    D = diagonal_table(700, 80)  # (80, 700)
    s = settling(D, 128)
    for j in range(80):
        p, t0 = int(s.period[j]), int(s.onset[j])
        assert np.array_equal(D[j, t0 + p:], D[j, t0:-p])
        assert t0 == 0 or D[j, t0 - 1 + p] != D[j, t0 - 1]
    assert s.onset[2] <= 3 and s.onset[3] <= 3  # the rigid diagonals settle at once
    assert s.period[3] == 2 and s.period[2] == 1


def test_adjacent_alternating_diagonals_reach_the_edge() -> None:
    # D_j(t) = D_{j+2}(t + 1) xor (D_{j+1}(t) or D_{j+2}(t)): from an alternating pair the diagonals before it alternate
    t = np.arange(40)
    top, below = (t % 2).astype(np.uint8), (1 - t % 2).astype(np.uint8)  # D_{j+2}, D_{j+1} with D_{j+1} = not D_{j+2}
    for _ in range(10):
        new = top[1:] ^ (below[:-1] | top[:-1])  # D_j(t) for t < len - 1
        assert np.array_equal(new, top[:-1])  # D_j = D_{j+2}, alternating
        top, below = below[:-1], new
        assert np.array_equal(below, 1 - top)


def test_white_runs_have_the_structure_the_argument_uses() -> None:
    checked, violations = white_run_violations(500)
    assert checked > 50 and violations == []


def test_longest_open_runs_follow_the_slopes() -> None:
    gamma, period, a = 2.5, 2, 600
    black = longest_open_black(a, gamma, period, 8)
    assert abs(black - slope_black(gamma) * a) <= 2 * period + 8
    white, ell = longest_open_white(300, gamma, period, 8)
    assert abs(white - slope_white(gamma) * 300) <= 2 * period + 12 and ell <= white
    lo, hi = white_block_window(100, 10, np.array([95, 105]))
    assert list(lo) == [100, 100] and list(hi) == [100 + (95 - 100 + 10) // 2, 100 + (105 - 100 + 10) // 2]


def test_true_strip_of_fixed_depth_leaves_slope_three_fifths() -> None:
    D = diagonal_table(400, 20)  # (20, 400)
    runs = {a: longest_open_strip(D, a, 5) for a in (200, 300)}
    assert runs == {200: 118, 300: 178}  # 3 a / 5 - 2: depth 5 shifts the bound, not its slope
    assert longest_open_strip(D, 300, 10) < runs[300] < 3 * 300 // 5


def test_settled_violations_counts_unsettled_diagonals() -> None:
    D = diagonal_table(400, 60)  # (60, 400)
    assert settled_violations(D) == 0  # the true orbit repeats with period 16 from 3 j / 2 on
    broken = D.copy()
    broken[20, -3] ^= 1  # one flipped late cell of diagonal 20 breaks its period
    broken[30, 20] ^= 1  # a flip before the settling time 45 of diagonal 30 changes nothing past it
    assert settled_violations(broken) == 1
