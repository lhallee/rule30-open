"""row_white_density against preimages enumerated by brute force, a cell-by-cell run of the single cell, and the
inequalities the entry proves."""

from __future__ import annotations

from itertools import product

import numpy as np

from computations.row_white_density import (black_runs, chain_check, periodic_strip_min, psi, strip_slack, telescope_gap, run_white_bound, single_cell_rows, step,
                                            triangle_area, triangle_counts)


def rule30_cell(a: int, b: int, c: int) -> int:
    return a ^ (b | c)


def test_run_bound_every_row() -> None:
    # every row of length <= 11: each black run of the image has floor(2 (m + 1) / 3) white cells over [u - 1, v]
    for L in range(3, 12):
        for bits in product((0, 1), repeat=L):
            row = np.array(bits, dtype=np.uint8)  # (L,)
            for whites, bound in run_white_bound(row):
                assert whites >= bound


def test_run_bound_is_least() -> None:
    # the least, over every preimage of 1^m on m + 2 cells, of the white cells on its first m + 1 cells
    for m in range(1, 11):
        pre = [w for w in product((0, 1), repeat=m + 2)
               if all(rule30_cell(w[i - 1], w[i], w[i + 1]) for i in range(1, m + 1))]
        assert len(pre) == 4
        assert min((m + 1) - sum(w[:m + 1]) for w in pre) == (2 * (m + 1)) // 3


def test_step_and_runs() -> None:
    row = np.array([0, 1, 0, 0, 1, 1, 0], dtype=np.uint8)
    assert step(row).tolist() == [rule30_cell(*row[i:i + 3]) for i in range(5)]
    assert black_runs(row) == [(1, 1), (4, 5)]


def test_triangle_area() -> None:
    for k in range(1, 30):
        area, w = 0, k
        while w > 0:
            area, w = area + w, w - 2
        assert triangle_area(k) == area <= (k + 1) ** 2 // 4


def test_triangle_counts_and_inequalities() -> None:
    n = 80
    tc = triangle_counts(n, progress=False)
    # a cell-by-cell run of the single cell
    cells = {0: 1}
    for t in range(n):
        seg = [cells.get(i, 0) for i in range(-t, t + 1)]
        assert tc.B[t] == sum(seg) and tc.W[t] == len(seg) - sum(seg)
        cells = {i: rule30_cell(cells.get(i - 1, 0), cells.get(i, 0), cells.get(i + 1, 0)) for i in range(-t - 1, t + 2)}
    for s in range(1, n):
        assert 3 * tc.W[s - 1] + 6 >= 2 * tc.B[s]
    for m in range(1, n + 1):
        Wt, A = int(tc.W[:m].sum()), int(tc.B[:m].sum())
        assert 5 * Wt >= 2 * (m - 1) * (m - 2)
        assert Wt <= int(tc.T[:max(m - 1, 0)].sum())
        if m >= 2:  # M_n is the longest black run of the rows 0..n-2
            assert A * (int(tc.M[:m - 1].max()) + 3) >= 2 * m * m


def test_chain_classification() -> None:
    # every maximal white run strictly inside the image window is a continuation or newborn
    for bits in product((0, 1), repeat=11):
        above = np.array(bits, dtype=np.uint8)  # (11,)
        assert chain_check(above, step(above))[2] == 0
    rows = single_cell_rows(60)  # (60, 121)
    for s in range(1, 60):
        assert chain_check(rows[s - 1], rows[s][1:-1])[2] == 0


def test_potential_and_telescope() -> None:
    for a, b, c in product((0, 1), repeat=3):
        assert 2 * rule30_cell(a, b, c) + psi(b, c) <= 3 * (1 - a) + psi(a, b)
    for L in range(3, 13):
        for bits in product((0, 1), repeat=L):
            assert telescope_gap(np.array(bits, dtype=np.uint8)) >= 0
    # the period-five orbit: (11001) maps to its shift by two, two white cells per period
    x = [1, 1, 0, 0, 1]
    y = [rule30_cell(x[i - 1], x[i], x[(i + 1) % 5]) for i in range(5)]
    assert y == x[2:] + x[:2] and x.count(0) == 2


def test_strip_constants() -> None:
    # the strip constant is 2 for every J, by a direct enumeration of rows
    for J in range(1, 9):
        best = max(2 * sum(rule30_cell(*w[i - 1:i + 2]) for i in range(1, J + 1)) - 3 * (J - sum(w[1:J + 1]))
                   for w in product((0, 1), repeat=J + 2))
        assert best == strip_slack(J) == 2
    # two adjacent black cells leave the right one white in the next row
    for a, b, c in product((0, 1), repeat=3):
        assert (1 - a) + (1 - b) + (1 - rule30_cell(a, b, c)) >= 1
    # periodic orbits: (01) is a fixed point with a black column; strips of 2 and 3 columns reach 1/3 by period 6
    assert periodic_strip_min(1, 2)[0] == 0
    assert abs(periodic_strip_min(3, 6)[0] - 1 / 3) < 1e-12
    assert periodic_strip_min(2, 6)[0] >= 0.25
