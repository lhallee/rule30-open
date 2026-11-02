"""Tests for computations/wedge_ladder.py: the reconstruction of a start from its column against forward simulation, the
simulation against rule 30 cell by cell, the peel chart of `WedgeLadderQ01` against the kit's wedge (`kit_wedge`, by cone
rows), and the starts against the forced runs of `wedge_hypotheses`."""

from __future__ import annotations

import itertools

import numpy as np

from computations import wedge_hypotheses as wh
from computations import wedge_ladder as wl


def cell_by_cell(s: tuple[int, ...], steps: int) -> list[dict[int, int]]:
    """The zero-driven left half by the rule, one cell at a time: rows[t][p] for p < 0."""
    m = len(s)
    rows = [{-(i + 1): s[i] for i in range(m)}]
    for _ in range(steps):
        prev = rows[-1]

        def get(p: int) -> int:
            return 0 if p >= 0 else prev.get(p, 0)

        rows.append({p: get(p - 1) ^ (get(p) | get(p + 1)) for p in range(-(m + len(rows) + 1), 0)})
    return rows


def test_simulate_matches_rule() -> None:
    for s in [(1,), (0, 1), (1, 0, 1), (1, 1, 0, 0, 1)]:
        h = wl.simulate(np.array([s], dtype=bool), 8)  # (1, 9, W)
        rows = cell_by_cell(s, 8)
        for t in range(9):
            for i in range(h.shape[2]):
                assert int(h[0, t, i]) == rows[t].get(-(i + 1), 0)


def test_starts_from_column_inverts_simulation() -> None:
    K = 5
    s = np.array(list(itertools.product((0, 1), repeat=K + 1)), dtype=bool)  # (2^(K+1), K + 1)
    col = wl.simulate(s, K)[:, :, 0]  # (2^(K+1), K + 1)
    assert np.array_equal(wl.starts_from_column(col), s)


def test_peel_chart() -> None:
    """peel^d(inverse e)(t) = pair(H(t, -(2d + t + 2)), H(t, -(2d + t + 3))) while column -1 stays black."""
    for n, c in [(2, 2), (3, 3), (4, 2)]:
        h = wl.simulate(wl.starts(n, c), 30)  # (B, 31, W)
        fw = wl.first_white_even(h)  # (B,)
        e = wl.endpoint(h)  # (B, 15)
        for b in range(h.shape[0]):
            K = (int(fw[b]) - 2) // 2  # e_0 .. e_{K-1} binary, column -1 black at the even steps <= 2K
            for d in range(3):
                w = wh.kit_wedge(d, e[b:b + 1, :K])[0]  # (K - d,)
                for t in range(K - d):
                    i = 2 * d + t + 2
                    assert int(w[t]) == 2 * int(h[b, t, i - 1]) + int(h[b, t, i])


def test_starts_are_forced_runs() -> None:
    for n in (2, 3, 4):
        for c in (2, 3):
            r = wl.ladder(n, c)
            assert r.prefixes == 1 << n and r.agree and r.steps_match
            assert r.latest == 2 * r.max_reach + 2
            assert (r.max_reach - n < n + 2) == (r.latest <= 4 * n + 4)
