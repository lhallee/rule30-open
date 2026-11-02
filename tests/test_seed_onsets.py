"""Tests of computations.seed_onsets: the bit-packed onset table against one seed at a time, the C searches against the
table, and the driven relaxation against a scalar run."""

from __future__ import annotations

from collections.abc import Iterator

import numpy as np
import pytest

from computations import seed_onsets as so


@pytest.fixture(scope="module")
def table12() -> np.ndarray:
    return so.onset_table(12, 60)  # (2^12, 13)


@pytest.fixture(scope="module", autouse=True)
def quick_compile() -> Iterator[None]:
    mp = pytest.MonkeyPatch()
    mp.setenv("SEED_ONSETS_FAST", "0")
    yield
    mp.undo()


def test_table_matches_scalar() -> None:
    J = 9
    T = so.onset_table(J, 50)  # (2^J, J + 1)
    for s in range(1 << J):
        assert (so.scalar_onsets(1 | (s << 1), J, 50, 8) == T[s]).all()


def test_scalar_single_cell_matches_settled_slope() -> None:
    onset, _ = so.skeleton(40)  # (41,), period 64
    assert (so.scalar_onsets(1, 40, 200, 64) == onset).all()


def test_known_maxima(table12: np.ndarray) -> None:
    assert table12.max(axis=0).tolist() == [0, 1, 2, 2, 4, 5, 6, 8, 7, 11, 12, 14, 14]


def test_exhaustive_search_matches_table(table12: np.ndarray) -> None:
    s = so.exhaustive_max(12, 64)
    M = table12.max(axis=0)  # (13,)
    assert (s.best == M).all()
    for j in range(13):
        reach = table12[:, j] == M[j]  # (2^12,)
        # seeds x_1 .. x_j reaching the maximum: count distinct prefixes
        prefixes = {int(p) & ((1 << j) - 1) for p in np.flatnonzero(reach)}
        assert s.count[j] == len(prefixes)
        x = s.seeds[j]
        assert so.scalar_onsets(so.seed_vector(x), j, 64, 8)[j] == M[j]


def test_pruned_search_matches_table(table12: np.ndarray) -> None:
    M = table12.max(axis=0)  # (13,)
    for K in (0, 6):
        s = so.pruned_max(12, 64, K, split=4)
        assert (s.best == M).all() and s.largest <= 64 - 9
        for j in range(13):
            assert so.scalar_onsets(so.seed_vector(s.seeds[j]), j, 64, 8)[j] == M[j]


def test_driven_matches_scalar() -> None:
    _, tail = so.skeleton(12)  # (64, 13)
    for i, phi in ((5, 0), (9, 3), (11, 6)):
        a, b = tail[phi:phi + 8, i - 1], tail[phi:phi + 8, i]  # (8,), (8,)
        m = 7
        G = so.driven_max(a, b, m, 60)  # (m + 1,)
        ref = np.max([so.driven_scalar(a, b, w, m, 60) for w in range(1 << m)], axis=0)  # (m + 1,)
        assert (G == ref).all()


def test_driven_bound_holds(table12: np.ndarray) -> None:
    """T_{i+k} <= S_i + G_k(pair at S_i) for every seed of 12 cells, the pair read from the seed's own diagonals."""
    J, H = 12, 60
    S = so.pair_onsets(table12)  # (2^J, J + 1)
    for s in range(0, 1 << J, 97):
        v = 1 | (s << 1)
        hist = np.zeros((H, J + 1), dtype=np.uint8)  # (H, J + 1)
        for t in range(H):
            hist[t] = [(v >> k) & 1 for k in range(J + 1)]
            v = ((v << 2) ^ ((v << 1) | v)) & ((1 << (J + 1)) - 1)
        for i in (4, 8):
            a, b = hist[S[s, i]:S[s, i] + 8, i - 1], hist[S[s, i]:S[s, i] + 8, i]  # (8,), (8,)
            G = so.driven_max(a, b, J - i, H)  # (J - i + 1,)
            assert (table12[s, i:] <= S[s, i] + G).all()


def test_same_skeleton(table12: np.ndarray) -> None:
    assert so.same_skeleton(table12, 12, 60)


def test_lemma_helpers() -> None:
    M = np.array([0, 1, 2, 2, 4, 5])  # (6,)
    assert so.offset_over(M) == 0
    assert so.pair_max(M).tolist() == [0, 1, 2, 2, 4, 5]
    assert so.subadditive_failures(so.pair_max(M)) == [(1, 3, 1), (2, 3, 1)]


def test_table_matches_rule30_cells() -> None:
    """The onsets of every seed of 8 cells from Rule 30 itself: the row as a Python integer, cell lo at bit O, the
    diagonal cells read at lo - t + j, and the onset taken with period 16 rather than 8."""
    J, H, P = 8, 60, 16
    T = so.onset_table(J, H)  # (2^J, J + 1)
    O = H + 2
    for s in range(1 << J):
        row = (1 | (s << 1)) << O  # cells lo .. lo + J
        diags = []
        for t in range(H):
            diags.append((row >> (O - t)) & ((1 << (J + 1)) - 1))
            row = (row << 1) ^ (row | (row >> 1))
        last = [-1] * (J + 1)
        for t in range(H - P):
            d = diags[t] ^ diags[t + P]
            for j in range(J + 1):
                if (d >> j) & 1:
                    last[j] = t
        assert [v + 1 for v in last] == T[s].tolist()
