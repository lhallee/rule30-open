"""Tests of computations.seed_certificate: the window abstraction against every seed of a few cells (exact for a wide
window, sound for a narrow one), the C program against the Python one, the one-step jumps against a direct run, the beam
against the exhaustive driven maxima, and the cycle means against Karp's algorithm."""

from __future__ import annotations

from collections.abc import Iterator
from fractions import Fraction

import numpy as np
import pytest

from computations import seed_certificate as sc
from computations import seed_onsets as so


@pytest.fixture(scope="module", autouse=True)
def quick_compile() -> Iterator[None]:
    mp = pytest.MonkeyPatch()
    mp.setenv("SEED_ONSETS_FAST", "0")
    yield
    mp.undo()


@pytest.fixture(scope="module")
def table10() -> np.ndarray:
    return so.onset_table(10, 48)  # (2^10, 11)


def concrete_key(s: int, J: int, h: int, P: int, H: int = 64) -> tuple[int, int, int]:
    """The abstract state of the seed with cells x_i = bit i - 1 of s at depth J, packed by hand, with R_J and T_J:
    one Python integer per time."""
    v = 1 | (s << 1)
    mask = (1 << (J + 1)) - 1
    rows = []
    for _ in range(H):
        rows.append(v)
        v = ((v << 2) ^ ((v << 1) | v)) & mask
    D = [[(r >> i) & 1 for r in rows] for i in range(J + 1)]
    T = []
    for i in range(J + 1):
        bad = [t for t in range(H - P) if D[i][t] != D[i][t + P]]
        T.append(bad[-1] + 1 if bad else 0)
    R = max(T)
    a = min(R, h)
    pw = sum(D[J - 1][R + k] << k for k in range(P)) | sum(D[J][R + k] << (P + k) for k in range(P))
    win = 0
    for k in range(h - a, h):
        t = R - h + k
        win |= D[J - 1][t] << k
        win |= D[J][t] << (h + k)
    key = (pw << (2 * h + 5)) | (a << (2 * h)) | win
    return key, R, T[J]


def test_wide_window_is_exact(table10: np.ndarray) -> None:
    run = sc.window_bounds(10, 16, P=8, progress=False)
    M = table10.max(axis=0)  # (11,)
    assert (run.bound == np.maximum.accumulate(M)).all()
    assert (run.onset == M).all()
    assert run.exact.all()


def test_narrow_window_is_sound(table10: np.ndarray) -> None:
    for h in (2, 4):
        run = sc.window_bounds(10, h, P=8, progress=False)
        assert run.keys is not None and run.values is not None
        found = dict(zip(run.keys.tolist(), run.values.tolist()))
        for s in range(0, 1 << 10, 7):
            key, R, T = concrete_key(s, 10, h, 8)
            assert R == np.max(table10[s]) and T == table10[s, 10]
            assert found[key] >= R
            assert run.onset[10] >= T


def test_c_matches_python() -> None:
    for P in (8, 16):
        a = sc.window_bounds(30, 4, P=P, progress=False)
        b = sc.window_bounds_c(30, 4, P=P)
        assert (a.bound == b.bound).all() and (a.onset == b.onset).all() and (a.states == b.states).all()


# the exact maxima M_0 .. M_76 of findings/diagonals/seed-uniform-onsets.md (branch and bound of seed_onsets)
KNOWN = [0, 1, 2, 2, 4, 5, 6, 8, 7, 11, 12, 14, 14, 16, 17, 19, 22, 21, 26, 24, 29, 29, 31, 30, 33, 34, 35, 36, 37, 36,
         39, 40, 42, 42, 46, 45, 52, 48, 54, 56, 61, 58, 63, 62, 67, 65, 70, 68, 77, 71, 79, 80, 82, 81, 84, 84, 88, 85,
         90, 91, 92, 93, 93, 97, 94, 99, 100, 103, 102, 105, 105, 105, 106, 105, 108, 107, 110]


def test_window_bounds_the_known_maxima() -> None:
    run = sc.window_bounds_c(76, 5, P=8)
    M = np.array(KNOWN)  # (77,)
    assert (run.onset >= M).all() and (run.onset[:49] == M[:49]).all()
    assert (run.bound >= np.maximum.accumulate(M)).all()


def test_jumps_match_driven_one_step() -> None:
    _, tail = so.skeleton(60)  # (64, 61)
    c = sc.jump_costs(tail)  # (61,)
    for n in range(29, 61, 3):
        assert sc.driven_one_step(tail[:8, n - 1], tail[:8, n], 8) == c[n]


def test_beam_matches_exhaustive() -> None:
    _, tail = so.skeleton(40)  # (64, 41)
    n = 40
    G = np.zeros(11, dtype=np.int64)  # (11,)
    N = np.zeros(10, dtype=np.int64)  # (10,)
    for phi in range(8):
        a, b = tail[phi:phi + 8, n - 1], tail[phi:phi + 8, n]
        G = np.maximum(G, so.driven_max(a, b, 10, 88))
        N = np.maximum(N, sc.driven_beam(a, b, 10, 256))
    assert (N == G[1:]).all()


def karp(succ: np.ndarray, weight: np.ndarray) -> Fraction:
    """The largest cycle mean by Karp's theorem, from a virtual source joined to every node."""
    n = len(succ)
    neg = None
    D = [[0] * n] + [[neg] * n for _ in range(n)]
    for k in range(1, n + 1):
        for u in range(n):
            if D[k - 1][u] is None:
                continue
            for c in range(succ.shape[1]):
                v = int(succ[u, c])
                if v >= 0:
                    val = D[k - 1][u] + int(weight[u, c])
                    if D[k][v] is None or val > D[k][v]:
                        D[k][v] = val
    best = None
    for v in range(n):
        if D[n][v] is None:
            continue
        worst = min(Fraction(D[n][v] - D[k][v], n - k) for k in range(n) if D[k][v] is not None)
        best = worst if best is None or worst > best else best
    assert best is not None
    return best


def test_howard_matches_karp() -> None:
    rng = np.random.default_rng(3)
    for _ in range(20):
        n = 12
        succ = rng.integers(0, n, size=(n, 2))  # (n, 2)
        weight = rng.integers(0, 6, size=(n, 2))  # (n, 2)
        g = sc.Graph(np.arange(n, dtype=np.uint64), succ, weight)
        mean, cycle = sc.max_cycle_mean(g)
        assert mean == karp(succ, weight)
        sc.check_certificate(g, mean)
    g = sc.pair_graph(4, 1)
    mean, cycle = sc.max_cycle_mean(g)
    assert mean == Fraction(7, 3) == karp(g.succ, g.weight)
    total = sum(int(g.weight[v][g.succ[v] == cycle[(i + 1) % len(cycle)]].max()) for i, v in enumerate(cycle))
    assert Fraction(total, len(cycle)) == mean
