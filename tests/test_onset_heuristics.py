"""onset_heuristics against direct runs: the diagonal table against the space-time diagram, the onsets against
`scalar_onsets`, the damage times against two full tables, the shifts read off full tables, and the statistics of the
onsets against loops."""

from __future__ import annotations

import numpy as np

from computations import onset_heuristics as oh
from computations.diagonal_cones import diagonal_table
from computations.rule30 import spacetime
from computations.seed_onsets import scalar_onsets
from computations.settled_slope import Diagonals


def seed_table(x: list[int], depth: int, steps: int) -> np.ndarray:
    """D[j, t] = cell(t, lo - t + j) of the row black at lo with cells x_1, x_2, ... right of it, from `spacetime`."""
    lo = 2 * steps
    cells = np.zeros(4 * steps + depth + 2, dtype=np.uint8)  # (n,)
    cells[lo] = 1
    cells[lo + 1:lo + 1 + len(x)] = x
    rows = spacetime(cells, steps)  # (steps + 1, n), row t exact on cells t .. n - 1 - t
    return np.array([[rows[t, lo - t + j] for t in range(steps)] for j in range(depth + 1)], dtype=np.uint8)


def test_tables_and_onsets() -> None:
    assert np.array_equal(oh.diagonal_rows(1, 30, 80), diagonal_table(80, 31))
    rng = np.random.default_rng(0)
    for _ in range(3):
        x = rng.integers(0, 2, 12).tolist()
        v0 = 1 | sum(b << (i + 1) for i, b in enumerate(x))
        D = oh.diagonal_rows(v0, 12, 40)  # (13, 40)
        assert np.array_equal(D, seed_table(x, 12, 40))
        Dl = oh.diagonal_rows(v0, 20, 400)  # (21, 400)
        assert np.array_equal(oh.table_onsets(Dl), scalar_onsets(v0, 20, 400, 64))


def test_reset_identity_and_density() -> None:
    D = oh.diagonal_rows(1, 24, 120).astype(int)  # (25, 120)
    for j in range(23):
        for r in np.flatnonzero(D[j + 1]):
            t = r
            while t + 1 < D.shape[1]:
                assert D[j + 2, t + 1] == 1 ^ (D[j, r:t + 1].sum() % 2)  # the reset identity
                if t + 1 >= D.shape[1] - 1 or D[j + 1, t + 1]:
                    break
                t += 1
    toy = np.array([[1, 0, 1, 1, 0, 0]], dtype=np.uint8)  # (1, 6)
    rho = oh.transient_density(toy, np.array([4]), np.array([0, 0]), np.array([0, 3]))  # (2,)
    assert rho.tolist() == [0.75, 1.0]
    assert np.isnan(oh.transient_density(toy, np.array([0]), np.array([0]), np.array([0]))[0])


def test_density_numbers() -> None:
    """The numbers the entry quotes for j = 50 .. 200."""
    out = oh.density_report()
    assert round(out["T/j"][0], 4) == 1.3325
    assert [round(v, 3) for v in out["[0, T)"]] == [0.311, 0.222, 0.411, 1.0, 0.0]
    assert [round(v, 3) for v in out["[j/2, T)"][:3]] == [0.500, 0.344, 0.643]
    assert round(out["[j/2, T)"][4], 3) == 0.020 and round(out["[j, T)"][4], 3) == 0.046


def test_damage_against_tables() -> None:
    depth, steps = 40, 512
    x = np.random.default_rng(3).integers(0, 2, depth).tolist()
    v0 = 1 | sum(b << (i + 1) for i, b in enumerate(x))
    S = oh.diagonal_rows(1, depth, steps)  # (41, 512)
    for k in (1, 2, 5):
        w0 = v0 ^ (1 << k)
        A, B = oh.diagonal_rows(v0, depth, steps), oh.diagonal_rows(w0, depth, steps)  # (41, 512) each
        last, ta, tb = oh.damage_run(v0, w0, depth, steps, 64)
        diff = A != B  # (41, 512)
        expect = np.where(diff.any(axis=1), steps - np.argmax(diff[:, ::-1], axis=1), 0)  # (41,)
        assert np.array_equal(last, expect) and not last[:k].any()
        assert np.array_equal(ta, A[:, -64:].T) and np.array_equal(tb, B[:, -64:].T)
        for j in range(depth + 1):
            h = oh.diagonal_shift(ta, S[:, -64:].T, j)
            assert h >= 0 and np.array_equal(A[j, 300:400], S[j, 300 + h:400 + h])
    d = oh.damage_survey(30, 12, 30, progress=False)
    assert (d.shift >= 0).all()
    assert np.array_equal(d.clear == -1, d.shift[:, 0] != d.shift[:, 1])
    assert (d.clear <= d.later).all()


def test_onset_statistics(deep_diagonals: Diagonals) -> None:
    rng = np.random.default_rng(1)
    T = rng.integers(0, 50, 41)  # (41,)
    assert oh.doubling_excess(T, 20)[:2] == (max(T[2 * j] - 2 * T[j] for j in range(1, 21)),
                                             min(T[2 * j] - 2 * T[j] for j in range(1, 21)))
    assert oh.base_ratio(T, 3, 4, 20)[0] == min((T[j] + 3) / j for j in range(4, 21))
    S = [T[j + 5] - T[j] for j in range(2, 31)]
    assert np.allclose(oh.dispersion(T, 2, 35, 5), (np.mean(S) / 5, np.var(S) / 5))
    U = np.array([0, 2, 1, 5, 5, 3, 9])  # (7,): F gains 1 at time 0, 2 at 2, 3 at 5, 1 at 9
    assert oh.frontier(U) == (3, 4, 6 / 9)
    # the numbers the entry quotes below depth 10,000
    D = deep_diagonals.onset.astype(np.int64)  # (10001,)
    assert oh.doubling_excess(D, 256)[::2] == (25, 35)
    assert [oh.doubling_excess(D, J)[0] for J in (1000, 4000)] == [93, 180]
    r, j0 = oh.base_ratio(D, 25, 16, 256)
    assert j0 == 245 and round(r, 4) == 1.3306
