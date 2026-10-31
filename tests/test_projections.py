"""Patches under the invariant measure and in diagrams, the exact chi-square, the onsets of the left diagonals and the
column spectra, against direct runs of the rule, plain enumeration and closed forms."""

from __future__ import annotations

import itertools

import numpy as np

from computations import projections as pj
from computations.left_diagonals import diagonals
from computations.rule30 import spacetime


def plain_patch(base: list[int], h: int, w: int) -> tuple[int, ...]:
    """The patch above a base row, by running the rule on a list."""
    rows, out = list(base), []
    for k in range(h):
        out.extend(rows[h - 1 - k:h - 1 - k + w])
        rows = [rows[i - 1] ^ (rows[i] | rows[i + 1]) for i in range(1, len(rows) - 1)]
    return tuple(out)


def test_cone_patches_against_spacetime() -> None:
    """Row k of a patch is row k of the spacetime diagram over the middle w cells of its base."""
    rng = np.random.default_rng(1)
    h, w = 3, 4
    cells = rng.integers(0, 2, 40, dtype=np.uint8)  # (40,)
    diagram = spacetime(cells, h - 1).astype(np.uint8)  # (h, 40)
    for x in range(h - 1, 40 - w - h + 2):
        base = cells[x - (h - 1):x + w + h - 1][None, :]  # (1, w + 2(h - 1))
        assert np.array_equal(pj.cone_patches(base, h, w)[0], diagram[:, x:x + w].reshape(-1))


def test_exact_law_against_plain_enumeration() -> None:
    """h = 1 is uniform; the column pair (h, w) = (2, 1) is uniform; (3, 3) matches a plain enumeration."""
    support, probs = pj.exact_law(1, 5)
    assert len(support) == 32 and np.allclose(probs, 1 / 32)
    support, probs = pj.exact_law(2, 1)
    assert len(support) == 4 and np.allclose(probs, 1 / 4)
    h, w = 3, 3
    counts: dict[int, int] = {}
    for base in itertools.product((0, 1), repeat=pj.base_width(h, w)):
        code = sum(bit << i for i, bit in enumerate(plain_patch(list(base), h, w)))
        counts[code] = counts.get(code, 0) + 1
    support, probs = pj.exact_law(h, w)
    assert support.tolist() == sorted(counts)
    assert np.allclose(probs, [counts[c] / 2 ** pj.base_width(h, w) for c in sorted(counts)])
    assert np.array_equal(pj.codes_of(pj.bits_of(support, h * w)), support)


def test_exact_covariance() -> None:
    """Cells of one row are independent; cell (t + 1, x) has correlation -1/2 with (t, x - 1) and 0 with (t, x)."""
    cov = pj.exact_covariance(2, 3)  # (6, 6): cells 0 .. 2 are row t, 3 .. 5 row t + 1
    assert np.allclose(np.diag(cov), 1)
    assert np.allclose(cov[:3, :3], np.eye(3))
    assert np.isclose(cov[4, 0], -0.5) and np.isclose(cov[4, 1], 0.0)
    rng = np.random.default_rng(2)
    s = 2.0 * pj.null_patches(40_000, 2, 3, rng) - 1  # (40000, 6)
    assert np.abs(s.T @ s / len(s) - cov).max() < 0.03


def test_chi_square_moments() -> None:
    """The exact mean K - 1 and variance of Pearson's statistic against multinomial draws."""
    rng = np.random.default_rng(3)
    probs = rng.random(12) + 0.2  # (12,)
    probs /= probs.sum()
    n = 30
    draws = rng.multinomial(n, probs, size=40_000)  # (40000, 12)
    stats = (((draws - n * probs) ** 2) / (n * probs)).sum(axis=1)  # (40000,)
    zs = np.array([pj.chi_square(d, probs).z for d in draws[:2000]])  # (2000,)
    assert abs(stats.mean() - 11) < 0.15
    variance = 2 * 11 + ((1 / probs).sum() - 144 - 24 + 2) / n
    assert abs(stats.var() / variance - 1) < 0.06
    assert abs(zs.mean()) < 0.1 and abs(zs.std() - 1) < 0.08


def test_diagram_patches_against_spacetime() -> None:
    """Patches of the single cell and of a random row, read from integer rows, are slices of the spacetime diagram."""
    rng = np.random.default_rng(4)
    h, w = 3, 4
    times = [20, 30, 41]
    support, _ = pj.exact_law(h, w)
    for kind in ("seed", "random"):
        row, origin = pj.make_diagram(kind, times[-1] + h, h, w, rng)
        span = 2 * (times[-1] + h) + w + 4  # rows of the slice stay exact on |x| <= t + w
        lo = origin - span
        # (2 span,): cell lo - origin + i
        cells = np.array([(row >> (lo + i)) & 1 for i in range(2 * span)], dtype=np.uint8)
        diagram = spacetime(cells, times[-1] + h).astype(np.uint8)  # (steps + 1, 2 span)
        positions = lambda t: pj.lattice(-t, t - w + 1, 5, rng)  # noqa: E731
        for t, x, patches in pj.diagram_patches(row, origin, times, h, w, positions, progress=False):
            for xi, p in zip(x, patches):
                i = xi + origin - lo
                assert np.array_equal(p, diagram[t:t + h, i:i + w].reshape(-1))
            pj.pattern_index(pj.codes_of(patches), support)


def test_profile_separates_the_left_side() -> None:
    """At times 200 .. 800 the seed's patches left of x / t = -0.5 fail the exact test; the random row's do not."""
    rng = np.random.default_rng(5)
    edges = np.array([-1.0, -0.5, -0.2, 0.2, 0.9])
    _, probs = pj.exact_law(2, 3)
    seed = pj.profile_rows(pj.position_counts("seed", 2, 3, 200, 800, 8, edges, "ratio", rng)[0], probs)
    control = pj.profile_rows(pj.position_counts("random", 2, 3, 200, 800, 8, edges, "ratio", rng)[0], probs)
    assert seed[0].z > 20
    assert all(abs(r.z) < 5 for r in control) and abs(seed[2].z) < 5


def test_onsets_against_full_table() -> None:
    """The streamed onsets equal the least s with D_j(t + 16) = D_j(t) on a full table, and the settling constants
    of the settled-runs finding (1.4792 at depth 48, 1.4112 at 107, 1.3150 at 1,492, depths to 1,499, 3,600 steps)."""
    steps, depth = 300, 160
    table = diagonals(steps, depth, steps)  # (depth, steps): times 0 .. steps - 1
    onset = pj.onsets(steps - 1, depth, progress=False)  # (depth,)
    for j in range(depth):
        s = next(s for s in range(steps) if np.array_equal(table[j, s + 16:], table[j, s:steps - 16]))
        assert onset[j] == s
    onset = pj.onsets(3600, 1500, progress=False)  # (1500,)
    for lo, ratio, at in ((8, 1.4792, 48), (100, 1.4112, 107), (400, 1.3150, 1492)):
        j = np.arange(lo, 1500)  # (1500 - lo,)
        k = int(np.argmax(onset[j] / j))
        assert round(onset[j][k] / j[k], 4) == ratio and j[k] == at


def test_right_periods_against_spacetime() -> None:
    """The right diagonals cell(t, t - k) read from a spacetime run of the single cell, and their least periods."""
    steps, depth, window = 256, 12, 128
    cells = np.zeros(2 * steps + 1, dtype=np.uint8)  # (2 steps + 1,), cell x at index x + steps
    cells[steps] = 1
    diagram = spacetime(cells, steps).astype(np.uint8)  # (steps + 1, 2 steps + 1)
    expected = []
    for k in range(depth):
        # (window,): cell t - k sits at index t - k + steps
        diagonal = np.array([diagram[t, t - k + steps] for t in range(steps - window, steps)])
        p = next((p for p in (1, 2, 4, 8, 16, 32) if np.array_equal(diagonal[p:], diagonal[:-p])), None)
        expected.append(p)
    assert pj.right_periods(steps, depth, window) == expected
    assert expected[:6] == [1, 2, 2, 4, 8, 8]


def test_front() -> None:
    onset = np.array([0, 0, 5, 3, 9, 2, 12])  # (7,)
    times = np.array([0, 4, 5, 8, 9, 11, 12])  # (7,)
    brute = [min(j for j in range(len(onset)) if onset[j] > t) if onset.max() > t else len(onset) for t in times]
    assert pj.front(onset, times).tolist() == brute


def test_knn_two_sample() -> None:
    rng = np.random.default_rng(6)
    same = rng.standard_normal((600, 3))  # (600, 3)
    labels = np.repeat([0, 1], 300).astype(np.int8)  # (600,)
    _, z = pj.knn_two_sample(same, labels, 5, rng, 100)
    assert abs(z) < 4
    shifted = same + labels[:, None] * 1.5  # (600, 3)
    _, z = pj.knn_two_sample(shifted, labels, 5, rng, 100)
    assert z > 10


def test_covariance_distance_and_welch() -> None:
    """The second-moment distance is small for invariant patches and large for planted ones; Welch's score equals
    SciPy's unequal-variance t statistic. (The sklearn classifiers and autoencoder are exercised by the `learned`
    command, whose regular bins are their positive control; importing sklearn would take most of this file's budget.)"""
    from scipy.stats import ttest_ind

    rng = np.random.default_rng(7)
    cov = pj.exact_covariance(2, 4)  # (8, 8)
    near, eigenvalues = pj.covariance_distance(pj.null_patches(20_000, 2, 4, rng), cov)
    far, _ = pj.covariance_distance(pj.planted_patches(20_000, 2, 4, rng, 1.0, 0.8), cov)
    assert near < 0.1 < 0.5 < far
    assert np.isclose(eigenvalues.sum(), 8) and np.all(np.diff(eigenvalues) <= 1e-12)
    a, b = rng.standard_normal(300), 0.3 + 2 * rng.standard_normal(500)  # (300,), (500,)
    assert np.isclose(pj.mean_difference_z(a, b), ttest_ind(a, b, equal_var=False).statistic)


def test_column_matrices() -> None:
    """The Hankel Gram matrix from lag sums equals H H^T / K; the reshaped spectrum and the Marchenko-Pastur law."""
    rng = np.random.default_rng(8)
    x = 2.0 * rng.integers(0, 2, 500) - 1  # (500,)
    L = 20
    H = np.stack([x[i:i + 500 - L + 1] for i in range(L)])  # (L, K)
    assert np.allclose(pj.hankel_gram(x, L), H @ H.T / H.shape[1])
    X = x[:500].reshape(20, 25)  # (20, 25)
    assert np.allclose(pj.reshaped_spectrum(25)(x), np.linalg.eigvalsh(X @ X.T / 25))
    assert np.allclose(pj.reshaped_spectrum(10)(x), np.linalg.eigvalsh(x.reshape(50, 10).T @ x.reshape(50, 10) / 50))
    y = 0.25
    grid = np.linspace(0, 3, 3001)  # (3001,)
    cdf = pj.marchenko_pastur_cdf(y, grid)  # (3001,)
    assert cdf[0] == 0 and cdf[-1] == 1
    mean = np.sum(1 - cdf) * (grid[1] - grid[0])
    assert abs(mean - 1) < 0.01
    coins = 2.0 * rng.integers(0, 2, 200 * 800) - 1  # (160000,)
    assert pj.ks_to_cdf(pj.reshaped_spectrum(800)(coins), lambda v: pj.marchenko_pastur_cdf(y, v)) < 0.05
