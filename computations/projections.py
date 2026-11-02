"""Linear and learned projections of Rule 30 space-time patches and of the center column, as tests against the
invariant measure.

Rule 30 is onto, so the uniform Bernoulli measure on rows is invariant. Under it, a space-time patch of h rows and w
cells (rows t .. t + h - 1, cells x .. x + w - 1) is the image of a uniform row of w + 2(h - 1) cells at time t: its law
can be enumerated exactly for small patches and sampled exactly for any patch. This module compares that law with

- patches of the single black cell's diagram, binned by x / t or by the distance t - x to the right edge, and
- patches of a control diagram run from a uniform random row with the same geometry, whose patches have exactly the
  invariant law and the same dependence between samples, so they calibrate every statistic,

by the exact Pearson chi-square of pattern counts, covariance (PCA) spectra, held-out classifier accuracy, autoencoder
reconstruction error and k-nearest-neighbor two-sample tests in the raw patch space and in a t-SNE embedding. It also
tests two matrix forms of the center column in plus/minus one encoding against independent fair coins: the delay
(Hankel) matrix of singular spectrum analysis, and the column cut into rows of r cells, whose Gram spectrum follows the
Marchenko-Pastur law for coins.

    python -m computations.projections profile    # exact chi-square profile across x / t, patches of 4 x 8
    python -m computations.projections edge       # the same near the right edge, patches of 3 x 4
    python -m computations.projections learned    # PCA, classifiers, autoencoder, kNN and t-SNE on patches of 8 x 16
    python -m computations.projections recheck    # gradient boosting refit on larger samples; stronger planted controls
    python -m computations.projections front      # where the left diagonals start to repeat, to depth 80,000
    python -m computations.projections column     # Hankel and reshaped spectra of the first 2^20 center cells
"""

from __future__ import annotations

import argparse
import sys
from collections.abc import Callable, Iterator
from dataclasses import dataclass

import numpy as np
from tqdm.auto import tqdm

from computations.rule30 import center_column, step


# ---------------------------------------------------------------------------------------------------------------------
# Patches under the invariant measure


def base_width(h: int, w: int) -> int:
    """Cells of row t that a patch of h rows and w cells depends on."""
    return w + 2 * (h - 1)


def cone_patches(base: np.ndarray, h: int, w: int) -> np.ndarray:
    """The patches above rows `base` of w + 2(h - 1) cells: row k of a patch is the middle w cells after k steps."""
    # base: (m, w + 2(h - 1))
    assert base.shape[1] == base_width(h, w)
    rows = base.astype(bool)  # (m, w + 2(h - 1) - 2k) after k steps
    out = np.empty((base.shape[0], h, w), dtype=bool)  # (m, h, w)
    for k in range(h):
        out[:, k] = rows[:, h - 1 - k:h - 1 - k + w]
        if k < h - 1:
            rows = rows[:, :-2] ^ (rows[:, 1:-1] | rows[:, 2:])
    return out.reshape(base.shape[0], h * w).astype(np.uint8)  # (m, h w), row-major: bit k w + j is row k, cell j


def codes_of(bits: np.ndarray) -> np.ndarray:
    """Each patch of at most 64 cells as an integer, bit i the i-th cell in row-major order."""
    # bits: (m, h w)
    assert bits.shape[1] <= 64
    weights = np.left_shift(np.uint64(1), np.arange(bits.shape[1], dtype=np.uint64))  # (h w,)
    return (bits.astype(np.uint64) * weights).sum(axis=1, dtype=np.uint64)  # (m,)


def bits_of(codes: np.ndarray, size: int) -> np.ndarray:
    """The inverse of `codes_of`."""
    # codes: (m,)
    shifts = np.arange(size, dtype=np.uint64)  # (size,)
    return ((codes[:, None] >> shifts[None, :]) & np.uint64(1)).astype(np.uint8)  # (m, size)


def exact_law(h: int, w: int) -> tuple[np.ndarray, np.ndarray]:
    """The patterns a patch of h x w takes under the invariant measure, sorted, with their probabilities."""
    width = base_width(h, w)
    assert width <= 24, "enumeration over 2^(w + 2h - 2) rows"
    index = np.arange(1 << width, dtype=np.uint32)  # (2^width,)
    base = ((index[:, None] >> np.arange(width, dtype=np.uint32)[None, :]) & 1).astype(np.uint8)  # (2^width, width)
    support, counts = np.unique(codes_of(cone_patches(base, h, w)), return_counts=True)  # each (K,)
    return support, counts / float(1 << width)  # (K,), (K,)


def exact_covariance(h: int, w: int) -> np.ndarray:
    """E[s s^T] for the patch in plus/minus one encoding (every cell has mean 0 under the invariant measure)."""
    support, probs = exact_law(h, w)  # (K,), (K,)
    signs = 2.0 * bits_of(support, h * w) - 1.0  # (K, h w)
    return (signs * probs[:, None]).T @ signs  # (h w, h w)


def null_patches(m: int, h: int, w: int, rng: np.random.Generator, density: float = 0.5) -> np.ndarray:
    """m patches above independent rows of Bernoulli(density) cells; density 1/2 is the invariant measure."""
    base = (rng.random((m, base_width(h, w))) < density).astype(np.uint8)  # (m, w + 2(h - 1))
    return cone_patches(base, h, w)  # (m, h w)


def planted_patches(m: int, h: int, w: int, rng: np.random.Generator, fraction: float, density: float) -> np.ndarray:
    """A positive control: invariant patches, with a random `fraction` of them taken over Bernoulli(density) rows."""
    out = null_patches(m, h, w, rng)  # (m, h w)
    swap = rng.random(m) < fraction  # (m,)
    out[swap] = null_patches(int(swap.sum()), h, w, rng, density)
    return out  # (m, h w)


# ---------------------------------------------------------------------------------------------------------------------
# Patches of a diagram


def seed_row(last: int, margin: int = 64) -> tuple[int, int]:
    """The single black cell as an integer row whose bit origin + x is cell x, with room for `last` steps."""
    origin = last + margin
    return 1 << origin, origin


def random_row(radius: int, last: int, rng: np.random.Generator, margin: int = 64) -> tuple[int, int]:
    """A uniform random row on cells -radius .. radius, white beyond; row t is exact on |x| <= radius - t."""
    bits = rng.integers(0, 2, 2 * radius + 1, dtype=np.uint8)  # (2 radius + 1,), bit k is cell k - radius
    value = int.from_bytes(np.packbits(bits, bitorder="little").tobytes(), "little")
    origin = radius + last + margin
    return value << (origin - radius), origin


def diagram_patches(row: int, origin: int, times: list[int], h: int, w: int,
                    positions: Callable[[int], np.ndarray], progress: bool = True
                    ) -> Iterator[tuple[int, np.ndarray, np.ndarray]]:
    """For each time t in `times` (increasing, at least h apart), the left ends x = positions(t) and the patches at
    (t, x) of the diagram that starts from `row` (bit origin + x is cell x)."""
    assert all(b - a >= h for a, b in zip(times, times[1:]))
    last = times[-1] + h - 1
    nbytes = (row.bit_length() + last + 16) // 8 + 1
    pending = iter(times)
    current = next(pending, None)
    buffer: list[np.ndarray] = []  # each (8 nbytes,)
    offsets = np.arange(w)  # (w,)
    for t in tqdm(range(last + 1), desc="evolve", unit="step", file=sys.stderr, mininterval=5, disable=not progress):
        if current is not None and current <= t:
            raw = np.frombuffer(row.to_bytes(nbytes, "little"), dtype=np.uint8)  # (nbytes,)
            buffer.append(np.unpackbits(raw, bitorder="little"))  # (8 nbytes,)
            if t == current + h - 1:
                x = positions(current)  # (n,)
                index = (x + origin)[:, None] + offsets[None, :]  # (n, w)
                patches = np.stack([cells[index] for cells in buffer], axis=1)  # (n, h, w)
                yield current, x, patches.reshape(len(x), h * w)
                buffer, current = [], next(pending, None)
        if current is None:
            return
        row = step(row)


def lattice(lo: int, hi: int, stride: int, rng: np.random.Generator) -> np.ndarray:
    """Left ends lo + offset, lo + offset + stride, ... <= hi, with a random offset below the stride."""
    return np.arange(lo + int(rng.integers(stride)), hi + 1, stride)  # (n,)


def make_diagram(kind: str, last: int, h: int, w: int, rng: np.random.Generator) -> tuple[int, int]:
    """The single cell (`seed`) or a uniform random row wide enough to be exact on |x| <= t + w at every time read."""
    if kind == "seed":
        return seed_row(last)
    return random_row(2 * last + w + h + 2, last, rng)


# ---------------------------------------------------------------------------------------------------------------------
# The exact chi-square test


@dataclass(frozen=True, slots=True)
class ChiSquare:
    """Pearson's statistic of n patches against the exact law with K patterns, standardized by its exact mean K - 1
    and variance under independent sampling; `divergence` estimates the chi-square divergence without bias."""

    n: int
    statistic: float
    z: float
    divergence: float
    divergence_sd: float


def chi_square(counts: np.ndarray, probs: np.ndarray) -> ChiSquare:
    """Counts of the K patterns (in the order of `probs`) against the exact law."""
    # counts: (K,), probs: (K,)
    n = int(counts.sum())
    k = len(probs)
    expected = n * probs  # (K,)
    statistic = float(((counts - expected) ** 2 / expected).sum())
    variance = 2.0 * (k - 1) + ((1.0 / probs).sum() - k * k - 2 * k + 2) / n
    return ChiSquare(n, statistic, (statistic - (k - 1)) / np.sqrt(variance), (statistic - (k - 1)) / n,
                     float(np.sqrt(variance)) / n)


def pattern_index(codes: np.ndarray, support: np.ndarray) -> np.ndarray:
    """The index of each code in the sorted support; every code must lie in it."""
    index = np.searchsorted(support, codes)  # (m,)
    assert np.all(index < len(support)) and np.all(support[np.minimum(index, len(support) - 1)] == codes), \
        "a patch outside the support of the invariant law"
    return index  # (m,)


def sample_times(t0: int, t1: int, spacing: int) -> list[int]:
    return list(range(t0, t1 + 1, spacing))


def position_counts(kind: str, h: int, w: int, t0: int, t1: int, spacing: int, edges: np.ndarray, coordinate: str,
                    rng: np.random.Generator, bands: int = 1) -> np.ndarray:
    """Pattern counts of patches with base windows that do not overlap within a row, per time band and per bin of
    `coordinate`: `ratio` bins x / t over the whole row, `edge` bins the distance d = t - x from the right edge."""
    support, probs = exact_law(h, w)  # (K,), (K,)
    times = sample_times(t0, t1, spacing)
    row, origin = make_diagram(kind, times[-1] + h, h, w, rng)
    stride = base_width(h, w)
    top = int(edges[-1])

    def positions(t: int) -> np.ndarray:
        if coordinate == "ratio":
            return lattice(-t, t - w + 1, stride, rng)
        return t - lattice(w - 1, min(top, 2 * t), stride, rng)[::-1]

    counts = np.zeros((bands, len(edges) - 1, len(probs)), dtype=np.int64)  # (bands, bins, K)
    band_edges = np.geomspace(t0, t1 + 1, bands + 1)  # (bands + 1,)
    for t, x, patches in diagram_patches(row, origin, times, h, w, positions):
        value = x / t if coordinate == "ratio" else (t - x).astype(float)  # (n,)
        b = np.searchsorted(edges, value, side="right") - 1  # (n,)
        keep = (b >= 0) & (b < len(edges) - 1)  # (n,)
        band = min(int(np.searchsorted(band_edges, t, side="right")) - 1, bands - 1)
        np.add.at(counts[band], (b[keep], pattern_index(codes_of(patches[keep]), support)), 1)
    return counts  # (bands, bins, K)


def profile_rows(counts: np.ndarray, probs: np.ndarray) -> list[ChiSquare | None]:
    """The chi-square of each bin, None for an empty bin."""
    # counts: (bins, K)
    return [chi_square(c, probs) if c.sum() > 0 else None for c in counts]


# ---------------------------------------------------------------------------------------------------------------------
# Learned and linear projections


def binned_samples(kind: str, h: int, w: int, t0: int, t1: int, spacing: int, bins: list[tuple[float, float]],
                   n_max: int, rng: np.random.Generator) -> list[np.ndarray]:
    """Up to n_max patches with non-overlapping base windows from each bin lo <= x / t < hi of a diagram."""
    times = sample_times(t0, t1, spacing)
    row, origin = make_diagram(kind, times[-1] + h, h, w, rng)
    stride = base_width(h, w)

    def positions(t: int) -> np.ndarray:
        x = lattice(-t, t - w + 1, stride, rng)  # (n,)
        u = x / t  # (n,)
        return x[np.any([(u >= lo) & (u < hi) for lo, hi in bins], axis=0)]

    found: list[list[np.ndarray]] = [[] for _ in bins]
    for t, x, patches in diagram_patches(row, origin, times, h, w, positions):
        u = x / t  # (n,)
        for i, (lo, hi) in enumerate(bins):
            found[i].append(patches[(u >= lo) & (u < hi)])
    out = []
    for parts in found:
        sample = np.concatenate(parts)  # (n, h w)
        out.append(sample[rng.permutation(len(sample))[:n_max]])
    return out


def signs(bits: np.ndarray) -> np.ndarray:
    return 2.0 * bits - 1.0  # (m, d)


def covariance_distance(bits: np.ndarray, reference: np.ndarray) -> tuple[float, np.ndarray]:
    """Frobenius distance of the second-moment matrix of a sample from `reference`, and its eigenvalues (descending)."""
    s = signs(bits)  # (m, d)
    second = s.T @ s / len(s)  # (d, d)
    return float(np.linalg.norm(second - reference)), np.linalg.eigvalsh(second)[::-1]


def classifier_accuracy(a: np.ndarray, b: np.ndarray, rng: np.random.Generator, model: str = "gb",
                        test_fraction: float = 0.25) -> tuple[float, float]:
    """Held-out accuracy of a classifier trained to tell sample a from sample b (equal sizes), and its standard error
    under chance."""
    m = min(len(a), len(b))
    X = signs(np.concatenate([a[:m], b[:m]]))  # (2m, d)
    y = np.concatenate([np.zeros(m), np.ones(m)])  # (2m,)
    order = rng.permutation(2 * m)  # (2m,)
    cut = int(2 * m * (1 - test_fraction))
    train, test = order[:cut], order[cut:]
    seed = int(rng.integers(1 << 31))
    if model == "gb":
        from sklearn.ensemble import HistGradientBoostingClassifier

        clf = HistGradientBoostingClassifier(max_iter=300, early_stopping=True, validation_fraction=0.15,
                                             random_state=seed)
    else:
        from sklearn.neural_network import MLPClassifier

        clf = MLPClassifier(hidden_layer_sizes=(128, 64), early_stopping=True, max_iter=200, random_state=seed)
    clf.fit(X[train], y[train])
    accuracy = float((clf.predict(X[test]) == y[test]).mean())
    return accuracy, float(np.sqrt(0.25 / len(test)))


def train_autoencoder(null: np.ndarray, bottleneck: int, rng: np.random.Generator, hidden: int = 64,
                      max_iter: int = 60):
    """An MLP autoencoder d -> hidden -> bottleneck -> hidden -> d trained on invariant patches."""
    from sklearn.neural_network import MLPRegressor

    X = signs(null)  # (m, d)
    model = MLPRegressor(hidden_layer_sizes=(hidden, bottleneck, hidden), activation="tanh", max_iter=max_iter,
                         early_stopping=True, random_state=int(rng.integers(1 << 31)))
    model.fit(X, X)
    return model


def reconstruction_errors(model, bits: np.ndarray) -> np.ndarray:
    """Mean squared reconstruction error of each patch."""
    X = signs(bits)  # (m, d)
    return ((model.predict(X) - X) ** 2).mean(axis=1)  # (m,)


def mean_difference_z(a: np.ndarray, b: np.ndarray) -> float:
    """Welch's standardized difference of two means."""
    return float((a.mean() - b.mean()) / np.sqrt(a.var(ddof=1) / len(a) + b.var(ddof=1) / len(b)))


def knn_two_sample(points: np.ndarray, labels: np.ndarray, k: int, rng: np.random.Generator,
                   permutations: int = 200) -> tuple[float, float]:
    """Schilling's test: the fraction of k nearest neighbors (self excluded) that share a point's label, and its
    standard score against random relabelings of the same neighbor graph."""
    from scipy.spatial import cKDTree

    # points: (m, d), labels: (m,)
    neighbors = cKDTree(points).query(points, k=k + 1)[1][:, 1:]  # (m, k); the jitter makes self the nearest point
    statistic = float((labels[neighbors] == labels[:, None]).mean())  # neighbors: (m, k)
    null = np.empty(permutations)  # (permutations,)
    for i in range(permutations):
        p = rng.permutation(labels)  # (m,)
        null[i] = (p[neighbors] == p[:, None]).mean()
    return statistic, float((statistic - null.mean()) / null.std(ddof=1))


def jitter(bits: np.ndarray, rng: np.random.Generator, scale: float = 1e-3) -> np.ndarray:
    """Plus/minus one patches with a small Gaussian jitter that breaks the ties between equal patches at random."""
    return signs(bits) + scale * rng.standard_normal(bits.shape)  # (m, d)


def tsne_knn(a: np.ndarray, b: np.ndarray, k: int, rng: np.random.Generator) -> tuple[float, float]:
    """The kNN two-sample test in a two-dimensional t-SNE embedding of the pooled samples."""
    from sklearn.manifold import TSNE

    pooled = jitter(np.concatenate([a, b]), rng)  # (m_a + m_b, d)
    labels = np.concatenate([np.zeros(len(a), dtype=np.int8), np.ones(len(b), dtype=np.int8)])  # (m_a + m_b,)
    embedding = TSNE(n_components=2, perplexity=30, init="pca",
                     random_state=int(rng.integers(1 << 31))).fit_transform(pooled)  # (m_a + m_b, 2)
    return knn_two_sample(embedding, labels, k, rng)


# ---------------------------------------------------------------------------------------------------------------------
# The front of the regular left side


def onsets(steps: int, depth: int, period: int = 16, progress: bool = True) -> np.ndarray:
    """For each left diagonal D_j(t) = cell(t, j - t), j < depth, of the single cell, the least s such that
    D_j(t + period) = D_j(t) for s <= t <= steps - period (0 if it holds throughout); `steps` if it never holds."""
    row, origin = seed_row(steps)
    mask = (1 << depth) - 1
    nbytes = (depth + 7) // 8
    ring = np.zeros((period, depth), dtype=np.uint8)  # (period, depth): D(t - period) .. D(t - 1)
    last = np.full(depth, -1, dtype=np.int64)  # (depth,): the last t with D_j(t) != D_j(t - period)
    for t in tqdm(range(steps + 1), desc="onsets", unit="step", file=sys.stderr, mininterval=5, disable=not progress):
        raw = ((row >> (origin - t)) & mask).to_bytes(nbytes, "little")
        diagonal = np.unpackbits(np.frombuffer(raw, dtype=np.uint8), bitorder="little")[:depth]  # (depth,)
        if t >= period:
            last[diagonal != ring[t % period]] = t
        ring[t % period] = diagonal
        row = step(row)
    return np.maximum(last - period + 1, 0)  # (depth,)


def right_periods(steps: int, depth: int, window: int) -> list[int | None]:
    """The least power-of-two period of each right diagonal R_k(t) = cell(t, t - k), k < depth, of the single cell
    over the last `window` of times 0 .. steps - 1 (None if no power of two up to window / 4 repeats there)."""
    row, origin = seed_row(steps)
    R = np.zeros((depth, window), dtype=np.uint8)  # (depth, window)
    k = np.arange(depth)  # (depth,)
    for t in range(steps):
        if t >= steps - window:
            R[:, t - (steps - window)] = [(row >> (origin + t - int(i))) & 1 for i in k]
        row = step(row)
    out: list[int | None] = []
    for diagonal in R:  # (window,)
        p = 1
        while p <= window // 4 and not np.array_equal(diagonal[p:], diagonal[:-p]):
            p *= 2
        out.append(p if p <= window // 4 else None)
    return out


def front(onset: np.ndarray, times: np.ndarray) -> np.ndarray:
    """The first diagonal not yet repeating at each time: min {j : onset(j) > t}."""
    # onset: (depth,), times: (m,)
    record = np.maximum.accumulate(onset)  # (depth,): max of onset over j' <= j
    return np.searchsorted(record, times, side="right")  # (m,): first j with record(j) > t


# ---------------------------------------------------------------------------------------------------------------------
# Matrix forms of the center column


def hankel_gram(x: np.ndarray, L: int) -> np.ndarray:
    """(1 / K) H H^T for the L x K delay matrix H[i, k] = x[i + k], K = len(x) - L + 1, from cumulative sums of the
    lagged products."""
    # x: (N,)
    n = len(x)
    K = n - L + 1
    gram = np.empty((L, L))  # (L, L)
    for lag in range(L):
        prefix = np.concatenate([[0.0], np.cumsum(x[:n - lag] * x[lag:])])  # (N - lag + 1,)
        i = np.arange(L - lag)  # (L - lag,)
        values = (prefix[i + K] - prefix[i]) / K  # (L - lag,)
        gram[i, i + lag] = values
        gram[i + lag, i] = values
    return gram


def marchenko_pastur_cdf(y: float, grid: np.ndarray) -> np.ndarray:
    """The Marchenko-Pastur distribution function with ratio y <= 1 and unit variance, at `grid`."""
    lo, hi = (1 - np.sqrt(y)) ** 2, (1 + np.sqrt(y)) ** 2
    theta = np.linspace(0, np.pi / 2, 20001)  # (20001,): x = lo + (hi - lo) sin^2 theta removes the edge singularities
    sin2, cos2 = np.sin(theta) ** 2, np.cos(theta) ** 2  # each (20001,)
    fine = lo + (hi - lo) * sin2  # (20001,)
    # (20001,): sin^2 theta / x, with its limit at x = 0 when y = 1
    ratio = np.where(fine > 0, sin2 / np.maximum(fine, 1e-300), 1 / (hi - lo))
    integrand = (hi - lo) ** 2 * ratio * cos2 / (np.pi * y)  # (20001,): density times dx / dtheta
    cdf = np.concatenate([[0.0], np.cumsum((integrand[1:] + integrand[:-1]) / 2 * np.diff(theta))])  # (20001,)
    return np.interp(grid, fine, cdf / cdf[-1], left=0.0, right=1.0)


def ks_to_cdf(values: np.ndarray, cdf: Callable[[np.ndarray], np.ndarray]) -> float:
    """Kolmogorov-Smirnov distance of the empirical distribution of `values` from a distribution function."""
    v = np.sort(values)  # (m,)
    f = cdf(v)  # (m,)
    m = len(v)
    return float(max(np.max(np.arange(1, m + 1) / m - f), np.max(f - np.arange(m) / m)))


@dataclass(frozen=True, slots=True)
class SpectrumTest:
    """Three statistics of a spectrum, each with the fraction of coin replicas at least as extreme (two-sided)."""

    name: str
    largest: float
    smallest: float
    ks: float
    p_largest: float
    p_smallest: float
    p_ks: float
    null_largest: tuple[float, float]  # mean and standard deviation over the replicas
    null_smallest: tuple[float, float]
    null_ks: tuple[float, float]


def two_sided(value: float, null: np.ndarray) -> float:
    """Two-sided Monte Carlo p-value by rank."""
    lo = (np.sum(null <= value) + 1) / (len(null) + 1)
    hi = (np.sum(null >= value) + 1) / (len(null) + 1)
    return float(min(1.0, 2 * min(lo, hi)))


def spectrum_test(name: str, spectrum: Callable[[np.ndarray], np.ndarray], column: np.ndarray, ks_reference:
                  Callable[[np.ndarray], np.ndarray], replicas: int, rng: np.random.Generator) -> SpectrumTest:
    """The largest and smallest eigenvalue and the KS distance to `ks_reference` for the column, against `replicas`
    sequences of independent fair coins of the same length."""
    def stats(x: np.ndarray) -> tuple[float, float, float]:
        e = spectrum(x)  # (L,)
        return float(e.max()), float(e.min()), ks_to_cdf(e, ks_reference)

    observed = stats(column)
    null = np.array([stats(2.0 * rng.integers(0, 2, len(column)) - 1.0)
                     for _ in tqdm(range(replicas), desc=name, file=sys.stderr, mininterval=5)])  # (replicas, 3)
    p = [two_sided(observed[i], null[:, i]) for i in range(3)]
    ms = [(float(null[:, i].mean()), float(null[:, i].std(ddof=1))) for i in range(3)]
    return SpectrumTest(name, *observed, *p, *ms)


def hankel_spectrum(L: int) -> Callable[[np.ndarray], np.ndarray]:
    return lambda x: np.linalg.eigvalsh(hankel_gram(x, L))


def reshaped_spectrum(r: int) -> Callable[[np.ndarray], np.ndarray]:
    """Eigenvalues of the Gram matrix of the column cut into rows of r cells, scaled to the Marchenko-Pastur law:
    m = N // r rows; with m <= r, (1 / r) X X^T; otherwise (1 / m) X^T X."""
    def spectrum(x: np.ndarray) -> np.ndarray:
        m = len(x) // r
        X = x[:m * r].reshape(m, r)  # (m, r)
        gram = X @ X.T / r if m <= r else X.T @ X / m  # (min, min)
        return np.linalg.eigvalsh(gram)
    return spectrum


def column_tests(n: int, hankel_lengths: list[int], widths: list[int], replicas: int,
                 rng: np.random.Generator) -> list[SpectrumTest]:
    """Hankel and reshaped spectra of the first n center cells against coins. The Hankel spectra are compared with
    the pooled spectrum of the coin replicas (the delay matrix is not a matrix of independent entries, so the
    Marchenko-Pastur law is not its null); the reshaped spectra with the Marchenko-Pastur law."""
    column = 2.0 * center_column(n) - 1.0  # (n,)
    out = []
    for L in hankel_lengths:
        pool = np.sort(np.concatenate([hankel_spectrum(L)(2.0 * rng.integers(0, 2, n) - 1.0) for _ in range(20)]))
        reference = lambda v, pool=pool: np.searchsorted(pool, v, side="right") / len(pool)  # noqa: E731
        out.append(spectrum_test(f"hankel L={L}", hankel_spectrum(L), column, reference, replicas, rng))
    for r in widths:
        m = n // r
        y = min(m, r) / max(m, r)
        out.append(spectrum_test(f"reshape r={r}", reshaped_spectrum(r), column,
                                 lambda v, y=y: marchenko_pastur_cdf(y, v), replicas, rng))
    return out


# ---------------------------------------------------------------------------------------------------------------------
# Command line


def print_profile(label: str, edges: np.ndarray, rows: list[ChiSquare | None]) -> None:
    print(f"\n{label}")
    print(f"{'bin':>18} {'n':>9} {'z':>9} {'divergence':>11} {'sd':>9}")
    for lo, hi, r in zip(edges[:-1], edges[1:], rows):
        if r is not None:
            print(f"[{lo:7.3f},{hi:7.3f}) {r.n:9d} {r.z:9.2f} {r.divergence:11.5f} {r.divergence_sd:9.5f}")


def run_profile(args: argparse.Namespace) -> None:
    rng = np.random.default_rng(args.seed)
    h, w = args.height, args.width
    support, probs = exact_law(h, w)
    print(f"patch {h} x {w}: {len(support)} patterns under the invariant measure, "
          f"base row of {base_width(h, w)} cells; "
          f"times {args.t0} .. {args.t1} every {args.spacing}")
    edges = np.round(np.linspace(-1, 1, int(round(2 / args.bin)) + 1), 6)  # (bins + 1,)
    for kind in ("seed", "random"):
        counts = position_counts(kind, h, w, args.t0, args.t1, args.spacing, edges, "ratio", rng, args.bands)
        total = counts.sum(axis=0)  # (bins, K)
        coarse = total.reshape(-1, args.coarse, total.shape[1]).sum(axis=1)  # (bins / coarse, K)
        print_profile(f"{kind}: x / t, all times", edges[::args.coarse], profile_rows(coarse, probs))
        lo, hi = np.searchsorted(edges, args.pool[0] - 1e-9), np.searchsorted(edges, args.pool[1] - 1e-9)
        pooled = chi_square(total[lo:hi].sum(axis=0), probs)
        print(f"{kind}: pooled over {args.pool[0]} <= x / t < {args.pool[1]}: n {pooled.n}, z {pooled.z:.2f}, "
              f"divergence {pooled.divergence:.6f} +- {pooled.divergence_sd:.6f}")
        if kind == "seed":
            lo = np.searchsorted(edges, -0.5 - 1e-9)
            hi = np.searchsorted(edges, 0.0 + 1e-9)
            for band in range(args.bands):
                print_profile(f"seed: x / t near the boundary, time band {band + 1} of {args.bands}",
                              edges[lo:hi + 1], profile_rows(counts[band, lo:hi], probs))


def run_edge(args: argparse.Namespace) -> None:
    rng = np.random.default_rng(args.seed)
    h, w = args.height, args.width
    support, probs = exact_law(h, w)
    print(f"patch {h} x {w}: {len(support)} patterns; distance d = t - x of the left end from the right edge; "
          f"times {args.t0} .. {args.t1} every {args.spacing}")
    edges = np.concatenate([np.arange(w - 1, 41), [48, 64, 128, 256, 512, 1024, 2048, 4096]]).astype(float)
    for kind in ("seed", "random"):
        counts = position_counts(kind, h, w, args.t0, args.t1, args.spacing, edges, "edge", rng)[0]  # (bins, K)
        print_profile(f"{kind}: distance from the right edge", edges, profile_rows(counts, probs))
    periods = right_periods(1 << 16, 48, 1 << 15)
    print("\nleast periods of the right diagonals R_k over times 32,768 .. 65,535 (None: above 8,192):")
    print(", ".join(f"{k}: {p}" for k, p in enumerate(periods)))


def run_learned(args: argparse.Namespace) -> None:
    rng = np.random.default_rng(args.seed)
    h, w, n = args.height, args.width, args.samples
    bins = [(-0.85, -0.75), (-0.40, -0.35), (-0.35, -0.30), (-0.30, -0.25), (-0.20, -0.10), (-0.05, 0.05),
            (0.40, 0.50), (0.90, 0.95)]
    seed_sets = binned_samples("seed", h, w, args.t0, args.t1, args.spacing, bins, n, rng)
    control = binned_samples("random", h, w, args.t0, args.t1, args.spacing, [(-0.05, 0.05)], n, rng)[0]
    planted = planted_patches(n, h, w, rng, args.planted_fraction, args.planted_density)
    sets = [(f"seed [{lo:+.2f},{hi:+.2f})", s) for (lo, hi), s in zip(bins, seed_sets)]
    sets += [("random-row control", control),
             (f"planted {args.planted_fraction} at density {args.planted_density}", planted)]
    reference = null_patches(400_000, h, w, rng)  # (400000, h w)
    second = signs(reference).T @ signs(reference) / len(reference)  # (h w, h w)
    eig = np.linalg.eigvalsh(second)[::-1]
    print(f"patch {h} x {w}; times {args.t0} .. {args.t1} every {args.spacing}; up to {n} patches per set")
    print(f"invariant second-moment eigenvalues (400,000 samples): top {np.round(eig[:6], 3).tolist()}, "
          f"bottom {np.round(eig[-3:], 3).tolist()}")
    autoencoder = train_autoencoder(null_patches(args.ae_train, h, w, rng), args.bottleneck, rng)
    held_out = reconstruction_errors(autoencoder, null_patches(n, h, w, rng))  # (n,)
    print(f"autoencoder {h * w}-64-{args.bottleneck}-64-{h * w}: held-out invariant error {held_out.mean():.4f}")
    null_distances = [covariance_distance(null_patches(n, h, w, rng), second)[0] for _ in range(8)]
    md, sd = float(np.mean(null_distances)), float(np.std(null_distances, ddof=1))
    print(f"covariance distance of {n} invariant patches from the reference: {md:.4f} +- {sd:.4f}")
    header = (f"{'set':>34} {'n':>6} {'cov dist':>9} {'top eig':>8} {'GB acc':>7} {'MLP acc':>8} {'AE err':>7} "
              f"{'AE z':>7} {'kNN':>6} {'kNN z':>7} {'tSNE':>6} {'tSNE z':>7}")
    print(header)
    for name, sample in tqdm(sets, desc="sets", file=sys.stderr):
        m = len(sample)
        distance, eigenvalues = covariance_distance(sample, second)
        null = null_patches(m, h, w, rng)  # (m, h w)
        gb, se = classifier_accuracy(sample, null, rng, "gb")
        mlp, _ = classifier_accuracy(sample, null_patches(m, h, w, rng), rng, "mlp")
        errors = reconstruction_errors(autoencoder, sample)  # (m,)
        k = min(args.knn_points, m)
        pooled = jitter(np.concatenate([sample[:k], null[:k]]), rng)  # (2k, h w)
        labels = np.concatenate([np.zeros(k, dtype=np.int8), np.ones(k, dtype=np.int8)])  # (2k,)
        knn, knn_z = knn_two_sample(pooled, labels, 10, rng)
        ts, ts_z = tsne_knn(sample[:args.tsne_points], null[:args.tsne_points], 10, rng)
        print(f"{name:>34} {m:6d} {distance:9.4f} {eigenvalues[0]:8.3f} {gb:7.4f} {mlp:8.4f} {errors.mean():7.4f} "
              f"{mean_difference_z(errors, held_out):7.2f} {knn:6.3f} {knn_z:7.2f} {ts:6.3f} {ts_z:7.2f}")
    print(f"classifier standard error under chance: {se:.4f}")


def run_recheck(args: argparse.Namespace) -> None:
    """Gradient boosting refit three times on larger samples of two chaotic bins and the control, and the planted
    contamination at larger fractions, to scale the sensitivity of the projections."""
    rng = np.random.default_rng(args.seed)
    h, w, n = args.height, args.width, args.samples
    bins = [(-0.20, -0.10), (-0.05, 0.05)]
    seed_sets = binned_samples("seed", h, w, args.t0, args.t1, args.spacing, bins, n, rng)
    control = binned_samples("random", h, w, args.t0, args.t1, args.spacing, bins, n, rng)
    for name, sets in (("seed", seed_sets), ("random-row control", control)):
        for (lo, hi), sample in zip(bins, sets):
            accuracies = [classifier_accuracy(sample, null_patches(len(sample), h, w, rng), rng, "gb", 0.5)
                          for _ in range(3)]
            print(f"{name} [{lo:+.2f},{hi:+.2f}): {len(sample)} patches, half held out, gradient boosting "
                  f"{', '.join(f'{a[0]:.4f}' for a in accuracies)} (standard error {accuracies[0][1]:.4f})", flush=True)
    reference = signs(null_patches(400_000, h, w, rng))  # (400000, h w)
    second = reference.T @ reference / len(reference)  # (h w, h w)
    m, k = 20_000, 5_000
    for fraction in args.fractions:
        planted = planted_patches(m, h, w, rng, fraction, args.planted_density)  # (m, h w)
        distance, _ = covariance_distance(planted, second)
        accuracy, se = classifier_accuracy(planted, null_patches(m, h, w, rng), rng, "gb")
        pooled = jitter(np.concatenate([planted[:k], null_patches(k, h, w, rng)]), rng)  # (2k, h w)
        labels = np.repeat(np.arange(2, dtype=np.int8), k)  # (2k,)
        knn, z = knn_two_sample(pooled, labels, 10, rng)
        print(f"planted {fraction} at density {args.planted_density}: covariance distance {distance:.4f}, gradient "
              f"boosting {accuracy:.4f} (standard error {se:.4f}), kNN {knn:.3f} (z {z:.2f})", flush=True)


def run_front(args: argparse.Namespace) -> None:
    onset = onsets(args.steps, args.depth)  # (depth,)
    unconfirmed = np.nonzero(onset > args.steps - args.margin)[0]  # (m,)
    top = int(unconfirmed[0]) if len(unconfirmed) else args.depth  # every diagonal below `top` is confirmed
    j = np.arange(8, min(top, args.depth))  # (m,)
    ratio = onset[j] / j  # (m,)
    print(f"diagonals 8 .. {j[-1]} confirmed (onset at most {args.steps - args.margin} of {args.steps} steps); "
          "period 16")
    late = j[onset[j] > np.ceil(3 * j / 2)]
    first = f", first {late[:10].tolist()}" if len(late) else ""
    print(f"diagonals with onset above ceil(3j/2): {len(late)}{first}")
    print(f"{'depths':>16} {'largest onset/j':>16} {'at':>7} {'median onset/j':>15}")
    lo = 8
    while lo < j[-1]:
        hi = min(2 * lo if lo >= 64 else 64, j[-1] + 1)
        sel = (j >= lo) & (j < hi)
        k = int(np.argmax(ratio[sel]))
        print(f"{lo:>7} .. {hi - 1:>6} {ratio[sel][k]:16.4f} {int(j[sel][k]):7d} {np.median(ratio[sel]):15.4f}")
        lo = hi
    times = np.array([1 << k for k in range(10, 18) if (1 << k) <= args.steps])  # (m,)
    f = front(onset, times)
    for t, fj in zip(times, f):
        if fj < top:
            print(f"t = {t:7d}: first diagonal not yet repeating j = {fj:6d}, x / t = {fj / t - 1:+.4f}")


def run_column(args: argparse.Namespace) -> None:
    rng = np.random.default_rng(args.seed)
    print(f"first {args.cells} center cells, {args.replicas} coin replicas per test")
    for L in args.hankel:
        coins = hankel_spectrum(L)(2.0 * rng.integers(0, 2, args.cells) - 1.0)  # (L,)
        y = L / (args.cells - L + 1)
        print(f"coins, hankel L={L}: spectrum {coins.min():.5f} .. {coins.max():.5f}, Marchenko-Pastur support "
              f"{(1 - np.sqrt(y)) ** 2:.5f} .. {(1 + np.sqrt(y)) ** 2:.5f}, KS to it "
              f"{ks_to_cdf(coins, lambda v: marchenko_pastur_cdf(y, v)):.4f}")
    for r in column_tests(args.cells, args.hankel, args.widths, args.replicas, rng):
        print(f"{r.name:>16}: largest {r.largest:.5f} (coins {r.null_largest[0]:.5f} +- {r.null_largest[1]:.5f}, "
              f"p {r.p_largest:.3f}); smallest {r.smallest:.5f} (coins {r.null_smallest[0]:.5f} +- "
              f"{r.null_smallest[1]:.5f}, p {r.p_smallest:.3f}); KS {r.ks:.5f} (coins {r.null_ks[0]:.5f} +- "
              f"{r.null_ks[1]:.5f}, p {r.p_ks:.3f})")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    profile = sub.add_parser("profile")
    profile.add_argument("--height", type=int, default=4)
    profile.add_argument("--width", type=int, default=8)
    profile.add_argument("--t0", type=int, default=1 << 14)
    profile.add_argument("--t1", type=int, default=1 << 17)
    profile.add_argument("--spacing", type=int, default=256)
    profile.add_argument("--bin", type=float, default=0.01)
    profile.add_argument("--coarse", type=int, default=5)
    profile.add_argument("--bands", type=int, default=3)
    profile.add_argument("--pool", type=float, nargs=2, default=[-0.2, 0.9])
    edge = sub.add_parser("edge")
    edge.add_argument("--height", type=int, default=3)
    edge.add_argument("--width", type=int, default=4)
    edge.add_argument("--t0", type=int, default=1 << 14)
    edge.add_argument("--t1", type=int, default=1 << 17)
    edge.add_argument("--spacing", type=int, default=16)
    learned = sub.add_parser("learned")
    learned.add_argument("--height", type=int, default=8)
    learned.add_argument("--width", type=int, default=16)
    learned.add_argument("--t0", type=int, default=1 << 14)
    learned.add_argument("--t1", type=int, default=1 << 17)
    learned.add_argument("--spacing", type=int, default=256)
    learned.add_argument("--samples", type=int, default=20_000)
    learned.add_argument("--ae-train", type=int, default=50_000)
    learned.add_argument("--bottleneck", type=int, default=16)
    learned.add_argument("--knn-points", type=int, default=5_000)
    learned.add_argument("--tsne-points", type=int, default=1_000)
    learned.add_argument("--planted-fraction", type=float, default=0.1)
    learned.add_argument("--planted-density", type=float, default=0.6)
    recheck = sub.add_parser("recheck")
    recheck.add_argument("--height", type=int, default=8)
    recheck.add_argument("--width", type=int, default=16)
    recheck.add_argument("--t0", type=int, default=1 << 14)
    recheck.add_argument("--t1", type=int, default=1 << 17)
    recheck.add_argument("--spacing", type=int, default=256)
    recheck.add_argument("--samples", type=int, default=40_000)
    recheck.add_argument("--fractions", type=float, nargs="*", default=[0.25, 0.5])
    recheck.add_argument("--planted-density", type=float, default=0.6)
    front_parser = sub.add_parser("front")
    front_parser.add_argument("--steps", type=int, default=1 << 17)
    front_parser.add_argument("--depth", type=int, default=80_000)
    front_parser.add_argument("--margin", type=int, default=4_096)
    column = sub.add_parser("column")
    column.add_argument("--cells", type=int, default=1 << 20)
    column.add_argument("--hankel", type=int, nargs="*", default=[64, 256])
    column.add_argument("--widths", type=int, nargs="*", default=[1024, 2048, 2047, 4096])
    column.add_argument("--replicas", type=int, default=100)
    for p in (profile, edge, learned, recheck, front_parser, column):
        p.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    {"profile": run_profile, "edge": run_edge, "learned": run_learned, "recheck": run_recheck, "front": run_front,
     "column": run_column}[args.command](args)


if __name__ == "__main__":
    main()
