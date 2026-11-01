"""Persistent homology of Rule 30 space-time windows: the single cell's center against random rows.

A window is a square of the space-time diagram, `size` steps by `size` cells. Its black cells (and, separately, its
white cells) form a point cloud in the plane, and `ripser` computes the Vietoris-Rips persistence of each cloud in
dimensions 0 and 1. Grid distances are 1, sqrt 2, 2, sqrt 5, ..., so the bars read off the shapes of the clusters:
the H0 bars that outlive 1 and sqrt 2 count the 4- and 8-connected clusters, the H1 bars born at 1 are the cycle rank
of the 4-neighbor graph, and the H1 bars that live past 2 are holes larger than one missing cell (for the black cells,
the white triangles). Each window gives a vector of such numbers.

Samples: windows of the single black cell's diagram centered on the center column, from step `start` on, one below
the other with no overlap; windows of uniform random rows run for `burn` steps (the uniform measure is invariant under
Rule 30, so these are windows of the stationary diagram); fair coin flips cell by cell, a positive control; and
windows of the single cell's diagram just inside the left and the right edge of its triangle.

    python -m computations.persistence --count 400 --size 32      # the tests and the controls, about 30 minutes
    python -m computations.persistence --count 400 --size 32 --start 20000 --rows-seed 7 --no-controls  # a replicate

Requires `ripser` (pip install ripser).
"""

from __future__ import annotations

import argparse
import math
import sys

import numpy as np
from scipy import ndimage, stats
from sklearn.linear_model import LogisticRegression
from sklearn.model_selection import StratifiedKFold, cross_val_predict
from sklearn.metrics import roc_auc_score
from sklearn.pipeline import make_pipeline
from sklearn.preprocessing import StandardScaler
from tqdm.auto import tqdm

CAP = 6.0  # the Rips filtration stops here; a bar alive at CAP counts as dying at CAP
FEATURES = [
    "clusters4", "clusters8", "cycles4", "holes", "hole_persistence", "largest_hole",
]


def seed_windows(count: int, size: int, start: int, edge: str = "") -> np.ndarray:
    """`count` windows of the single black cell's diagram, rows start + i * size .. start + (i + 1) * size - 1 of the
    i-th, on cells -size // 2 .. size // 2 - 1 (cell 0 the black cell), or, with `edge` "left", on the cells from
    -t0 + size // 2 on, where t0 is the window's first step and -t0 the left edge of the triangle then, or with
    `edge` "right" on the cells up to t0 - size // 2 - 1, t0 being the right edge then."""
    steps = start + count * size
    n = steps + size + 2  # bit n is cell 0
    row = 1 << n
    mask = (1 << size) - 1
    nbytes = (size + 7) // 8
    out = np.zeros((count, size, size), dtype=np.uint8)  # (count, size, size): window, step, cell
    for t in range(steps):
        if t >= start:
            i, j = divmod(t - start, size)
            t0 = start + i * size
            first = {"": -(size // 2), "left": -t0 + size // 2, "right": t0 - size - size // 2}[edge]
            low = n + first  # bit of the window's first cell
            chunk = np.frombuffer(((row >> low) & mask).to_bytes(nbytes, "little"), dtype=np.uint8)  # (nbytes,)
            out[i, j] = np.unpackbits(chunk, bitorder="little")[:size]
        row = (row << 1) ^ (row | (row >> 1))
    return out  # (count, size, size)


def random_windows(count: int, size: int, burn: int, seed: int) -> np.ndarray:
    """`count` windows of rows `burn` .. burn + size - 1 of Rule 30 from independent uniform random rows, each row wide
    enough that the window is exact."""
    rng = np.random.default_rng(seed)
    width = size + 2 * (burn + size)
    rows = rng.integers(0, 2, (count, width), dtype=np.uint8)  # (count, width)
    out = np.zeros((count, size, size), dtype=np.uint8)  # (count, size, size)
    lo = burn + size
    for t in range(burn + size):
        if t >= burn:
            out[:, t - burn] = rows[:, lo:lo + size]
        left = np.concatenate([np.zeros((count, 1), dtype=np.uint8), rows[:, :-1]], axis=1)  # (count, width)
        right = np.concatenate([rows[:, 1:], np.zeros((count, 1), dtype=np.uint8)], axis=1)  # (count, width)
        rows = left ^ (rows | right)
    return out  # (count, size, size)


def coin_windows(count: int, size: int, seed: int) -> np.ndarray:
    """`count` windows of fair coin flips, cell by cell."""
    return np.random.default_rng(seed).integers(0, 2, (count, size, size), dtype=np.uint8)  # (count, size, size)


def diagrams(window: np.ndarray, value: int) -> list[np.ndarray]:
    """The H0 and H1 diagrams of the cells of `window` equal to `value`, Rips filtration up to CAP, infinite deaths set
    to CAP."""
    from ripser import ripser

    points = np.argwhere(window == value).astype(np.float64)  # (p, 2)
    if points.shape[0] < 2:
        return [np.full((points.shape[0], 2), [0.0, CAP]), np.zeros((0, 2))]
    dgms = ripser(points, maxdim=1, thresh=CAP)["dgms"]
    return [np.where(np.isinf(d), CAP, d) for d in dgms]  # each (bars, 2)


def features(window: np.ndarray, value: int) -> np.ndarray:
    """The numbers of FEATURES for the cells of `window` equal to `value`."""
    h0, h1 = diagrams(window, value)
    eps = 1e-9
    clusters4 = np.sum(h0[:, 1] > 1 + eps)
    clusters8 = np.sum(h0[:, 1] > math.sqrt(2) + eps)
    cycles4 = np.sum(np.abs(h1[:, 0] - 1) < eps)
    big = h1[h1[:, 1] > 2 + eps]  # (holes, 2)
    holes = big.shape[0]
    persistence = float(np.sum(big[:, 1] - big[:, 0]))
    largest = float(big[:, 1].max()) if holes else 0.0
    return np.array([clusters4, clusters8, cycles4, holes, persistence, largest], dtype=np.float64)  # (6,)


def feature_matrix(windows: np.ndarray, progress: bool = False) -> np.ndarray:
    """Features of the black cells, then of the white cells, of each window."""
    rows = [np.concatenate([features(w, 1), features(w, 0)]) for w in tqdm(windows, disable=not progress,
                                                                           mininterval=5.0)]
    return np.stack(rows)  # (count, 2 * len(FEATURES))


def graph_counts(window: np.ndarray, value: int) -> tuple[int, int, int]:
    """The independent check: 4-connected and 8-connected clusters of the cells equal to `value` (scipy labels) and
    the cycle rank E - V + C of their 4-neighbor graph."""
    cells = window == value
    c4 = ndimage.label(cells)[1]
    c8 = ndimage.label(cells, structure=np.ones((3, 3)))[1]
    edges = int(np.sum(cells[1:] & cells[:-1]) + np.sum(cells[:, 1:] & cells[:, :-1]))
    return int(c4), int(c8), edges - int(cells.sum()) + int(c4)


def classifier_auc(x: np.ndarray, y: np.ndarray, permutations: int, seed: int = 0) -> tuple[float, float]:
    """Cross-validated AUC of a logistic regression telling the two samples apart, and its permutation p-value."""
    rng = np.random.default_rng(seed)
    model = make_pipeline(StandardScaler(), LogisticRegression(max_iter=2000))
    folds = StratifiedKFold(5, shuffle=True, random_state=seed)

    def auc(labels: np.ndarray) -> float:
        score = cross_val_predict(model, x, labels, cv=folds, method="predict_proba")[:, 1]  # (n,)
        return float(roc_auc_score(labels, score))

    base = auc(y)
    null = np.array([auc(rng.permutation(y)) for _ in range(permutations)])  # (permutations,)
    return base, float((1 + np.sum(null >= base)) / (permutations + 1))


def energy_test(a: np.ndarray, b: np.ndarray, permutations: int, seed: int = 0) -> tuple[float, float]:
    """The energy distance between two samples of standardized feature vectors, and its permutation p-value."""
    rng = np.random.default_rng(seed)
    z = np.concatenate([a, b])  # (n, f)
    z = (z - z.mean(0)) / np.where(z.std(0) > 0, z.std(0), 1.0)
    d = np.sqrt(((z[:, None, :] - z[None, :, :]) ** 2).sum(-1))  # (n, n)
    n = a.shape[0]

    def energy(idx: np.ndarray) -> float:
        i, j = idx[:n], idx[n:]
        return float(2 * d[np.ix_(i, j)].mean() - d[np.ix_(i, i)].mean() - d[np.ix_(j, j)].mean())

    order = np.arange(z.shape[0])
    base = energy(order)
    null = np.array([energy(rng.permutation(order)) for _ in range(permutations)])  # (permutations,)
    return base, float((1 + np.sum(null >= base)) / (permutations + 1))


def compare(a: np.ndarray, b: np.ndarray, label: str, permutations: int) -> None:
    """Print the per-feature Mann-Whitney tests (Bonferroni over the features), the energy test and the classifier."""
    names = [f"black {f}" for f in FEATURES] + [f"white {f}" for f in FEATURES]
    print(f"{label}: {a.shape[0]} against {b.shape[0]} windows")
    for k, name in enumerate(names):
        if np.all(a[:, k] == a[0, k]) and np.all(b[:, k] == a[0, k]):
            continue
        p = stats.mannwhitneyu(a[:, k], b[:, k]).pvalue
        print(f"  {name:24s} means {a[:, k].mean():8.3f} {b[:, k].mean():8.3f}   p x {len(names)} = "
              f"{min(1.0, p * len(names)):.3g}")
    e, pe = energy_test(a, b, permutations)
    x = np.concatenate([a, b])
    y = np.concatenate([np.zeros(a.shape[0], dtype=np.int64), np.ones(b.shape[0], dtype=np.int64)])  # (n,)
    auc, pa = classifier_auc(x, y, max(1, permutations // 2))
    print(f"  energy distance {e:.4f} ({permutations} permutations, p {pe:.3g}); classifier AUC {auc:.3f} "
          f"({max(1, permutations // 2)} permutations, p {pa:.3g})")
    sys.stdout.flush()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--count", type=int, default=400)
    parser.add_argument("--size", type=int, default=32)
    parser.add_argument("--start", type=int, default=1000)
    parser.add_argument("--burn", type=int, default=64)
    parser.add_argument("--rows-seed", type=int, default=1, help="seed of the random rows")
    parser.add_argument("--permutations", type=int, default=200)
    parser.add_argument("--no-controls", action="store_true", help="only the center against random rows")
    args = parser.parse_args()
    n, s = args.count, args.size
    center = feature_matrix(seed_windows(n, s, args.start), progress=True)
    rand = feature_matrix(random_windows(n, s, args.burn, seed=args.rows_seed), progress=True)
    compare(center, rand, f"single-cell center from step {args.start} against random rows (seed {args.rows_seed})",
            args.permutations)
    if args.no_controls:
        return
    rand2 = feature_matrix(random_windows(n, s, args.burn, seed=args.rows_seed + 1), progress=True)
    coin = feature_matrix(coin_windows(n, s, seed=args.rows_seed + 2), progress=True)
    left = feature_matrix(seed_windows(n, s, args.start, edge="left"), progress=True)
    right = feature_matrix(seed_windows(n, s, args.start, edge="right"), progress=True)
    compare(rand2, rand, "random rows against random rows (null control)", args.permutations)
    compare(coin, rand, "coin flips against random rows (positive control)", args.permutations)
    compare(left, rand, "single-cell left edge against random rows", args.permutations)
    compare(right, rand, "single-cell right edge against random rows", args.permutations)
    for eps in (0.002, 0.01):
        flips = np.random.default_rng(args.rows_seed + 3).random((n, s, s)) < eps  # (n, s, s)
        noisy = feature_matrix(random_windows(n, s, args.burn, seed=args.rows_seed + 1) ^ flips, progress=True)
        compare(noisy, rand, f"random rows with a fraction {eps} of cells flipped against random rows (power)",
                args.permutations)


if __name__ == "__main__":
    main()
