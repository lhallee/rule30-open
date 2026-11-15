"""Locally consistent pseudo-measures for Rule 30 and the linear programs they solve.

A pseudo-measure of range k on the left-edge frame is a family mu_0, ..., mu_{J-1} of probability vectors, mu_d on
the 2^(k+2) words of the row R on positions d-2, ..., d+k-1, with
  (boundary)    positions < 0 are white and position 0 is black,
  (shift)       mu_d and mu_{d+1} have the same marginal on positions d-1, ..., d+k-1,
  (stationary)  under mu_d, the image word R'[d..d+k-1] has the same law as R[d..d+k-1],
where R'_j = R_{j-2} XOR (R_{j-1} OR R_j). The empirical measure of every periodic orbit is one. The minimum of
sum_d mu_d[R_d = color] over pseudo-measures equals, by linear programming duality, the best lower bound on the
time-averaged number of cells of that color on diagonals 0..J-1 that a telescoping certificate (a spatial potential
on k+1 adjacent cells that may depend on d, plus a temporal potential on k adjacent cells) can prove.

    python computations/edge_pseudo_measures.py           # the ordinary and left-edge bounds for k = 1 .. 4
    python computations/edge_pseudo_measures.py --table   # and the table of the entry, up to about a minute a row
"""

from __future__ import annotations

import sys
import numpy as np

from fractions import Fraction
from itertools import product
from scipy.optimize import linprog
from scipy.sparse import lil_matrix


def words(n: int) -> np.ndarray:
    """All 0/1 words of length n; shape (2^n, n), word index = sum bits[i] << (n-1-i)."""
    return np.array(list(product((0, 1), repeat=n)), dtype=np.int64)  # shape (2^n, n)


def image(word: np.ndarray) -> np.ndarray:
    """Rule 30 image R'[2..] of rows R given on a window; word shape (m, n) -> (m, n-2)."""
    # word: (m, n)
    a, b, c = word[:, :-2], word[:, 1:-1], word[:, 2:]  # (m, n-2) each
    return a ^ (b | c)  # shape (m, n-2)


def index(bits: np.ndarray) -> np.ndarray:
    """Integer index of each row of a 0/1 array; shape (m, n) -> (m,)."""
    # bits: (m, n)
    n = bits.shape[1]
    return (bits * (1 << np.arange(n - 1, -1, -1))).sum(axis=1)  # shape (m,)


def left_edge_bound(J: int, k: int, color: int, stationary: bool = True) -> float:
    """Minimum over range-k pseudo-measures on diagonals 0..J-1 of the expected number of cells of `color`."""
    return left_edge_profile(J, k, color, stationary).sum()


def left_edge_profile(J: int, k: int, color: int, stationary: bool = True) -> np.ndarray:
    """mu_d[R_d = color] for an optimal range-k pseudo-measure on diagonals 0..J-1; shape (J,)."""
    W = words(k + 2)  # shape (2^(k+2), k+2)
    x = left_edge_solution(J, k, color, stationary)  # shape (J, 2^(k+2))
    return (x * (W[:, 2] == color)).sum(axis=1)  # shape (J,)


def left_edge_solution(J: int, k: int, color: int, stationary: bool = True, white_end: bool = False) -> np.ndarray:
    """An optimal range-k pseudo-measure on diagonals 0..J-1 as an array; shape (J, 2^(k+2))."""
    W = words(k + 2)  # shape (2^(k+2), k+2); column j is position d-2+j
    nw = W.shape[0]
    nvar = J * nw
    rows: list[dict[int, float]] = []
    rhs: list[float] = []
    lo = [0.0] * nvar
    hi = [1.0] * nvar
    for d in range(J):
        pos = np.arange(d - 2, d + k)  # shape (k+2,)
        bad = np.zeros(nw, dtype=bool)  # shape (2^(k+2),)
        bad |= (W[:, pos < 0] != 0).any(axis=1)
        bad |= (W[:, pos == 0] != 1).any(axis=1)
        if white_end and d == J - 1:
            bad[1:] = True
        for i in np.nonzero(bad)[0]:
            hi[d * nw + i] = 0.0
        rows.append({d * nw + i: 1.0 for i in range(nw)})
        rhs.append(1.0)
    sub = index(W[:, 1:])  # shape (nw,) marginal of mu_d on positions d-1..d+k-1
    pre = index(W[:, :-1])  # shape (nw,) marginal of mu_{d+1} on positions d-1..d+k-1
    for d in range(J - 1):
        for m in range(1 << (k + 1)):
            r: dict[int, float] = {}
            for i in np.nonzero(sub == m)[0]:
                r[d * nw + i] = r.get(d * nw + i, 0.0) + 1.0
            for i in np.nonzero(pre == m)[0]:
                r[(d + 1) * nw + i] = r.get((d + 1) * nw + i, 0.0) - 1.0
            rows.append(r)
            rhs.append(0.0)
    if stationary:
        old = index(W[:, 2:])  # shape (nw,)
        new = index(image(W))  # shape (nw,)
        for d in range(J):
            for m in range(1 << k):
                r = {}
                for i in np.nonzero(new == m)[0]:
                    r[d * nw + i] = r.get(d * nw + i, 0.0) + 1.0
                for i in np.nonzero(old == m)[0]:
                    r[d * nw + i] = r.get(d * nw + i, 0.0) - 1.0
                rows.append(r)
                rhs.append(0.0)
    A = lil_matrix((len(rows), nvar))
    for t, r in enumerate(rows):
        for j, v in r.items():
            if v != 0.0:
                A[t, j] = v
    cost = np.zeros(nvar)  # shape (nvar,)
    for d in range(J):
        cost[d * nw: (d + 1) * nw] = (W[:, 2] == color)
    res = linprog(cost, A_eq=A.tocsr(), b_eq=np.array(rhs), bounds=list(zip(lo, hi, strict=True)), method="highs")
    assert res.status == 0, res.message
    return res.x.reshape(J, nw)  # shape (J, 2^(k+2))


def ordinary_white_bound(k: int) -> float:
    """Minimum white density over shift-invariant, stationary measures on (k+2)-words of the ordinary row."""
    W = words(k + 2)  # shape (2^(k+2), k+2)
    nw = W.shape[0]
    sub, pre = index(W[:, 1:]), index(W[:, :-1])  # shape (nw,) each
    old, new = index(W[:, 2:]), index(image(W))  # shape (nw,) each
    A = np.zeros((1 + (1 << (k + 1)) + (1 << k), nw))  # shape (1 + 2^(k+1) + 2^k, nw)
    A[0] = 1.0
    for m in range(1 << (k + 1)):
        A[1 + m] = (sub == m).astype(float) - (pre == m).astype(float)
    for m in range(1 << k):
        A[1 + (1 << (k + 1)) + m] = (new == m).astype(float) - (old == m).astype(float)
    b = np.zeros(A.shape[0])  # shape (rows,)
    b[0] = 1.0
    cost = (image(W)[:, 0] == 0).astype(float)  # shape (nw,)
    res = linprog(cost, A_eq=A, b_eq=b, bounds=(0, 1), method="highs")
    assert res.status == 0
    return float(res.fun)


def check_pair_potential() -> Fraction:
    """Exact check of 2[a XOR (b OR c)] + psi(b,c) <= 3[a white] + psi(a,b) for all a, b, c; returns 2/5."""
    psi = {(0, 0): 0, (0, 1): 1, (1, 0): 2, (1, 1): 2}
    for a, b, c in product((0, 1), repeat=3):
        y = a ^ (b | c)  # image cell above b
        assert 2 * y + psi[(b, c)] <= 3 * (1 - a) + psi[(a, b)]
    return Fraction(2, 5)


def white_end_feasible(J: int, k: int) -> bool:
    """Whether some range-k pseudo-measure on diagonals 0..J-1 has mu_{J-1} equal to the all-white word."""
    try:
        left_edge_solution(J, k, 1, white_end=True)
    except AssertionError:
        return False
    return True


def cycle_rows(n: int) -> list[tuple[int, ...]]:
    """The rows R[0..n-1] on the final cycle of the left-edge orbit of the single black cell, truncated to n diagonals."""
    row = (1,) + (0,) * (n - 1)
    seen: dict[tuple[int, ...], int] = {}
    orbit: list[tuple[int, ...]] = []
    while row not in seen:
        seen[row] = len(orbit)
        orbit.append(row)
        ext = (0, 0) + row
        row = tuple(ext[j] ^ (ext[j + 1] | ext[j + 2]) for j in range(n))
    return orbit[seen[row]:]


def empirical_pseudo_measure(n: int, J: int, k: int) -> list[list[Fraction]]:
    """The empirical range-k pseudo-measure of the final cycle on diagonals 0..J-1; needs J + k - 1 <= n."""
    assert J + k - 1 <= n
    cyc = cycle_rows(n)
    W = list(product((0, 1), repeat=k + 2))
    pos = {w: i for i, w in enumerate(W)}
    mu = [[Fraction(0)] * len(W) for _ in range(J)]
    for row in cyc:
        ext = (0, 0) + row
        for d in range(J):
            mu[d][pos[tuple(ext[d: d + k + 2])]] += Fraction(1, len(cyc))
    return mu


def verify_pseudo_measure(mu: list[list[Fraction]], k: int, white_end: bool = False) -> bool:
    """Exact check of boundary, shift, stationarity, nonnegativity, normalization (and optionally a white last word)."""
    W = [tuple(w) for w in product((0, 1), repeat=k + 2)]
    J = len(mu)
    for d in range(J):
        if any(v < 0 for v in mu[d]) or sum(mu[d]) != 1:
            return False
        for v, w in zip(mu[d], W, strict=True):
            if v != 0 and (any(w[j] for j in range(k + 2) if d - 2 + j < 0) or (d <= 1 and w[2 - d] != 1)):
                return False
        new: dict[tuple[int, ...], Fraction] = {}
        old: dict[tuple[int, ...], Fraction] = {}
        for v, w in zip(mu[d], W, strict=True):
            img = tuple(w[j - 2] ^ (w[j - 1] | w[j]) for j in range(2, k + 2))
            new[img] = new.get(img, Fraction(0)) + v
            old[w[2:]] = old.get(w[2:], Fraction(0)) + v
        if {x: y for x, y in new.items() if y} != {x: y for x, y in old.items() if y}:
            return False
    for d in range(J - 1):
        a: dict[tuple[int, ...], Fraction] = {}
        b: dict[tuple[int, ...], Fraction] = {}
        for v, w in zip(mu[d], W, strict=True):
            a[w[1:]] = a.get(w[1:], Fraction(0)) + v
        for v, w in zip(mu[d + 1], W, strict=True):
            b[w[:-1]] = b.get(w[:-1], Fraction(0)) + v
        if {x: y for x, y in a.items() if y} != {x: y for x, y in b.items() if y}:
            return False
    return mu[J - 1][0] == 1 or not white_end


def black_mass(mu: list[list[Fraction]], k: int) -> Fraction:
    """Total of mu_d[R_d = 1] over d; exact."""
    W = list(product((0, 1), repeat=k + 2))
    return sum((v for row in mu for v, w in zip(row, W, strict=True) if w[2] == 1), Fraction(0))


def cycle_density(J: int, n: int) -> np.ndarray:
    """Black density of diagonals 0..J-1 on the final cycle of the single cell, truncated to n >= J diagonals; shape (J,)."""
    cyc = np.array(cycle_rows(n))  # shape (period, n)
    return cyc[:, :J].mean(axis=0)  # shape (J,)


def matching_depth(J: int, k: int, prof: np.ndarray | None = None, tol: float = 1e-6) -> int:
    """Last diagonal d such that the optimal black profile equals the single cell's cycle density on diagonals 0..d."""
    # prof: (J,) when given
    if prof is None:
        prof = left_edge_profile(J, k, 1)  # shape (J,)
    true = cycle_density(J, J + k + 2)  # shape (J,)
    bad = np.nonzero(np.abs(prof - true) > tol)[0]
    return int(bad[0]) - 1 if len(bad) else J - 1


def tail_ratio(J: int, k: int, prof: np.ndarray | None = None) -> float:
    """Least-squares ratio of mu_d[R_d = 1] over diagonals where it lies in (1e-6, 0.03); a rough fit."""
    # prof: (J,) when given
    if prof is None:
        prof = left_edge_profile(J, k, 1)  # shape (J,)
    d = np.nonzero((prof > 1e-6) & (prof < 0.03))[0]  # shape (m,)
    if len(d) < 2:
        return float("nan")
    slope = np.polyfit(d, np.log(prof[d]), 1)[0]
    return float(np.exp(slope))


TABLE = [(1, 48), (2, 96), (3, 128), (4, 160), (5, 96), (5, 128), (5, 160), (6, 128)]


def successive_ratios(J: int, k: int, ds: range) -> list[float]:
    """mu_{d+1}[R = 1] / mu_d[R = 1] for d in ds, for the optimal black profile."""
    prof = left_edge_profile(J, k, 1)  # shape (J,)
    return [float(prof[d + 1] / prof[d]) for d in ds]


def table_rows(rows: list[tuple[int, int]] = TABLE) -> list[tuple[int, int, float, int, float]]:
    """(k, J, B_k(J), matching depth, tail ratio) for each table row; the large rows take up to about a minute each."""
    out: list[tuple[int, int, float, int, float]] = []
    for k, J in rows:
        prof = left_edge_profile(J, k, 1)  # shape (J,)
        out.append((k, J, float(prof.sum()), matching_depth(J, k, prof), tail_ratio(J, k, prof)))
        print(out[-1], flush=True)
    return out


def main() -> None:
    """The bounds of the entry, and the table with `--table`; the command line takes no other argument."""
    for k in range(1, 5):
        print("ordinary frame, white in image row, k =", k, ":", round(ordinary_white_bound(k), 6))
    for color in (1, 0):
        for k in (1, 2, 3, 4):
            vals = [left_edge_bound(J, k, color) for J in (4, 8, 16, 24, 32)]
            print("left edge color", color, "k", k, [round(v, 4) for v in vals], flush=True)
    if "--table" in sys.argv:
        table_rows()


if __name__ == "__main__":
    main()
