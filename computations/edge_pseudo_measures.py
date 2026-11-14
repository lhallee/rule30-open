"""Locally consistent pseudo-measures for Rule 30 and the linear programs they solve.

A pseudo-measure of range k on the left-edge frame is a family mu_0, ..., mu_{J-1} of probability vectors, mu_d on
the 2^(k+2) words of the row R on positions d-2, ..., d+k-1, with
  (boundary)    positions < 0 are white and position 0 is black,
  (shift)       mu_d and mu_{d+1} have the same marginal on positions d-1, ..., d+k-1,
  (stationary)  under mu_d, the image word R'[d..d+k-1] has the same law as R[d..d+k-1],
where R'_j = R_{j-2} XOR (R_{j-1} OR R_j). The empirical measure of every periodic orbit is one. The minimum of
sum_d mu_d[R_d = colour] over pseudo-measures equals, by linear programming duality, the best lower bound on the
time-averaged number of cells of that colour on diagonals 0..J-1 that a telescoping certificate (a spatial potential
on k+1 adjacent cells that may depend on d, plus a temporal potential on k adjacent cells) can prove.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import product

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix


def words(n: int) -> np.ndarray:
    """All 0/1 words of length n; shape (2^n, n), word index = sum bits[i] << (n-1-i)."""
    return np.array(list(product((0, 1), repeat=n)), dtype=np.int64)  # shape (2^n, n)


def image(word: np.ndarray) -> np.ndarray:
    """Rule 30 image R'[2..] of rows R given on a window; word shape (m, n) -> (m, n-2)."""
    a, b, c = word[:, :-2], word[:, 1:-1], word[:, 2:]
    return a ^ (b | c)  # shape (m, n-2)


def index(bits: np.ndarray) -> np.ndarray:
    """Integer index of each row of a 0/1 array; shape (m, n) -> (m,)."""
    n = bits.shape[1]
    return (bits * (1 << np.arange(n - 1, -1, -1))).sum(axis=1)  # shape (m,)


def left_edge_bound(J: int, k: int, colour: int, stationary: bool = True) -> float:
    """Minimum over range-k pseudo-measures on diagonals 0..J-1 of the expected number of cells of `colour`."""
    return left_edge_profile(J, k, colour, stationary).sum()


def left_edge_profile(J: int, k: int, colour: int, stationary: bool = True) -> np.ndarray:
    """mu_d[R_d = colour] for an optimal range-k pseudo-measure on diagonals 0..J-1; shape (J,)."""
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
        cost[d * nw: (d + 1) * nw] = (W[:, 2] == colour)
    res = linprog(cost, A_eq=A.tocsr(), b_eq=np.array(rhs), bounds=list(zip(lo, hi)), method="highs")
    assert res.status == 0, res.message
    x = res.x.reshape(J, nw)  # shape (J, 2^(k+2))
    return (x * (W[:, 2] == colour)).sum(axis=1)  # shape (J,)


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
    """Exact check of 2[y black] + psi(b,c) <= 3[a white] + psi(a,b) over all 5-cell windows; returns 2/5."""
    psi = {(0, 0): 0, (0, 1): 1, (1, 0): 2, (1, 1): 2}
    for u, v, a, b, c in product((0, 1), repeat=5):
        y = u ^ (v | a)  # image cell above a
        assert 2 * y + psi[(b, c)] <= 3 * (1 - a) + psi[(a, b)]
    return Fraction(2, 5)


if __name__ == "__main__":
    for k in range(1, 5):
        print("ordinary frame, white in image row, k =", k, ":", round(ordinary_white_bound(k), 6))
    for colour in (1, 0):
        for k in (1, 2, 3, 4):
            vals = [left_edge_bound(J, k, colour) for J in (4, 8, 16, 24, 32)]
            print("left edge colour", colour, "k", k, [round(v, 4) for v in vals], flush=True)
