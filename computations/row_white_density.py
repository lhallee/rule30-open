"""White cells of a row against the black runs of the next row, and the counts of both colors in the single cell's
light-cone triangle.

- `step`: one Rule 30 step on a finite window (the window shrinks by one cell on each side).
- `black_runs`: the maximal black runs of a 0/1 row, as (start, end) pairs, ends included.
- `run_white_bound`: for every black run [u, v] of the image, the white cells of the row on [u - 1, v], against the
  bound floor(2 (m + 1) / 3), m = v - u + 1.
- `triangle_counts`: the single cell's rows 0..n-1 on their cells -t..t: the black count B(t), the white count W(t),
  the longest black run M(t), and the sum over the black runs of row t of T(m), the area of the white triangle a
  newborn white run of length m starts.
- `psi`, `telescope_gap`: the potential of a pair of adjacent cells and the slack of the telescoped count
  3 (white cells of x on [a - 1, a + n - 2]) + psi(x_(a-1), x_a) - 2 (black cells of step x on [a, a + n - 1]) -
  psi(x_(a+n-1), x_(a+n)), which `Rule30Open.Foundations.RowWhiteDensity.telescope` proves nonnegative.
- `chain_check`: the classification of every maximal white run of a row into a continuation (the row above is white
  from one cell left to one cell right of it) or a newborn run (the row above is 1^k 0 1, 1^(k+1) 0 or 1^(k+2) there).

    python -m computations.row_white_density --n 3000      # the triangle counts to row 3,000, about 20 s
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass

import numpy as np
from tqdm.auto import tqdm


def step(row: np.ndarray) -> np.ndarray:
    """Rule 30 on a window: cell i of the result is row[i] xor (row[i + 1] or row[i + 2]), cells 1..len-2 of row."""
    # row: (L,) uint8 -> result: (L - 2,) uint8
    return row[:-2] ^ (row[1:-1] | row[2:])


def black_runs(row: np.ndarray) -> list[tuple[int, int]]:
    """The maximal black runs of row as (start, end) index pairs, ends included."""
    # row: (L,) uint8
    padded = np.concatenate(([0], row.astype(np.int8), [0]))  # (L + 2,)
    d = np.diff(padded)  # (L + 1,)
    starts = np.flatnonzero(d == 1)  # (r,)
    ends = np.flatnonzero(d == -1) - 1  # (r,)
    return list(zip(starts.tolist(), ends.tolist()))


def run_white_bound(row: np.ndarray) -> list[tuple[int, int]]:
    """For each black run [u, v] of step(row) (indices in row's frame), the pair (white cells of row on [u - 1, v],
    floor(2 (m + 1) / 3)). Image cell j sits over row cell j + 1, so run [u, v] of the image is [u + 1, v + 1] in row."""
    # row: (L,) uint8
    out: list[tuple[int, int]] = []
    for u, v in black_runs(step(row)):
        a, b = u + 1, v + 1  # the run in row's coordinates
        m = b - a + 1
        whites = int((row[a - 1:b + 1] == 0).sum())
        out.append((whites, (2 * (m + 1)) // 3))
    return out


PSI: dict[tuple[int, int], int] = {(0, 0): 0, (0, 1): 1, (1, 0): 2, (1, 1): 2}


def psi(a: int, b: int) -> int:
    """The potential of the adjacent cells a, b."""
    return PSI[(a, b)]


def telescope_gap(row: np.ndarray) -> int:
    """The slack of the telescoped count over the whole window: y = step(row) is the image on cells 1..L-2 of row."""
    # row: (L,) uint8, L >= 3
    y = step(row)  # (L - 2,) y[j] sits over row[j + 1]
    L = len(row)
    whites = int((row[:L - 2] == 0).sum())  # cells j for the image cells j + 1, j = 0..L-3
    return 3 * whites + psi(int(row[0]), int(row[1])) - 2 * int(y.sum()) - psi(int(row[L - 2]), int(row[L - 1]))


def triangle_area(k: int) -> int:
    """The white cells of the triangle a white run of length k starts: k + (k - 2) + (k - 4) + ... while positive."""
    return sum(k - 2 * j for j in range((k + 1) // 2))


@dataclass
class TriangleCounts:
    B: np.ndarray  # (n,) black cells of row t on -t..t
    W: np.ndarray  # (n,) white cells of row t on -t..t
    M: np.ndarray  # (n,) longest black run of row t
    T: np.ndarray  # (n,) sum over the black runs of row t of triangle_area(length)


def single_cell_rows(n: int) -> np.ndarray:
    """Rows 0..n-1 of the single cell on cells -n..n."""
    # result: (n, 2 n + 1) uint8, column n is cell 0
    rows = np.zeros((n, 2 * n + 1), dtype=np.uint8)
    row = np.zeros(2 * n + 5, dtype=np.uint8)  # (2 n + 5,) cell 0 at index n + 2
    row[n + 2] = 1
    for t in range(n):
        rows[t] = row[2:-2]
        row = np.concatenate(([0], step(row), [0]))
    return rows


def triangle_counts(n: int, progress: bool = True) -> TriangleCounts:
    """B, W, M and T for rows 0..n-1 of the single cell."""
    B = np.zeros(n, dtype=np.int64)  # (n,)
    W = np.zeros(n, dtype=np.int64)  # (n,)
    M = np.zeros(n, dtype=np.int64)  # (n,)
    T = np.zeros(n, dtype=np.int64)  # (n,)
    row = np.zeros(2 * n + 5, dtype=np.uint8)  # (2 n + 5,) cell 0 at index n + 2
    c = n + 2
    row[c] = 1
    for t in tqdm(range(n), disable=not progress, desc="rows"):
        seg = row[c - t:c + t + 1]  # (2 t + 1,)
        B[t] = int(seg.sum())
        W[t] = 2 * t + 1 - B[t]
        runs = black_runs(seg)
        M[t] = max(v - u + 1 for u, v in runs)
        T[t] = sum(triangle_area(v - u + 1) for u, v in runs)
        row = np.concatenate(([0], step(row), [0]))
    return TriangleCounts(B, W, M, T)


def chain_check(above: np.ndarray, below: np.ndarray) -> tuple[int, int, int]:
    """Classify the maximal white runs of `below` (cells 1..L-2 of the window `above` is on): returns (continuations,
    newborn, other). `below[j]` sits under `above[j + 1]`."""
    # above: (L,) uint8, below: (L - 2,) uint8, below == step(above)
    cont = new = other = 0
    for u, v in black_runs(1 - below):
        if u == 0 or v == len(below) - 1:
            continue  # the run touches the window's edge: its preimage window is not all inside `above`
        k = v - u + 1
        w = above[u:v + 3]  # (k + 2,) the cells over [u - 1, v + 1] of below
        s = "".join(map(str, w.tolist()))
        if s == "0" * (k + 2):
            cont += 1
        elif s in ("1" * k + "01", "1" * (k + 1) + "0", "1" * (k + 2)):
            new += 1
        else:
            other += 1
    return cont, new, other


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--n", type=int, default=3000)
    args = ap.parse_args()
    n = args.n
    tc = triangle_counts(n)
    A = np.cumsum(tc.B)  # (n,) black cells of rows < t + 1
    Wt = np.cumsum(tc.W)  # (n,)
    Tsum = np.cumsum(tc.T)  # (n,)
    Mmax = np.maximum.accumulate(tc.M)  # (n,)
    worst_pair = min(int(3 * tc.W[s - 1] + 6 - 2 * tc.B[s]) for s in range(1, n))
    print(f"rows 0..{n - 1}")
    for t in sorted({t for t in (99, 299, 999, 1999, n - 1) if t < n}):
        if True:
            m = t + 1
            print(f"n={m}: black {A[t] / m**2:.5f}, white {Wt[t] / m**2:.5f}, white bound 2(n-1)(n-2)/5 = "
                  f"{2 * (m - 1) * (m - 2) / 5 / m**2:.5f}, longest row black run {Mmax[t]}, "
                  f"sum T over runs of rows < n-1 {Tsum[t - 1]} >= white {Wt[t]}: {Tsum[t - 1] >= Wt[t]}, "
                  f"2n^2/(M+3) = {2 * m * m / (Mmax[t] + 3):.0f} <= black {A[t]}")
    print(f"least 3 W(s-1) + 6 - 2 B(s) over 1 <= s < n: {worst_pair}")
    rows = single_cell_rows(min(n, 600))
    tot = [0, 0, 0]
    for s in range(1, rows.shape[0]):
        r = chain_check(rows[s - 1], rows[s][1:-1])
        tot = [a + b for a, b in zip(tot, r)]
    print(f"white runs of rows 1..{rows.shape[0] - 1}: continuations {tot[0]}, newborn {tot[1]}, other {tot[2]}")


if __name__ == "__main__":
    main()
