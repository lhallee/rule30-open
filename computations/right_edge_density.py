"""Density of the single cell's first J right diagonals over one common period, against the doubling count.

Right-edge frame: bit e of the code at time t is the cell e places left of the right edge, R_e(t) = cell(t, t - e),
and T(y)_e = y_e xor (y_{e-1} or y_{e-2}) (y_{-1} = y_{-2} = 0).

- `step_slack`: least value of 3 W_J(c) + 2 W_J(T c) - 2 J over all codes of J bits (W_J: white bits among 0 .. J-1).
- `seed_rows`: the codes of the single cell, T^t(1), as bit arrays.
- `strip_counts`: for each J, the period L_J of bits 0 .. J-1, the number k of doublings among diagonals 1 .. J-1
  (L_J = 2^k), and the black and white cells of diagonals 0 .. J-1 over one period, with the bounds
  black >= L_J (1 + k/2), white >= L_J k/2 of the entry.

    python -m computations.right_edge_density   # about 5 s
"""

from __future__ import annotations

import numpy as np


def T(y: int, n: int) -> int:
    """One step on the n low bits of a code."""
    return (y ^ ((y << 1) | (y << 2))) & ((1 << n) - 1)


def step_slack(J: int) -> int:
    best = 10 ** 9
    for c in range(1 << J):
        w0 = J - bin(c).count("1")
        w1 = J - bin(T(c, J)).count("1")
        best = min(best, 3 * w0 + 2 * w1 - 2 * J)
    return best


def seed_rows(n: int, steps: int) -> np.ndarray:
    """(steps, n) array: bit e of T^t(1)."""
    out = np.zeros((steps, n), dtype=np.uint8)  # (steps, n)
    y = 1
    for t in range(steps):
        out[t] = [(y >> e) & 1 for e in range(n)]
        y = T(y, n)
    return out


def least_period(col: np.ndarray) -> int:
    """Least p (a power of two dividing len(col)) with col periodic of period p; col has shape (m,)."""
    m = len(col)
    p = 1
    while p < m and not np.array_equal(col, np.roll(col, -p)):
        p *= 2
    return p


def strip_counts(Jmax: int) -> list[tuple[int, int, int, int, int]]:
    """Rows (J, L_J, k, black, white) for J = 1 .. Jmax."""
    steps = 1 << 14
    rows = seed_rows(Jmax, steps)  # (steps, Jmax)
    per = [least_period(rows[:, e]) for e in range(Jmax)]
    out = []
    for J in range(1, Jmax + 1):
        L = max(per[:J])
        k = L.bit_length() - 1
        black = int(rows[:L, :J].sum())
        out.append((J, L, k, black, J * L - black))
    return out


def main() -> None:
    print("least slack 3W + 2W' - 2J, J = 1..12:", [step_slack(J) for J in range(1, 13)])
    print("| J | L_J | k_J | black | L(1 + k/2) | white | L k/2 | black density | white density |")
    print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for J, L, k, b, w in strip_counts(22):
        print(f"| {J} | {L} | {k} | {b} | {L + L * k // 2} | {w} | {L * k // 2} | {b / (J * L):.3f} | {w / (J * L):.3f} |")


if __name__ == "__main__":
    main()
