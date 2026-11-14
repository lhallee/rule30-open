"""Numbers for Rule30Open.Diagonals.SkeletonWhiteDensity: the constant of the white bound and the single cell's actual
white fraction on its settled diagonals.

- `step_slack`: the least value of 3 W(R) + 2 W(leftStep R) - 2 J over all rows R of J diagonals (W counts white cells
  among diagonals 0 .. J-1); the Lean bound says it is at least -4.
- `skeleton_white`: the white fraction of the single cell's settled words of period 16, and the least ratio of
  5 W to (2J - 4) P over J (W the white cells of diagonals 0 .. J-1 over the period P = 16).

    python -m computations.skeleton_white_density   # about 15 s
"""

from __future__ import annotations

import numpy as np

from computations.depth_register import skeleton_weights


def left_step(row: list[int]) -> list[int]:
    s = [0, 0] + row
    return [s[d] ^ (s[d + 1] | s[d + 2]) for d in range(len(row))]


def step_slack(J: int) -> int:
    """min over the 2^J rows of 3 W(R) + 2 W(leftStep R) - 2 J."""
    best = 10 ** 9
    for x in range(1 << J):
        row = [(x >> d) & 1 for d in range(J)]
        best = min(best, 3 * (J - sum(row)) + 2 * (J - sum(left_step(row))) - 2 * J)
    return best


def skeleton_white(depth: int = 53200, steps: int = 82000, lo: int = 400) -> tuple[float, float]:
    wt = skeleton_weights(depth, steps, 16)  # (depth+1,) black cells per period 16
    whites = np.cumsum(16 - wt)  # (depth+1,) white cells of diagonals 0 .. J-1, J = 1 ..
    J = np.arange(1, depth + 2)  # (depth+1,)
    ratio = 5 * whites[2:] / ((2 * J[2:] - 4) * 16)  # (depth-1,)
    return float(1 - wt[lo:].mean() / 16), float(ratio.min())


def main() -> None:
    print("least slack 3W + 2W' - 2J, J = 1..12:", [step_slack(J) for J in range(1, 13)])
    frac, ratio = skeleton_white()
    print(f"white fraction of the settled words, depths 400 to 53,200: {frac:.4f}")
    print(f"least 5W / ((2J - 4) P) over J = 3 .. 53,201: {ratio:.4f}")


if __name__ == "__main__":
    main()
