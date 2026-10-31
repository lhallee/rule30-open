"""Runs of the center column against the settled left diagonals: what a forced pattern excludes, given when and how
the diagonals settle.

A run of the center column forces a pattern on a trapezoid of the rows before its start (alternating cells for a black
run, and for a white run an alternating tail beside a white block). Read along the left diagonals
D_j(t) = cell(t, j - t), the pattern makes two adjacent diagonals alternate (black) or stay white (white block) over a
window of times. If both diagonals are periodic with period P over that window, the window extends forever, and that
contradicts the rule (adjacent alternating diagonals force D_0 to alternate; adjacent white diagonals do not occur).
This module computes the windows exactly, the longest run each hypothesis on the settling of the diagonals leaves open,
and the settling constants of the true orbit.

    python -m computations.diagonal_cones            # settling constants to depth 1200 and the implied slopes
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass

import numpy as np
from tqdm.auto import tqdm

from computations.rule30 import step


def diagonal_table(steps: int, depth: int) -> np.ndarray:
    """D[j, t] = cell(t, j - t) of the single cell for j < depth and t < steps."""
    width = 2 * steps + 3
    row = 1 << steps  # bit i is cell i - steps
    D = np.zeros((depth, steps), dtype=np.uint8)  # (depth, steps)
    for t in tqdm(range(steps), desc="evolve", unit="step", file=sys.stderr, mininterval=5):
        raw = np.frombuffer(row.to_bytes((width + 7) // 8, "little"), dtype=np.uint8)  # (width / 8,)
        cells = np.unpackbits(raw, bitorder="little")  # (8 ceil(width / 8),)
        D[:, t] = cells[steps - t:steps - t + depth]  # cells -t .. -t + depth - 1
        row = step(row)
    return D  # (depth, steps)


@dataclass(frozen=True, slots=True)
class Settling:
    """Eventual period and first time of exact periodicity of each diagonal."""

    period: np.ndarray  # (depth,) least power of two the diagonal repeats with
    onset: np.ndarray  # (depth,) first time from which D_j(t + period) = D_j(t) for every later t read


def settling(D: np.ndarray, window: int) -> Settling:
    """Periods from the last `window` steps; onsets from the whole table. `window` must exceed twice every period."""
    # D: (depth, steps)
    depth, steps = D.shape
    period = np.ones(depth, dtype=np.int64)  # (depth,)
    onset = np.zeros(depth, dtype=np.int64)  # (depth,)
    for j in range(depth):
        tail = D[j, steps - window:]  # (window,)
        p = 1
        while not np.array_equal(tail[p:], tail[:-p]):
            p *= 2
            assert 2 * p < window, f"window {window} is too short for diagonal {j}"
        period[j] = p
        mismatch = np.nonzero(D[j, p:] != D[j, :-p])[0]  # times t with D_j(t + p) != D_j(t)
        onset[j] = 0 if len(mismatch) == 0 else mismatch[-1] + 1
        assert onset[j] + 2 * p < steps, f"steps {steps} is too few for diagonal {j}"
    return Settling(period, onset)


def onset_slope(s: Settling, from_depth: int) -> tuple[float, int, int]:
    """The largest onset / depth ratio over depths >= from_depth, the depth that attains it, and the largest period."""
    depth = np.arange(len(s.onset))  # (depth,)
    ratio = s.onset[from_depth:] / depth[from_depth:]  # (depth - from_depth,)
    k = int(np.argmax(ratio))
    return float(ratio[k]), from_depth + k, int(s.period[from_depth:].max())


# --- the windows a forced pattern leaves on the diagonals ---

def settled_violations(D: np.ndarray, first: int = 8, period: int = 16) -> int:
    """Number of diagonals j >= first with D_j(t + period) != D_j(t) for some t >= ceil(3 j / 2) (the Lean hypothesis)."""
    bad = 0
    for j in range(first, D.shape[0]):
        t0 = (3 * j + 1) // 2
        assert t0 + 2 * period <= D.shape[1], "steps too short to test diagonal j"
        bad += int(not np.array_equal(D[j, t0 + period:], D[j, t0:-period]))
    return bad


def _ceil_div(x: np.ndarray, d: int) -> np.ndarray:
    """ceil(x / d) for integer arrays and d > 0."""
    return -((-x) // d)


def alternating_window(a: int, run: int, tail_end: int, j: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """First and last time at which diagonal j lies in the alternating trapezoid behind a run starting at time a.

    The trapezoid holds, at time a - s, the cells x with -(run - 1) - s <= x <= -(tail_end + 4 s); `tail_end` is 0
    for a black run (the alternating cells end at the center) and l + 2 for a white run whose first black cell to the
    right of the center is column l + 1. Diagonal j meets time a - s at x = j - a + s. Empty windows have last < first.
    """
    # j: (n,)
    s_low = np.maximum(0, _ceil_div(a - run + 1 - j, 2))  # (n,)
    s_high = (a - tail_end - j) // 5  # (n,)
    return a - s_high, a - s_low  # (n,), (n,)


def white_block_window(a: int, left: int, j: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """First and last time at which diagonal j lies in the white triangle under the white cells -left .. right of row a.

    The triangle holds, at time a + i, the cells -left + i .. right - i; diagonal j meets it from time a for as long as
    j - a - i >= -left + i, and only for a - left <= j <= a + right.
    """
    # j: (n,)
    last = a + (j - a + left) // 2  # (n,)
    return np.full_like(j, a), last  # (n,), (n,)


def black_excluded(a: int, run: int, gamma: float, period: int, first: int) -> bool:
    """Whether the hypothesis 'diagonals j >= first are `period`-periodic from time gamma j' excludes a black run."""
    j = np.arange(first, a)  # (n,)
    lo0, hi0 = alternating_window(a, run, 0, j)  # (n,)
    lo1, hi1 = alternating_window(a, run, 0, j + 1)  # (n,)
    lo, hi = np.maximum(lo0, lo1), np.minimum(hi0, hi1)  # (n,)
    settled = lo >= np.ceil(gamma * (j + 1))  # (n,)
    return bool(np.any(settled & (hi - lo >= period)))


def white_excluded(a: int, run: int, ell: int, gamma: float, period: int, first: int) -> bool:
    """Whether the hypothesis excludes a white run with first black cell right of the center at column ell + 1."""
    j = np.arange(first, a)  # (n,)
    if ell <= run - 3:  # an alternating tail of run - ell - 1 >= 2 cells beside the white block
        lo0, hi0 = alternating_window(a, run, ell + 2, j)  # (n,)
        lo1, hi1 = alternating_window(a, run, ell + 2, j + 1)  # (n,)
        lo, hi = np.maximum(lo0, lo1), np.minimum(hi0, hi1)  # (n,)
        if np.any((lo >= np.ceil(gamma * (j + 1))) & (hi - lo >= period)):
            return True
    left = min(ell, run - 1)
    lo0, hi0 = white_block_window(a, left, j)  # (n,)
    lo1, hi1 = white_block_window(a, left, j + 1)  # (n,)
    inside = (j >= a - left) & (j + 1 <= a + ell)  # (n,)
    hi = np.minimum(hi0, hi1)  # (n,)
    settled = lo0 >= np.ceil(gamma * (j + 1))  # (n,)
    return bool(np.any(inside & settled & (hi - lo0 + 1 >= period)))


def longest_open_black(a: int, gamma: float, period: int, first: int) -> int:
    """The longest black run starting at time a that the hypothesis leaves open (the exclusion grows with the run)."""
    low, high = 0, a + 1  # runs of length `low` are open, of length `high` excluded or longer than the row allows
    while high - low > 1:
        mid = (low + high) // 2
        if black_excluded(a, mid, gamma, period, first):
            high = mid
        else:
            low = mid
    return low


def longest_open_white(a: int, gamma: float, period: int, first: int) -> tuple[int, int]:
    """The longest white run starting at time a that the hypothesis leaves open, and the ell that attains it."""
    best, best_ell = 0, 0
    for ell in range(0, a - 2):
        low, high = 0, a + 1
        while high - low > 1:
            mid = (low + high) // 2
            if white_excluded(a, mid, ell, gamma, period, first):
                high = mid
            else:
                low = mid
        if low > best:
            best, best_ell = low, ell
    return best, best_ell


# --- the structure a white run leaves in its first row ---

def white_run_violations(limit: int) -> tuple[int, list[str]]:
    """Check, for every maximal white run of the center column starting at a < limit, the structure the argument uses.

    Let l be the number of white cells right of the center in row a, L the run's length and m = min(l, L - 1). Row a is
    white on -m .. l; row a - 1 is black on -m - 1 .. max(l - 1, 0); when l + 1 < L - 1, cell -(l + 1) of row a is black
    and cell -k is black exactly for odd k from l + 2 to L - 1; and L + 2 floor((a - l - 3) / 5) <= a.
    Returns the number of runs checked and a description of each violation.
    """
    row = 1 << limit  # bit i is cell i - limit
    rows: list[int] = []
    for _ in tqdm(range(limit + 1), desc="rows", unit="step", file=sys.stderr, mininterval=5):
        rows.append(row)
        row = step(row)

    def cell(t: int, x: int) -> int:
        return (rows[t] >> (limit + x)) & 1

    center = [cell(t, 0) for t in range(limit + 1)]
    checked, violations = 0, []
    for a in range(3, limit - 1):
        if center[a] != 0 or center[a - 1] != 1:
            continue
        run = 1
        while a + run <= limit and center[a + run] == 0:
            run += 1
        if a + run > limit:
            continue  # the run may continue past the table
        ell = 0
        while cell(a, ell + 1) == 0:
            ell += 1
        m = min(ell, run - 1)
        checked += 1
        ok = all(cell(a, x) == 0 for x in range(-m, ell + 1))
        ok &= all(cell(a - 1, x) == 1 for x in range(-m - 1, max(ell, 1)))
        if ell + 1 < run - 1:
            ok &= cell(a, -(ell + 1)) == 1
            ok &= all(cell(a, -k) == k % 2 for k in range(ell + 2, min(run, a)))
        s = max(a - ell - 3, 0) // 5
        ok &= run + 2 * s <= a
        if not ok:
            violations.append(f"a={a} L={run} l={ell}")
    return checked, violations


# --- what a strip of fixed depth can exclude ---

def strip_excluded(D: np.ndarray, a: int, run: int, k: int) -> bool:
    """Whether the alternating trapezoid behind a black run of length `run` from time a contradicts the true cells of
    depth < k (D[j, t], j < k) or the white cells left of the pattern, at some time a - s.

    The trapezoid holds, at time a - s, the cell -m black exactly for even m, from m = 4 s down to m = run - 1 + s.
    """
    # D: (depth >= k, steps > a)
    for s in range(0, a - 1):
        left, right = -(run - 1) - s, -4 * s  # cells of the trapezoid at time a - s
        if left > right:
            break
        x = np.arange(left, right + 1)  # (width,)
        expected = ((-x) % 2 == 0).astype(np.uint8)  # (width,)
        depth = x + (a - s)  # (width,), depth of each cell below the row's left edge
        outside = depth < 0
        if np.any(expected[outside] != 0):
            return True
        inside = (depth >= 0) & (depth < k)
        if np.any(D[depth[inside], a - s] != expected[inside]):
            return True
    return False


def longest_open_strip(D: np.ndarray, a: int, k: int) -> int:
    """The longest black run from time a that no conflict with the true strip of depth k excludes."""
    low, high = 0, a + 1
    while high - low > 1:
        mid = (low + high) // 2
        if strip_excluded(D, a, mid, k):
            high = mid
        else:
            low = mid
    return low


def slope_black(gamma: float) -> float:
    """Limit of the longest open black run over a: 3 (gamma - 1) / (5 gamma - 1)."""
    return 3 * (gamma - 1) / (5 * gamma - 1)


def slope_white(gamma: float) -> float:
    """Limit of the longest open white run over a: 1 - 1 / gamma (a white block of half-width a (1 - 1 / gamma))."""
    return 1 - 1 / gamma


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--depth", type=int, default=1200)
    parser.add_argument("--steps", type=int, default=3800)
    parser.add_argument("--window", type=int, default=512)
    args = parser.parse_args()

    D = diagonal_table(args.steps, args.depth)  # (depth, steps)
    s = settling(D, args.window)
    for from_depth in (8, 30, 100, 400):
        ratio, at, longest = onset_slope(s, from_depth)
        print(f"depths >= {from_depth}: onset / depth at most {ratio:.4f} (at {at}), periods at most {longest}")
    print(f"diagonals 8 <= j < {args.depth} violating period 16 from time 3j/2: {settled_violations(D)}")
    gamma = onset_slope(s, 8)[0]
    print(f"slopes at gamma = {gamma:.3f}: black {slope_black(gamma):.4f}, white {slope_white(gamma):.4f}")
    for g in (1.35, 1.5, 2.0, 2.5, 5.0, 1e9):
        print(f"gamma {g}: black {slope_black(g):.4f}, white {slope_white(g):.4f}")


if __name__ == "__main__":
    main()
