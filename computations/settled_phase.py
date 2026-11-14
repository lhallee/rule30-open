"""What the settled left region of a driven quadrant keeps of its driver, and two interface identities at the center.

A *quadrant* is the pattern on the cells i <= 0 at times t >= 0 that obeys Rule 30, x'_i = x_(i-1) xor (x_i or x_(i+1)),
at every cell i <= -1, from a finite left part `left` (cells -w..0 at time 0, `left[0]` = 1 the leftmost black cell,
`left[w]` = cell 0) with column 0 prescribed by a driver c (c(0) = left[w]). In the left-edge frame d = i + t + w the
diagonal d starts at time max(0, d - w), with the cell of `left` (d <= w) or the driver bit c(d - w) (d > w), and then
follows D_d(t + 1) = D_(d-2)(t) xor (D_(d-1)(t) or D_d(t)). Diagonal d therefore reads the driver only at times
0..d - w.

* `quadrant_diagonals`: the diagonals of a quadrant by that recursion.
* `quadrant_by_rows`: the same quadrant by stepping rows with column 0 overwritten by the driver, an independent check.
* `period_and_onset`: the eventual power-of-two period of one diagonal in the data and the time it starts.
* `skeleton_shift`: the one time shift k (mod the period) with D_d(t) = S_d(t + k) on a band of settled diagonals,
  where S is the single cell's own quadrant, or None.
* `interface_identity_holds`: for two finite rows, at every step s where their center cells agree at s and s + 1, the
  difference of columns -1 equals the difference of columns 1 masked by the white steps of the center.
* `prefix_shift_trials`, `grafted_shifts`, `first_period_depths`: the shift for drivers that share a prefix, for the
  center column followed by a repeated block from time T, and the depths where the skeleton's periods first appear.
* `latch_entropy`: the entropy of the sequences a with a(t) = 1 => a(t + 1) = not b(t mod P), from the product of the
  2x2 transfer matrices, and `latch_count` the number of such words by enumeration.

    python -m computations.settled_phase            # the numbers of the entry (about a minute)
"""

from __future__ import annotations

import argparse
import itertools
import math
import sys

import numpy as np
from tqdm.auto import tqdm

from computations.rule30 import center_column, step

DRIVER_BLOCKS = ("10", "100", "110", "1101", "10110", "1011100", "10000000")


def quadrant_diagonals(left: np.ndarray, driver: np.ndarray, depth: int) -> np.ndarray:
    """The diagonals 0..depth-1 of the quadrant of `left` driven by `driver`, at times 0..len(driver)-1; entries before
    a diagonal's start time are 0 and unused."""
    # left: (w + 1,), driver: (n,)
    w = len(left) - 1
    n = len(driver)
    assert left[0] == 1 and driver[0] == left[w]
    rows: list[list[int]] = []
    for d in range(depth):
        start = max(0, d - w)
        row = [0] * n
        row[start] = int(left[d]) if d <= w else int(driver[d - w])
        lower2 = rows[d - 2] if d >= 2 else None
        lower1 = rows[d - 1] if d >= 1 else None
        for t in range(start, n - 1):
            a = lower2[t] if lower2 is not None else 0
            b = lower1[t] if lower1 is not None else 0
            row[t + 1] = a ^ (b | row[t])
        rows.append(row)
    return np.array(rows, dtype=np.uint8)  # (depth, n)


def quadrant_by_rows(left: np.ndarray, driver: np.ndarray, depth: int) -> np.ndarray:
    """The same diagonals as `quadrant_diagonals`, by stepping whole rows of the cells -w-n..0 and overwriting cell 0
    with the driver after each step."""
    # left: (w + 1,), driver: (n,)
    w = len(left) - 1
    n = len(driver)
    width = w + n + 1  # cells -(w + n)..0 at bits width-1..0 (bit 0 is cell 0)
    row = 0
    for j, bit in enumerate(left):  # cell j - w at bit w - j
        row |= int(bit) << (w - j)
    out = np.zeros((depth, n), dtype=np.uint8)  # (depth, n)
    mask = (1 << width) - 1
    for t in range(n):
        for d in range(depth):
            bit = t + w - d  # diagonal d at time t is cell d - t - w, at bit t + w - d
            if t >= max(0, d - w) and bit < width:
                out[d, t] = (row >> bit) & 1
        if t + 1 < n:
            # bit k is cell -k: the left neighbor of cell -k is bit k + 1, the right neighbor bit k - 1
            nxt = ((row >> 1) ^ (row | (row << 1))) & mask
            nxt = (nxt & ~1) | int(driver[t + 1])
            row = nxt
    return out  # (depth, n)


def period_and_onset(diagonal: np.ndarray, start: int, max_log: int = 8) -> tuple[int, int] | None:
    """The least power of two p with the data p-periodic on their second half, and the least time T >= start from
    which the whole diagonal is p-periodic in the data; None if no p up to 2^max_log fits."""
    # diagonal: (n,)
    n = len(diagonal)
    half = n // 2
    for e in range(max_log + 1):
        p = 1 << e
        if np.array_equal(diagonal[half - p : n - p], diagonal[half:]):
            bad = np.nonzero(diagonal[start : n - p] != diagonal[start + p : n])[0]  # (m,)
            return p, (start + int(bad[-1]) + 1 if len(bad) else start)
    return None


def skeleton_shift(
    diagonals: np.ndarray, skeleton: np.ndarray, depths: range, window: int, max_shift: int = 64
) -> int | None:
    """The least k in [0, max_shift) with diagonals[d, t] = skeleton[d, t + k] for every d in `depths` and every t in
    the last `window` + max_shift times but max_shift, or None."""
    # diagonals: (depth, n), skeleton: (depth, n)
    n = diagonals.shape[1]
    lo, hi = n - window - max_shift, n - max_shift
    for k in range(max_shift):
        if all(np.array_equal(diagonals[d, lo:hi], skeleton[d, lo + k : hi + k]) for d in depths):
            return k
    return None


def seed_left(driver_bit: int = 1) -> np.ndarray:
    """The single cell's left part: one black cell at column 0."""
    return np.array([driver_bit], dtype=np.uint8)  # (1,)


def periodic_driver(block: str, n: int, first: int = 1) -> np.ndarray:
    """The block repeated from time 0, with c(0) replaced by `first` so that it can drive the given left part."""
    bits = np.array([int(ch) for ch in block], dtype=np.uint8)  # (P,)
    out = np.tile(bits, n // len(bits) + 1)[:n].copy()  # (n,)
    out[0] = first
    return out  # (n,)


def rows_columns(row: int, origin: int, steps: int, columns: tuple[int, ...]) -> np.ndarray:
    """Columns of the orbit of a finite row (an integer whose bit k is cell k - origin), at times 0..steps-1."""
    out = np.zeros((len(columns), steps), dtype=np.uint8)  # (len(columns), steps)
    for t in range(steps):
        for j, col in enumerate(columns):
            out[j, t] = (row >> (col + origin)) & 1
        row = step(row)
    return out  # (len(columns), steps)


def interface_identity_holds(row_a: int, row_b: int, origin: int, steps: int) -> tuple[bool, int]:
    """Whether, at every step s < steps - 1 where the center cells of the two orbits agree at s and s + 1, the XOR of
    their columns -1 equals (not c(s)) and the XOR of their columns 1; and the number of such steps."""
    cols_a = rows_columns(row_a, origin, steps, (-1, 0, 1))  # (3, steps)
    cols_b = rows_columns(row_b, origin, steps, (-1, 0, 1))  # (3, steps)
    ok = True
    used = 0
    for s in range(steps - 1):
        if cols_a[1, s] == cols_b[1, s] and cols_a[1, s + 1] == cols_b[1, s + 1]:
            used += 1
            left = cols_a[0, s] ^ cols_b[0, s]
            right = (1 - cols_a[1, s]) & (cols_a[2, s] ^ cols_b[2, s])
            ok = ok and left == right
    return ok, used


def latch_matrix(bit: int) -> np.ndarray:
    """Transfer matrix of one step of the latch a(t) = 1 => a(t + 1) = not bit, on states a(t) in {0, 1}."""
    if bit:
        return np.array([[1, 1], [1, 0]], dtype=np.int64)  # (2, 2): from 1 only to 0
    return np.array([[1, 1], [0, 1]], dtype=np.int64)  # (2, 2): from 1 only to 1


def latch_entropy(block: str) -> float:
    """Entropy per step (natural log) of the latch sequences driven by the repeated block."""
    product = np.eye(2, dtype=np.float64)  # (2, 2)
    for ch in block:
        product = product @ latch_matrix(int(ch)).astype(np.float64)
    radius = max(abs(np.linalg.eigvals(product)))
    return math.log(radius) / len(block)


def latch_count(block: str, length: int) -> int:
    """The number of 0/1 words a(0..length-1) with a(t) = 1 => a(t + 1) = not block[t mod P], by enumeration."""
    P = len(block)
    count = 0
    for word in itertools.product((0, 1), repeat=length):
        if all(not word[t] or word[t + 1] == 1 - int(block[t % P]) for t in range(length - 1)):
            count += 1
    return count


def prefix_shift_trials(
    prefixes: tuple[int, ...], trials: int, n: int, depth: int, seed: int = 5
) -> dict[int, list[int | None]]:
    """For each m, `trials` drivers that share a random prefix of length m and are random afterwards: the shift of
    each one's quadrant (single cell's left part) against the skeleton on depths 70..min(depth, 100) - 1, mod 8."""
    skeleton = quadrant_diagonals(seed_left(), center_column(n), depth)  # (depth, n)
    rng = np.random.default_rng(seed)
    out: dict[int, list[int | None]] = {}
    for m in tqdm(prefixes, file=sys.stderr):
        base = rng.integers(0, 2, n).astype(np.uint8)  # (n,)
        base[0] = 1
        shifts: list[int | None] = []
        for _ in range(trials):
            driver = base.copy()  # (n,)
            driver[m:] = rng.integers(0, 2, n - m)
            diagonals = quadrant_diagonals(seed_left(), driver, depth)  # (depth, n)
            shifts.append(skeleton_shift(diagonals, skeleton, range(70, min(depth, 100)), 40, 8))
        out[m] = shifts
    return out


def grafted_shifts(
    onsets: tuple[int, ...], blocks: tuple[str, ...], n: int, depth: int
) -> dict[int, list[tuple[int | None, bool]]]:
    """For each onset T and block: the driver equal to the single cell's center column before T and to the block
    repeated from T. Returns its quadrant's shift against the skeleton on depths 70..99 and whether every diagonal
    below `depth` has the skeleton's eventual period."""
    column = center_column(n)  # (n,)
    skeleton = quadrant_diagonals(seed_left(), column, depth)  # (depth, n)
    periods = [period_and_onset(skeleton[d], d) for d in range(depth)]
    out: dict[int, list[tuple[int | None, bool]]] = {}
    for onset in tqdm(onsets, file=sys.stderr):
        row: list[tuple[int | None, bool]] = []
        for block in blocks:
            driver = column.copy()  # (n,)
            driver[onset:] = periodic_driver(block, n - onset, int(block[0]))
            diagonals = quadrant_diagonals(seed_left(), driver, depth)  # (depth, n)
            found = [period_and_onset(diagonals[d], d) for d in range(depth)]
            same = all(f is not None and p is not None and f[0] == p[0] for f, p in zip(found, periods))
            row.append((skeleton_shift(diagonals, skeleton, range(70, 100), 40, 16), same))
        out[onset] = row
    return out


def first_period_depths(n: int, depth: int) -> dict[int, int]:
    """The least depth at which a diagonal of the single cell's left half has each eventual period, in the data."""
    skeleton = quadrant_diagonals(seed_left(), center_column(n), depth)  # (depth, n)
    first: dict[int, int] = {}
    for d in range(depth):
        found = period_and_onset(skeleton[d], d)
        if found is not None:
            first.setdefault(found[0], d)
    return first


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--steps", type=int, default=8000)
    parser.add_argument("--depth", type=int, default=120)
    args = parser.parse_args(argv)
    n, depth = args.steps, args.depth
    skeleton = quadrant_diagonals(seed_left(), center_column(n), depth)  # (depth, n)
    rng = np.random.default_rng(0)
    drivers: dict[str, np.ndarray] = {"seed": center_column(n)}
    random_driver = rng.integers(0, 2, n).astype(np.uint8)  # (n,)
    random_driver[0] = 1
    drivers["random"] = random_driver
    for block in DRIVER_BLOCKS:
        drivers[block] = periodic_driver(block, n)
    seed_periods = [period_and_onset(skeleton[d], d) for d in range(depth)]
    print(f"single cell's left part, diagonals 0..{depth - 1}, times 0..{n - 1}")
    print("driver       same periods  max onset age  shift on depths 70..100")
    for name, driver in tqdm(drivers.items(), file=sys.stderr):
        diagonals = quadrant_diagonals(seed_left(), driver, depth)  # (depth, n)
        found = [period_and_onset(diagonals[d], d) for d in range(depth)]
        same = all(f is not None and s is not None and f[0] == s[0] for f, s in zip(found, seed_periods))
        age = max(f[1] - d for d, f in enumerate(found) if f is not None)
        shift = skeleton_shift(diagonals, skeleton, range(70, 100), 40, 16)
        print(f"{name:12s} {str(same):13s} {age:13d}  {shift}")
    trials = prefix_shift_trials((20, 30, 34, 36, 40, 60), 8, 6000, depth)
    print("shared prefix length: shifts of 8 drivers")
    for m, shifts in trials.items():
        print(f"  {m:3d} {shifts}")
    print("the center column before T, a block repeated from T: (shift, same periods) for blocks", DRIVER_BLOCKS[:6])
    for onset, row in grafted_shifts((25, 30, 50, 100), DRIVER_BLOCKS[:6], n, depth).items():
        print(f"  T = {onset:3d} {row}")
    print("first depth of each period (diagonals < 600, times < 40,000):", first_period_depths(40000, 600))
    print("latch entropy per step: block, h, the bound log(2)/P (P >= 2)")
    for block in ("0", "1", "10", "100", "110", "1101"):
        print(f"  {block:6s} {latch_entropy(block):.6f} {math.log(2) / len(block):.6f}")


if __name__ == "__main__":
    main()
