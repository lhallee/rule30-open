"""How long a finite row's center can follow a prescribed word, for every right half at once, and where Condrey's proof stops.

Fix the center word c (a period of the column, "0" or "1" for the constant columns of Condrey 2026, "10" or "01" for
period two) and a right half R at time 0. The left half that keeps the center on c forever is the row Psi(R) of
`computations.coupled`: its cell at depth j + 1 (column -j - 1) is bit j. A finite left half of width M that agrees with
Psi(R) on the depths 1 .. M keeps the center on c at the times 0 .. d - 1 and leaves it at time d, where d is the first
black depth of Psi(R) beyond M, and no other left half of width M does better. So the longest run of a row with right
half R and left width M is d, found for every R of a width at once by running Psi on all of them as NumPy bit slices.

`horizon_table` takes the maximum over every R of at most `right` cells and every phase of the word, for support radius
A = right = M: the analogue of the w + 2 of Condrey's Corollary 8, which this reproduces for the words "0" and "1".
`subfunction_profile` counts the distinct residual functions of one cell of Psi(R) after the first k cells of R are
fixed (the width of its decision diagram in the natural order). For the constant words that width is at most 3, the
running OR of Condrey's Theorem 2; for the alternating word it grows with the number of cells.

    python -m computations.alternating_horizon table --max-radius 20            # about 1 min
    python -m computations.alternating_horizon profile --cells 18 --depth 16    # seconds
    python -m computations.alternating_horizon tails --cells 12 --depth 1500    # about 1 min
"""

from __future__ import annotations

import argparse
from collections import Counter

import numpy as np
from tqdm.auto import tqdm

from computations.coupled import center, eventual_period, psi

U64 = np.uint64
MAX_DEPTH = 61  # steps = depth + 1 <= 62 keeps every shifted-out right cell too far to reach column 1 in time


def psi_batch(word: str, phase: int, rights: np.ndarray, depth: int) -> np.ndarray:
    """Psi(R) at depths 1 .. `depth` for every right half in `rights`, bit j being the cell at depth j + 1."""
    # rights: (n,) uint64, bit i is column i + 1
    assert 0 < depth <= MAX_DEPTH
    steps = depth + 1
    c = center(word, phase, steps)
    row = rights.astype(U64)  # (n,)
    column = np.zeros_like(row)  # (n,), column 1, bit t is time t
    one = U64(1)
    for t in range(steps):
        column |= (row & one) << U64(t)
        row = ((row << one) | U64((c >> t) & 1)) ^ (row | (row >> one))
    a = ((U64(c >> 1)) ^ (U64(c) | column)) & U64((1 << depth) - 1)  # (n,), column -1 at times < depth
    b = np.full_like(a, U64(c))  # (n,), column 0
    out = np.zeros_like(a)  # (n,)
    for j in range(depth):
        out |= (a & one) << U64(j)
        a, b = (a >> one) ^ (a | b), a
    return out


def lowest_bit(x: np.ndarray) -> np.ndarray:
    """Index of the lowest set bit of each entry of a uint64 array, and -1 where the entry is 0."""
    # x: (n,)
    isolated = x & (~x + U64(1))  # (n,)
    out = np.full(x.shape, -1, dtype=np.int64)
    nonzero = x != 0
    out[nonzero] = np.log2(isolated[nonzero].astype(np.float64)).astype(np.int64)  # exact for powers of two
    return out


def run_length(word: str, phase: int, rights: np.ndarray, left_width: int, depth: int) -> np.ndarray:
    """The number of times 0 .. d - 1 at which the best left half of width `left_width` keeps the center on the word, for
    each right half; entries are censored (equal to depth + 1) when Psi(R) has no black cell in depths up to `depth`."""
    rows = psi_batch(word, phase, rights, depth)  # (n,)
    beyond = rows >> U64(left_width)
    low = lowest_bit(beyond)  # (n,)
    return np.where(low < 0, depth + 1, left_width + low + 1)  # (n,)


def horizon_table(word: str, max_radius: int, extra: int = 40, chunk: int = 1 << 22) -> list[tuple[int, int, int, int]]:
    """For each support radius A = 1 .. max_radius, the longest run over every row with support in [-A, A], a center
    cell at time 0 matching the word, both phases of the word: (A, longest run, number of right halves reaching it
    (both phases), a right half that does). The zero row is excluded. Psi is computed once for every right half of
    `max_radius` cells and read at each radius."""
    depth = min(MAX_DEPTH, max_radius + extra)
    best = [0] * (max_radius + 1)
    count = [0] * (max_radius + 1)
    witness = [-1] * (max_radius + 1)
    total = len(word) * -(-(1 << max_radius) // chunk)
    with tqdm(total=total, desc=f"word {word}", leave=False) as bar:
        for phase in range(len(word)):
            for start in range(0, 1 << max_radius, chunk):
                rights = np.arange(start, min(1 << max_radius, start + chunk), dtype=U64)  # (n,)
                rows = psi_batch(word, phase, rights, depth)  # (n,)
                for radius in range(1, max_radius + 1):
                    if start >= 1 << radius:
                        break
                    size = min(len(rights), (1 << radius) - start)
                    low = lowest_bit(rows[:size] >> U64(radius))  # (size,)
                    runs = np.where(low < 0, depth + 1, radius + low + 1)  # (size,)
                    if start == 0 and word[phase] == "0" and int(rows[0]) & ((1 << radius) - 1) == 0:
                        runs[0] = radius  # the zero row is out; a lone black cell at the last depth runs `radius` steps
                    top = int(runs.max())
                    assert top <= depth, f"censored at radius {radius}: raise `extra`"
                    if top > best[radius]:
                        best[radius], count[radius], witness[radius] = top, 0, start + int(np.argmax(runs))
                    if top == best[radius]:
                        count[radius] += int((runs == top).sum())
                bar.update(1)
    return [(radius, best[radius], count[radius], witness[radius]) for radius in range(1, max_radius + 1)]


def subfunction_profile(word: str, phase: int, cells: int, depth: int) -> list[list[int]]:
    """For each cell depth 1 .. `depth` of Psi(R), as a function of the `cells` cells of R, the number of distinct
    functions of the remaining cells left after the first k cells are fixed, for k = 0 .. cells."""
    rights = np.arange(1 << cells, dtype=U64)  # (2^cells,)
    rows = psi_batch(word, phase, rights, depth)  # (2^cells,)
    profile = []
    for j in range(depth):
        table = ((rows >> U64(j)) & U64(1)).astype(np.uint8)  # (2^cells,), index = R, first cell is the low bit
        widths = []
        for k in range(cells + 1):
            columns = table.reshape(1 << (cells - k), 1 << k)  # (rest, fixed): column = the first k cells
            packed = np.packbits(columns, axis=0).T  # (fixed, ceil(rest / 8))
            widths.append(len(np.unique(packed, axis=0)))
        profile.append(widths)
    return profile


def tail_census(word: str, phase: int, cells: int, depth: int, max_period: int = 200) -> Counter:
    """For every right half of at most `cells` cells, the least period (up to `max_period`) with which Psi(R) repeats over
    its outer half out to `depth`, or None: how many right halves end in a spatially periodic tail."""
    census: Counter = Counter()
    for right in tqdm(range(1 << cells), desc=f"tails {word}/{phase}", leave=False):
        found = eventual_period(psi(word, phase, right, depth), depth, max_period)
        census[None if found is None else found[1]] += 1
    return census


def brute_runs(word: str, phase: int, right_cells: int, left_width: int, steps: int) -> dict[int, int]:
    """Independent check by stepping whole rows: for each right half R of `right_cells` cells, the longest run of the word
    over every left half of at most `left_width` cells (the zero row skipped). Rows are Python integers whose bit i is
    column i - origin, with room below for the left edge to move."""
    best: dict[int, int] = {}
    pad = steps + 1
    origin = left_width + pad
    for right in range(1 << right_cells):
        top = 0
        for left in range(1 << left_width):
            row = (((right << 1) | int(word[phase])) << left_width | left) << pad
            if row == 0:
                continue
            run = 0
            for t in range(steps):
                if ((row >> origin) & 1) != int(word[(t + phase) % len(word)]):
                    break
                run += 1
                row = (row << 1) ^ (row | (row >> 1))
            top = max(top, run)
        best[right] = top
    return best


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = parser.add_subparsers(dest="mode", required=True)
    t = sub.add_parser("table")
    t.add_argument("--max-radius", type=int, default=16)
    t.add_argument("--words", nargs="+", default=["0", "1", "10"])
    p = sub.add_parser("profile")
    p.add_argument("--cells", type=int, default=16)
    p.add_argument("--depth", type=int, default=14)
    p.add_argument("--words", nargs="+", default=["0", "1", "10", "01"])
    q = sub.add_parser("tails")
    q.add_argument("--cells", type=int, default=12)
    q.add_argument("--depth", type=int, default=1500)
    q.add_argument("--words", nargs="+", default=["0", "1", "10"])
    args = parser.parse_args()
    if args.mode == "tails":
        for word in args.words:
            for phase in range(len(word)):
                census = tail_census(word, phase, args.cells, args.depth)
                aperiodic = census.pop(None, 0)
                print(f"word {word} phase {phase}: {aperiodic} of {1 << args.cells} right halves have no period up to 200 "
                      f"by depth {args.depth}; periods of the rest: {dict(sorted(census.items()))}")
    elif args.mode == "table":
        for word in args.words:
            print(f"word {word}: radius, longest run, rows reaching it, an R that does")
            for radius, best, count, witness in horizon_table(word, args.max_radius):
                print(f"  {radius:3d} {best:4d} {count:8d} {witness}")
    else:
        for word in args.words:
            for phase in range(len(word)):
                profile = subfunction_profile(word, phase, args.cells, args.depth)
                widest = [max(widths) for widths in profile]
                print(f"word {word} phase {phase}: widest level of the diagram for depths 1..{args.depth}: {widest}")


if __name__ == "__main__":
    main()
