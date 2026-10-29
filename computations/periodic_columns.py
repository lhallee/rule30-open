"""Finite rows with a column that repeats from time 0: an exhaustive search over small supports, with controls.

An eventually periodic column of a finite row is a column that repeats from time 0 in a later row, so the general
form of Problem 1 for finite rows asks whether some column of some finite nonzero row repeats from time 0. Take every
row whose black cells lie in cells 0 .. w - 1, run it for `steps` steps, and watch every column within `max_period`
cells of the support (farther columns stay white until an edge reaches them and then turn black, which no period up to
`max_period` survives). A (row, column, period) triple survives while the column has repeated with that period at every
time so far. Rows are bit-sliced: bit i of lane l of the array at cell x is cell x of row 64 l + i, so one step of the
rule is three operations on whole arrays.

The same search under Rule 90 and Rule 150, whose single-cell center columns are periodic, is the control that the
search sees a repeating column when there is one.

    python -m computations.periodic_columns --cells 20 --max-period 32 --steps 256
    python -m computations.periodic_columns --cells 12 --max-period 32 --steps 256 --rule 90   # the control
"""

from __future__ import annotations

import argparse
import sys
import time
import numpy as np

from tqdm.auto import tqdm


ALL = np.uint64(0xFFFFFFFFFFFFFFFF)
LOW_PATTERNS = [0xAAAAAAAAAAAAAAAA, 0xCCCCCCCCCCCCCCCC, 0xF0F0F0F0F0F0F0F0, 0xFF00FF00FF00FF00, 0xFFFF0000FFFF0000,
                0xFFFFFFFF00000000]  # bit i of word = bit j of i, for j < 6


def initial_rows(cells: int, first_lane: int, lanes: int, width: int, origin: int) -> np.ndarray:
    """Bit-sliced initial rows for row numbers 64 first_lane .. 64 (first_lane + lanes) - 1: cell `origin + j` of row r
    is bit j of r, for j < cells, and every other cell is white."""
    rows = np.zeros((width, lanes), dtype=np.uint64)  # (width, lanes)
    lane_index = np.arange(first_lane, first_lane + lanes, dtype=np.uint64)  # (lanes,)
    for j in range(cells):
        if j < 6:
            rows[origin + j] = np.uint64(LOW_PATTERNS[j])
        else:
            rows[origin + j] = np.where((lane_index >> np.uint64(j - 6)) & np.uint64(1), ALL, np.uint64(0))
    return rows  # (width, lanes)


def step(rows: np.ndarray, rule: int) -> np.ndarray:
    """One step of Rule 30, 90 or 150 on bit-sliced rows, white beyond both ends."""
    # rows: (width, lanes)
    left = np.zeros_like(rows)  # (width, lanes), cell x - 1
    left[1:] = rows[:-1]
    right = np.zeros_like(rows)  # (width, lanes), cell x + 1
    right[:-1] = rows[1:]
    if rule == 30:
        return left ^ (rows | right)
    if rule == 90:
        return left ^ right
    if rule == 150:
        return left ^ rows ^ right
    raise ValueError(f"rule {rule} is not 30, 90 or 150")


def survivors(cells: int, max_period: int, steps: int, rule: int, first_lane: int,
              lanes: int) -> tuple[list[tuple[int, int, int]], int, tuple[int, int, int] | None]:
    """The (row, column, period) triples, among rows 64 first_lane .. 64 (first_lane + lanes) - 1 and columns within
    `max_period` of the support, whose column repeats with that period at every time up to `steps`; the column is
    given relative to cell 0 of the support. Row 0, the white row, is left out. Also the longest repetition seen in a
    column of the support, the most times it was checked to repeat with a period before it first did not, and one
    triple that attains it. (Columns outside the support repeat trivially while they are white, before an edge
    arrives, so they are left out of this measure.)"""
    origin = max_period + steps + 2
    width = origin + cells + steps + max_period + 2
    rows = initial_rows(cells, first_lane, lanes, width, origin)  # (width, lanes)
    columns = np.arange(origin - max_period, origin + cells + max_period)  # (k,)
    history = np.zeros((max_period, columns.size, lanes), dtype=np.uint64)  # (P, k, lanes), ring of past columns
    alive = np.full((max_period, columns.size, lanes), ALL, dtype=np.uint64)  # (P, k, lanes), bit i: row 64 l + i
    if first_lane == 0:
        alive[:, :, 0] &= ~np.uint64(1)  # the white row repeats trivially
    longest, witness = 0, None
    for t in range(steps):
        current = rows[columns]  # (k, lanes)
        for p in range(1, min(t, max_period) + 1):
            alive[p - 1] &= ~(history[(t - p) % max_period] ^ current)
        history[t % max_period] = current
        tested = alive[:min(t, max_period)]  # (p, k, lanes), periods checked at least once
        inside = tested[:, max_period:max_period + cells]  # (p, cells, lanes), the columns of the support
        if inside.any():
            p, k, lane = (int(i[0]) for i in np.nonzero(inside))  # the least period still alive
            if t - p > longest:  # period p + 1 has been checked at times p + 1 .. t
                bit = (int(inside[p, k, lane]) & -int(inside[p, k, lane])).bit_length() - 1
                longest, witness = t - p, (64 * (first_lane + lane) + bit, k, p + 1)
        if t >= max_period and not tested.any():
            return [], longest, witness
        rows = step(rows, rule)
    found = []
    for p, k, lane in zip(*np.nonzero(alive)):
        word = int(alive[p, k, lane])
        for bit in range(64):
            if (word >> bit) & 1:
                found.append((64 * (first_lane + int(lane)) + bit, int(columns[k]) - origin, int(p) + 1))
    return found, longest, witness


def search(cells: int, max_period: int, steps: int, rule: int,
           chunk: int = 256) -> tuple[list[tuple[int, int, int]], int, tuple[int, int, int] | None]:
    """Every surviving (row, column, period) triple over all rows with black cells in cells 0 .. cells - 1, the
    longest repetition seen (checked times before the first miss), and a triple that attains it."""
    lanes_total = max(1, (1 << cells) // 64)
    found, longest, witness = [], 0, None
    for first in tqdm(range(0, lanes_total, chunk), desc=f"rule {rule}, {cells} cells", file=sys.stderr, leave=False):
        more, last, seen = survivors(cells, max_period, steps, rule, first, min(chunk, lanes_total - first))
        found += more
        if last > longest and seen is not None and seen[0] < (1 << cells):
            longest, witness = last, seen
    return [f for f in found if f[0] < (1 << cells)], longest, witness


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--cells", type=int, default=20)
    parser.add_argument("--max-period", type=int, default=32)
    parser.add_argument("--steps", type=int, default=256)
    parser.add_argument("--rule", type=int, default=30, choices=[30, 90, 150])
    args = parser.parse_args()

    started = time.perf_counter()
    found, longest, witness = search(args.cells, args.max_period, args.steps, args.rule)
    rows = sorted({row for row, _, _ in found})
    print(f"rule {args.rule}: {len(found)} (row, column, period) triples survive {args.steps} steps among the "
          f"{(1 << args.cells) - 1} nonzero rows with black cells in cells 0 .. {args.cells - 1}, columns within "
          f"{args.max_period} of them, periods up to {args.max_period}; {len(rows)} rows")
    for row, column, period in found[:10]:
        print(f"  row {format(row, f'0{args.cells}b')[::-1]} (cell 0 first), column {column}, period {period}")
    if witness is not None and not found:
        row, column, period = witness
        print(f"  longest repetition: {longest} checked times, row {format(row, f'0{args.cells}b')[::-1]} (cell 0 "
              f"first), column {column}, period {period}")
    print(f"({time.perf_counter() - started:.0f} s)")


if __name__ == "__main__":
    main()
