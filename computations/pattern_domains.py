"""Periodic domains in the single black cell's pattern: where a wall between two phases of a background could sit.

A background of Rule 30 that recurs, F^k x = sigma^d x with 1 - k <= d <= k, is periodic in space (the kit's
`Rule30Equivalents.PeriodicPoints`, `recurs_add_factorial`), so every row of a domain of such a background, the ether
among them, repeats with the background's spatial period. A *domain block* is a block of `side` x `side` cells, rows
t - side + 1 .. t and cells x .. x + side - 1, in which every row repeats with one spatial period p <= `max_period`
across the block: cell y equals cell y + p for x <= y < x + side - p. `domain_census` counts the domain blocks inside
the light cone of the single cell, by half and by period, streaming the rows; `random_census` does the same for a
random row run with white beyond its ends, on the cells that the ends have not reached.

    python -m computations.pattern_domains --steps 8192 --side 24 --max-period 16   # none, about 30 s
    python -m computations.pattern_domains --steps 8192 --side 16 --max-period 8    # 9 block starts, at one place
    python -m computations.pattern_domains --steps 4096 --side 12 --max-period 7    # 244 block starts, 186 by the right edge
"""

from __future__ import annotations

import argparse
import time

from collections.abc import Iterator

import numpy as np

from tqdm.auto import tqdm


def step_row(row: np.ndarray) -> np.ndarray:
    """One step of Rule 30 on a row, white beyond its ends."""
    # row: (n,)
    left = np.concatenate([[False], row[:-1]])  # (n,)
    right = np.concatenate([row[1:], [False]])  # (n,)
    return left ^ (row | right)  # (n,)


def periodic_segments(row: np.ndarray, side: int, max_period: int) -> np.ndarray:
    """Entry [p - 1, x] is True when cells x .. x + side - 1 of `row` repeat with period p (False past the end)."""
    # row: (n,)
    n = row.size
    out = np.zeros((max_period, n), dtype=bool)  # (max_period, n)
    for p in range(1, max_period + 1):
        equal = np.zeros(n, dtype=np.int64)  # (n,), cell y equals cell y + p
        equal[: n - p] = row[: n - p] == row[p:]
        prefix = np.concatenate([[0], np.cumsum(equal)])  # (n + 1,)
        span = side - p
        starts = n - side + 1
        if starts > 0:
            out[p - 1, :starts] = (prefix[span: span + starts] - prefix[:starts]) == span
    return out


def stream(row: np.ndarray, steps: int, side: int, max_period: int,
           desc: str) -> Iterator[tuple[int, np.ndarray, np.ndarray]]:
    """Yield (t, row, blocks) for t = 0 .. steps - 1, blocks[p - 1, x] True when the domain block of rows t - side + 1 ..
    t at cell x has period p (all False for t < side - 1)."""
    # row: (n,)
    history: list[np.ndarray] = []  # each (max_period, n)
    for t in tqdm(range(steps), desc=desc, mininterval=5.0, leave=False):
        history.append(periodic_segments(row, side, max_period))
        if len(history) > side:
            history.pop(0)
        blocks = np.logical_and.reduce(history) if len(history) == side else np.zeros_like(history[0])
        yield t, row, blocks  # (n,), (max_period, n)
        row = step_row(row)


def domain_census(steps: int, side: int, max_period: int) -> dict[str, object]:
    """Domain blocks of the single cell's rows 0 .. steps - 1 whose cells all lie in the light cone of their first row.
    Positions are cells relative to the center column; a block is in the left half when all its cells are left of the
    column, in the right half when all are right of it."""
    margin = side
    width = 2 * steps + 1 + 2 * margin
    center = steps + margin
    row = np.zeros(width, dtype=bool)  # (width,)
    row[center] = True
    left = right = left_cells = right_cells = 0
    by_period = np.zeros(max_period, dtype=np.int64)  # (max_period,)
    found: list[tuple[int, int, int]] = []  # (t, x, p) of each block start
    for t, _, blocks in stream(row, steps, side, max_period, "single cell"):
        if t < side - 1:
            continue
        first = t - side + 1  # the block's first row; its light cone is cells -first .. first
        lo, hi = center - first, center + first - side + 1  # block starts whose cells all lie in that cone
        if hi < lo:
            continue
        starts = np.arange(lo, hi + 1) - center  # (k,)
        window = blocks[:, lo: hi + 1]  # (max_period, k)
        any_period = window.any(0)  # (k,)
        left_mask, right_mask = starts + side <= 0, starts > 0  # (k,), (k,)
        left += int((any_period & left_mask).sum())
        right += int((any_period & right_mask).sum())
        left_cells += int(left_mask.sum())
        right_cells += int(right_mask.sum())
        by_period += window.sum(1)
        for p, x in zip(*np.nonzero(window)):
            found.append((t, int(starts[x]), int(p) + 1))
    return {"left": left, "right": right, "left_starts": left_cells, "right_starts": right_cells,
            "by_period": by_period.tolist(), "blocks": found}


def random_census(steps: int, side: int, max_period: int, width: int, seed: int = 0) -> dict[str, object]:
    """Domain blocks of a random row of `width` cells, white beyond its ends, over rows 0 .. steps - 1, on the cells
    that are exact (the ends reach one cell further in per step) and more than `side` cells from them."""
    row = np.random.default_rng(seed).integers(0, 2, width).astype(bool)  # (width,)
    count = cells = 0
    by_period = np.zeros(max_period, dtype=np.int64)  # (max_period,)
    for t, _, blocks in stream(row, steps, side, max_period, "random row"):
        if t < side - 1:
            continue
        lo, hi = t + side, width - t - 2 * side
        if hi <= lo:
            break
        window = blocks[:, lo:hi]  # (max_period, k)
        count += int(window.any(0).sum())
        cells += hi - lo
        by_period += window.sum(1)
    return {"blocks": count, "starts": cells, "by_period": by_period.tolist()}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--steps", type=int, default=8192)
    parser.add_argument("--side", type=int, default=24)
    parser.add_argument("--max-period", type=int, default=16)
    args = parser.parse_args()
    start = time.time()
    single = domain_census(args.steps, args.side, args.max_period)
    print(f"single cell, rows 0 .. {args.steps - 1}, blocks of {args.side} x {args.side}, periods 1 .. "
          f"{args.max_period}: left half {single['left']} of {single['left_starts']} block starts, right half "
          f"{single['right']} of {single['right_starts']}; by period {single['by_period']}")
    starts = sorted({(t, x) for t, x, _ in single["blocks"]})
    right_gaps = np.array([t - (x + args.side - 1) for t, x in starts if x > 0])  # (r,), cells to the right edge
    left_gaps = np.array([x + t for t, x in starts if x + args.side <= 0])  # (l,), cells to the left edge
    for name, gaps in (("right", right_gaps), ("left", left_gaps)):
        if gaps.size:
            print(f"  {name} half: {gaps.size} block starts; distance "
                  f"of the block from the {name} edge in its last row: under 64 for {(gaps < 64).sum()}, 64 to 511 "
                  f"for {((gaps >= 64) & (gaps < 512)).sum()}, 512 or more for {(gaps >= 512).sum()}")
    near = sorted({t % 256 for t, x in starts if x > 0 and t - (x + args.side - 1) < 64})
    if near:
        print(f"  right-half block starts within 64 cells of the right edge come at times t with t mod 256 in {near}")
    control = random_census(args.steps // 4, args.side, args.max_period, 2 * args.steps + 1)
    print(f"random row of {2 * args.steps + 1} cells, rows 0 .. {args.steps // 4 - 1}: {control['blocks']} of "
          f"{control['starts']} block starts; by period {control['by_period']}")
    print(f"{time.time() - start:.0f} s")


if __name__ == "__main__":
    main()
