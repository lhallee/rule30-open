"""Ordered decision diagrams of the center column in every variable order.

Read c(n) as a Boolean function of the ell binary digits of n < 2^ell (variable i is bit i). An ordered binary decision
diagram that reads the variables in the order p has, for every j, at least as many nodes as the function has distinct
subfunctions after the first j variables of p are fixed: each subfunction is reached through an edge across that level.
So the size of every diagram, in every order, is at least min over orders of max over j of that count, which a dynamic
program over subsets of variables finds exactly: best[S] = min over x in S of max(best[S - x], count(S)).

    python -m computations.obdd_orders 16        # the center column, random bits and Thue-Morse on 16 digits
"""

from __future__ import annotations

import argparse
import sys

import numpy as np

from tqdm.auto import tqdm

from computations.crossing_bounds import random_cells, thue_morse
from computations.rule30 import center_column


def deposit_table(positions: list[int]) -> np.ndarray:
    """For k = len(positions): the 2^k integers whose bit i is bit positions[i] of the value i-th digit pattern."""
    table = np.zeros(1, dtype=np.int64)  # (1,)
    for position in positions:
        table = np.concatenate([table, table | (1 << position)])  # (2 * previous,)
    return table  # (2^k,)


def subfunction_count(cells: np.ndarray, ell: int, first: int) -> int:
    """The number of distinct functions of the other variables that arise when the variables in the bit mask `first` are
    fixed to each of their values."""
    # cells: (2^ell,)
    inside = [i for i in range(ell) if (first >> i) & 1]
    outside = [i for i in range(ell) if not (first >> i) & 1]
    rows = deposit_table(inside)  # (2^j,)
    cols = deposit_table(outside)  # (2^(ell-j),)
    matrix = cells[rows[:, None] | cols[None, :]]  # (2^j, 2^(ell-j))
    packed = np.ascontiguousarray(np.packbits(matrix.astype(np.uint8), axis=1))  # (2^j, ceil(2^(ell-j) / 8))
    keyed = packed.view(np.dtype((np.void, packed.shape[1]))).ravel()  # (2^j,)
    return len(np.unique(keyed))


def all_counts(cells: np.ndarray, ell: int, progress: bool = False) -> np.ndarray:
    """`subfunction_count` for every set of variables."""
    # cells: (2^ell,)
    counts = np.zeros(1 << ell, dtype=np.int64)  # (2^ell,)
    for first in tqdm(range(1 << ell), desc="variable sets", file=sys.stderr, disable=not progress):
        counts[first] = subfunction_count(cells, ell, first)
    return counts  # (2^ell,)


def least_width(counts: np.ndarray, ell: int) -> int:
    """Over all orders of the variables, the least largest count along the order: a lower bound on the size of an
    ordered decision diagram in every order."""
    # counts: (2^ell,)
    best = np.zeros(1 << ell, dtype=np.int64)  # (2^ell,)
    best[0] = 1
    for mask in range(1, 1 << ell):
        options = [max(int(best[mask & ~(1 << x)]), int(counts[mask])) for x in range(ell) if (mask >> x) & 1]
        best[mask] = min(options)
    return int(best[(1 << ell) - 1])


def least_width_in_order(counts: np.ndarray, order: list[int]) -> int:
    """The largest count along one order of the variables."""
    mask, widest = 0, 1
    for variable in order:
        mask |= 1 << variable
        widest = max(widest, int(counts[mask]))
    return widest


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("ell", type=int)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    size = 1 << args.ell
    ensembles = {"center column": center_column(size), "random bits": random_cells(size, args.seed),
                 "Thue-Morse": thue_morse(size)}  # each (2^ell,)
    for name, cells in ensembles.items():
        counts = all_counts(cells, args.ell, progress=True)  # (2^ell,)
        low_first = least_width_in_order(counts, list(range(args.ell)))
        high_first = least_width_in_order(counts, list(range(args.ell - 1, -1, -1)))
        print(f"{name:14s} least width over all orders {least_width(counts, args.ell):6d}   "
              f"low digits first {low_first:6d}   high digits first {high_first:6d}")


if __name__ == "__main__":
    main()
