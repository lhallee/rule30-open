"""The subfunction counts and the dynamic program over orders against direct enumeration."""

from __future__ import annotations

import itertools

import numpy as np

from computations import crossing_bounds, obdd_orders
from computations.rule30 import center_column


def direct_count(cells: np.ndarray, ell: int, first: list[int]) -> int:
    """Distinct subfunctions by enumerating every assignment as a tuple."""
    rest = [i for i in range(ell) if i not in first]
    seen = set()
    for assignment in itertools.product([0, 1], repeat=len(first)):
        row = []
        for other in itertools.product([0, 1], repeat=len(rest)):
            n = sum(bit << i for bit, i in zip(assignment, first)) + sum(bit << i for bit, i in zip(other, rest))
            row.append(int(cells[n]))
        seen.add(tuple(row))
    return len(seen)


def test_counts_and_orders() -> None:
    """Counts against enumeration for every set of 6 variables, and the least width against all 720 orders."""
    ell = 6
    cells = center_column(1 << ell)  # (64,)
    counts = obdd_orders.all_counts(cells, ell)  # (64,)
    for first in range(1 << ell):
        assert counts[first] == direct_count(cells, ell, [i for i in range(ell) if (first >> i) & 1])
    brute = min(obdd_orders.least_width_in_order(counts, list(order)) for order in itertools.permutations(range(ell)))
    assert obdd_orders.least_width(counts, ell) == brute


def test_controls() -> None:
    """Thue-Morse is a parity, so every order gives width 2; random bits on 8 variables are far from that."""
    ell = 8
    parity = obdd_orders.all_counts(crossing_bounds.thue_morse(1 << ell), ell)  # (256,)
    assert obdd_orders.least_width(parity, ell) == 2
    noise = obdd_orders.all_counts(crossing_bounds.random_cells(1 << ell, 3), ell)  # (256,)
    assert obdd_orders.least_width(noise, ell) >= 8
