"""Tests of computations.coupled: Psi against whole rows stepped with the rule and against the rebuild of `held_map`."""

from __future__ import annotations

import numpy as np

from computations import absorption, coupled, held_map
from computations.rule30 import spacetime


def test_coupled_exact_death() -> None:
    """Psi against stepping whole rows: a left half equal to Psi(R) at depths 1 .. W and white beyond keeps the center
    on the word exactly until the first black depth of Psi(R) past W, for random words, phases, right halves and
    widths."""
    rng = np.random.default_rng(11)
    steps = 120
    for _ in range(40):
        word = coupled.WORDS[int(rng.integers(len(coupled.WORDS)))]
        phase, right, width = int(rng.integers(len(word))), int(rng.integers(1 << 10)), int(rng.integers(1, 60))
        row = coupled.psi(word, phase, right, steps)
        death = next(j for j in range(width, steps) if (row >> j) & 1) + 1
        middle = width + steps
        cells = np.zeros(middle + steps + 12, dtype=bool)  # (n,), the center at index `middle`
        cells[middle - width:middle] = [(row >> j) & 1 for j in reversed(range(width))]
        cells[middle] = word[phase] == "1"
        cells[middle + 1:middle + 11] = [(right >> i) & 1 for i in range(10)]
        column = spacetime(cells, death)[:, middle]  # (death + 1,)
        want = [int(word[(t + phase) % len(word)]) for t in range(death + 1)]
        assert column[:death].tolist() == want[:death] and column[death] != want[death]


def test_coupled_rebuilds() -> None:
    """Psi of the empty right half against the antidiagonal rebuild of `held_map` with the center as the boundary, and
    for 0011 at phase 2 against the left half of the kit's ether, which it equals from depth 1."""
    c, column = coupled.center("01", 1, 301), coupled.drive_column("01", 1, 0, 301)
    rebuilt, a1, a2 = 0, 0, 0
    for m in range(300):
        reading = ((c >> (m + 1)) ^ ((c >> m) | (column >> m))) & 1  # column -1 at time m, forced
        d = a1 | a2 | ((((c >> (m - 1)) & 1) << (m - 1)) if m else 0)
        bit = reading ^ ((d & ((1 << m) - 1)).bit_count() & 1)
        a1, a2 = held_map.next_diagonal(bit, d, m), a1
        rebuilt |= bit << m
    assert rebuilt == coupled.psi("01", 1, 0, 300)
    ether_left = sum(int(absorption.ETHER[-k % 7][2]) << (k - 1) for k in range(1, 701))
    assert coupled.psi("0011", 2, 0, 700) == ether_left
    assert coupled.ether_after("10001010111100") == 4 and coupled.ether_after("0010011") == 0
