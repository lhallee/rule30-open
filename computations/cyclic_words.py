"""Words read cyclically: the least rotation and the least period.

A cyclic word follows its last letter with its first. Its least rotation, the least of its rotations in lexicographic
order, names its necklace; its least period is the least p with letter t + p equal to letter t for every t, taken
around the circle, and divides its length. `least_period` reads a string, `least_array_period` a one-dimensional
array.
"""

from __future__ import annotations

import numpy as np


def least_rotation(word: str) -> str:
    """The least rotation of `word`."""
    return min(word[i:] + word[:i] for i in range(len(word)))


def least_period(word: str) -> int:
    """The least period of a nonempty word read cyclically."""
    assert word, "the empty word has no period"
    return (word + word).find(word, 1)  # the least rotation that gives the word back, which divides its length


def least_array_period(column: np.ndarray) -> int:
    """The least p dividing the length with column(t + p) = column(t) for every t, read cyclically."""
    # column: (n,)
    n = column.size
    return next(p for p in range(1, n + 1) if n % p == 0 and np.array_equal(column, np.roll(column, p)))
