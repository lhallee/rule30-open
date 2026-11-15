"""Tests of computations.cyclic_words: the least rotation and the least periods against definitions written out here,
on every binary word of up to 12 letters and on random arrays."""

from __future__ import annotations

import itertools
import numpy as np
import pytest

from computations.cyclic_words import least_array_period, least_period, least_rotation


WORDS = ["".join(letters) for n in range(1, 13) for letters in itertools.product("01", repeat=n)]


def rotations(word: str) -> list[str]:
    """Every rotation of `word`, letter by letter: rotation r moves the first r letters to the end."""
    out = []
    current = word
    for _ in range(len(word)):
        out.append(current)
        current = current[1:] + current[0]
    return out


def period_by_shifts(letters: list[int]) -> int:
    """The least p > 0 with letter (t + p) mod n equal to letter t for every t, tried p by p without assuming that p
    divides n."""
    n = len(letters)
    return next(p for p in range(1, n + 1) if all(letters[(t + p) % n] == letters[t] for t in range(n)))


def test_least_rotation() -> None:
    """The least rotation is the least of the rotations, and every rotation has the same one."""
    for word in WORDS:
        least = least_rotation(word)
        assert least == sorted(rotations(word))[0]
        assert all(least_rotation(rotation) == least for rotation in rotations(word))
    assert least_rotation("0110100") == "0001101" and least_rotation("cab") == "abc"


def test_least_period() -> None:
    """The least period of a string against shifts tried one at a time, which divides the length, and the number of
    distinct rotations equals it."""
    for word in WORDS:
        p = least_period(word)
        assert p == period_by_shifts([int(c) for c in word]) == len(set(rotations(word)))
        assert len(word) % p == 0 and word == word[:p] * (len(word) // p)
    assert least_period("abcabc") == 3 and least_period("aaaa") == 1 and least_period("abab" + "a") == 5
    with pytest.raises(AssertionError, match="no period"):
        least_period("")


def test_least_array_period() -> None:
    """The least period of an array against shifts tried one at a time, on binary words and on random arrays of
    several values built from a repeated block."""
    for word in WORDS[:2046]:  # every word of up to 10 letters
        column = np.array([int(c) for c in word], dtype=np.uint8)  # (n,)
        assert least_array_period(column) == period_by_shifts(column.tolist()) == least_period(word)
    rng = np.random.default_rng(0)
    for _ in range(200):
        block = rng.integers(0, 3, int(rng.integers(1, 8)))  # (b,)
        column = np.tile(block, int(rng.integers(1, 5)))  # (n,)
        assert least_array_period(column) == period_by_shifts(column.tolist())
