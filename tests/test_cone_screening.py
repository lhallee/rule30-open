"""The cone screening: constant centers for alternating left halves, the pair lemmas, and the subfunction counts."""

from __future__ import annotations

import itertools
from collections.abc import Iterator

import numpy as np
import pytest

from computations import cone_screening as cs
from computations import obdd_orders


def plain_center(cells: list[int]) -> int:
    """c_t from the 2t + 1 cone cells x_{-t} .. x_t by running the rule on a list, one cell at a time."""
    row = list(cells)  # (2t + 1,)
    while len(row) > 1:
        row = [row[i - 1] ^ (row[i] | row[i + 1]) for i in range(1, len(row) - 1)]  # (len - 2,)
    return row[0]


def plain_pattern_center(t: int, odd: bool, right: int) -> int:
    """c_t for the pattern on the left half and the right half x_i = bit i of `right`, by `plain_center`."""
    left = [int(v) for v in cs.left_pattern(t, odd)]  # (t,)
    return plain_center(left + [(right >> i) & 1 for i in range(t + 1)])


@pytest.fixture(scope="module")
def table9() -> np.ndarray:
    return cs.cone_table(9)  # (2^19,)


def test_left_pattern() -> None:
    """The even pattern has x_{-j} = 1 for the even j only, the odd pattern for the odd j only; x_{-1} is the last."""
    assert cs.left_pattern(4, False) == [True, False, True, False]  # x_{-4} .. x_{-1}
    assert cs.left_pattern(5, True) == [True, False, True, False, True]


def test_cone_table_against_plain_run() -> None:
    """Every entry of the bit-sliced table is the center of a run of the rule on a list, for t = 3 and 4."""
    for t in (3, 4):
        table = cs.cone_table(t)  # (2^(2t+1),)
        for index in range(1 << (2 * t + 1)):
            assert table[index] == plain_center([(index >> i) & 1 for i in range(2 * t + 1)])


def test_constant_centers_against_plain_run() -> None:
    """Even pattern: c_t = 1 for t >= 8 and not before. Odd pattern: c_t = 0 for t >= 9 and not before. All right halves
    from the bit-sliced run, and a sample of them from the plain run."""
    rng = np.random.default_rng(0)
    assert cs.constant_value(cs.pattern_values(7, False)) is None
    assert cs.constant_value(cs.pattern_values(8, True)) is None
    for t in range(8, 13):
        even, odd = cs.pattern_values(t, False), cs.pattern_values(t, True)  # each (2^(t+1),)
        assert cs.constant_value(even) == 1
        assert cs.constant_value(odd) == (None if t < 9 else 0)
        for right in rng.integers(0, 1 << (t + 1), 12).tolist() + [0, (1 << (t + 1)) - 1]:
            assert plain_pattern_center(t, False, right) == even[right] == 1
            if t >= 9:
                assert plain_pattern_center(t, True, right) == odd[right] == 0


def test_pattern_values_are_a_slice_of_the_cone_table() -> None:
    """The left word is the lowest t bits of the cone index and the right half the highest t + 1."""
    t = 5
    table = cs.cone_table(t)  # (2^11,)
    for odd in (False, True):
        word = sum(int(v) << i for i, v in enumerate(cs.left_pattern(t, odd)))
        assert np.array_equal(table[word + (np.arange(1 << (t + 1)) << t)], cs.pattern_values(t, odd))


def test_pair_step_and_lemmas() -> None:
    """The pair map on its cases, the local facts of the argument, and the pair model against a plain run."""
    assert cs.pair_step((0, 0), 0) == (1, 0) and cs.pair_step((0, 0), 1) == (1, 1)
    assert cs.pair_step((1, 0), 0) == (0, 1) and cs.pair_step((0, 1), 0) == (0, 1)
    counts = cs.check_pair_lemmas()
    assert counts["zero_zero_from_a"] == counts["zero_zero_two_back"] == 3 and counts["b_zero_cases"] == 4
    cs.check_pair_model(4, 20)


def trajectories(horizon: int) -> Iterator[list]:
    """Every pair trajectory p_0 .. p_horizon for every initial pair and every sequence of third cells, in the order of
    the sequences, the paths that share a prefix of third cells sharing its steps."""
    def extend(path: list) -> Iterator[list]:
        if len(path) > horizon:
            yield path
            return
        for third in (0, 1):
            yield from extend(path + [cs.pair_step(path[-1], third)])

    for start in itertools.product((0, 1), repeat=2):
        yield from extend([start])


def test_pair_induction_from_the_base_values() -> None:
    """The induction, exhausted up to time 13 over all initial pairs and third cells. Odd pattern (c_t = a(t)): a pair
    (0, 0) at neither 8 nor 9 means none at any time from 8 on, so a(t) = [(0, 0) at t - 1] = 0 for t >= 9. Even
    pattern (c_t = b(t)): b = 1 at 8 and 9 means b = 1 at every later time."""
    for path in trajectories(13):
        if path[8] != (0, 0) and path[9] != (0, 0):
            assert all(p != (0, 0) for p in path[8:])
            assert all(path[s][0] == int(path[s - 1] == (0, 0)) for s in range(1, 14))
        if path[8][1] == 1 and path[9][1] == 1:
            assert all(p[1] == 1 for p in path[8:])


def test_subfunction_counts_against_brute_force(table9: np.ndarray) -> None:
    """Counts of the distinct columns and rows of the table by a set of byte strings, at t = 9, and against the diagram
    width of `obdd_orders` at t = 6."""
    n = 19
    for k in (8, 9, 10):
        left = {bytes(table9.reshape(1 << (n - k), 1 << k)[:, low]) for low in range(1 << k)}
        right = {bytes(table9.reshape(1 << k, 1 << (n - k))[high]) for high in range(1 << k)}
        assert cs.left_count(table9, n, k) == len(left)
        assert cs.right_count(table9, n, k) == len(right)
    assert cs.left_count(table9, n, 9) == 506 and cs.left_count(table9, n, 8) == 256
    table6 = cs.cone_table(6)  # (2^13,)
    for k in (3, 6, 7):
        assert cs.left_count(table6, 13, k) == obdd_orders.subfunction_count(table6, 13, (1 << k) - 1)
        assert cs.right_count(table6, 13, k) == obdd_orders.subfunction_count(table6, 13, ((1 << k) - 1) << (13 - k))


def test_left_half_is_not_incompressible(table9: np.ndarray) -> None:
    """The leftmost cell enters additively, the four screened words share two subfunctions, and the count of the left
    half is at most 2^t - 2 at t = 9 (it is 506)."""
    t, n = 9, 19
    assert cs.flip_leftmost_flips_center(t, table9)
    columns = table9.reshape(1 << (n - t), 1 << t).T  # (2^t, 2^(t+1)), row = left word
    groups = cs.screened_words(t)
    assert len(set(groups[1] + groups[0])) == 4
    for value, words in groups.items():
        for word in words:
            assert np.all(columns[word] == value)
    assert cs.left_count(table9, n, t) <= 2**t - 2
    assert [cs.left_count(table9, n, k) for k in range(1, t)] == [2**k for k in range(1, t)]


def test_counts_before_the_threshold() -> None:
    """The left half still has 2^t subfunctions for t = 7 and 8, and the right counts of t = 7 start as at t = 10."""
    for t in (7, 8):
        table = cs.cone_table(t)  # (2^(2t+1),)
        assert cs.left_count(table, 2 * t + 1, t) == 2**t
    assert cs.right_counts(7)[:9] == [2, 2, 4, 5, 9, 12, 20, 26, 42]
