"""Tests for computations/restricted_models.py, each against an independent computation."""

from __future__ import annotations

import itertools

import numpy as np

from computations.restricted_models import (
    certificate_cells,
    certificate_lower_bound,
    dyadic_witnesses,
    first_strip_error,
    is_certificate,
    lazy_certificate,
    min_certificate,
    min_certificate_set,
    ray_flip_depths,
    rule90_certificate_size,
    spacetime_cone,
    strip_center,
    true_center,
)
from computations.rule30 import center_column


def _strip_by_dict(rule: int, left: int, right: int, steps: int) -> list[int]:
    """The strip evolution cell by cell from the rule number, on a dictionary (independent of the array code)."""
    row = {j: int(j == 0) for j in range(-left, right + 1)}
    out = [1]
    for _ in range(steps):
        get = lambda j: row.get(j, 0)
        row = {j: (rule >> (4 * get(j - 1) + 2 * get(j) + get(j + 1))) & 1 for j in range(-left, right + 1)}
        out.append(row[0])
    return out


def test_true_center_matches_integer_rows() -> None:
    assert np.array_equal(true_center(30, 199), center_column(200))


def test_strip_matches_dictionary_evolution() -> None:
    for rule, left, right in [(30, 3, 5), (30, 6, 2), (90, 4, 4), (150, 2, 7)]:
        assert list(strip_center(rule, left, right, 25)) == _strip_by_dict(rule, left, right, 25)


def test_strip_first_error_is_two_w_plus_two() -> None:
    truth = {rule: true_center(rule, 70) for rule in (30, 90, 150)}  # (71,) each
    for rule in (30, 90, 150):
        for w in range(30):
            assert first_strip_error(rule, w, w + 1, 70, truth[rule]) == 2 * w + 2
            assert first_strip_error(rule, w, 70, 70, truth[rule]) == 2 * w + 2


def test_right_strip_respects_light_cone() -> None:
    truth = true_center(30, 300)  # (301,)
    for wr in range(0, 25):
        assert first_strip_error(30, 300, wr, 300, truth) >= 2 * wr + 2


def _min_by_choices(n: int) -> int:
    """Least closure of (n, 0) over every choice of one black parent where both or-parents are black: a minimal
    certificate is such a closure, so this is the minimum, found without integer programming."""
    x = spacetime_cone(30, n)  # (n + 1, 2n + 1)
    value = lambda s, j: int(x[s, j + n]) if abs(j) <= s else 0
    choice_cells = [
        (s, j) for (s, j) in certificate_cells(n) if s >= 2 and value(s - 1, j) == 1 and value(s - 1, j + 1) == 1
    ]
    best = None
    for bits in itertools.product((0, 1), repeat=len(choice_cells)):
        pick = dict(zip(choice_cells, bits))
        seen: set[tuple[int, int]] = set()
        stack = [(n, 0)]
        while stack:
            s, j = stack.pop()
            if (s, j) in seen or s == 0 or abs(j) > s:
                continue
            seen.add((s, j))
            stack.append((s - 1, j - 1))
            if (s, j) in pick:
                stack.append((s - 1, j + pick[(s, j)]))
            elif value(s - 1, j) == 1:
                stack.append((s - 1, j))
            elif value(s - 1, j + 1) == 1:
                stack.append((s - 1, j + 1))
            else:
                stack.extend([(s - 1, j), (s - 1, j + 1)])
        best = len(seen) if best is None else min(best, len(seen))
    return best


def test_certificates_are_valid_and_minimum_matches_exhaustive_search() -> None:
    for n in range(1, 4):
        cells = certificate_cells(n)
        brute = next(
            size for size in range(1, len(cells) + 1)
            if any(is_certificate(n, set(c)) for c in itertools.combinations(cells, size))
        )
        assert brute == min_certificate(n)
    for n in range(4, 10):  # n <= 9, as the restricted-models entry states
        assert _min_by_choices(n) == min_certificate(n)
    for n in (8, 15, 22):
        assert is_certificate(n, lazy_certificate(n))
        assert is_certificate(n, min_certificate_set(n))
        assert certificate_lower_bound(n) <= min_certificate(n) <= len(lazy_certificate(n))


def test_rule90_closure_is_forced() -> None:
    for n in (6, 11, 16):
        closure = lazy_certificate(n, 90)
        assert is_certificate(n, closure, 90)
        assert len(closure) == rule90_certificate_size(n) == min_certificate(n, 90)
        for cell in closure:
            assert not is_certificate(n, closure - {cell}, 90)


def test_dyadic_witnesses_against_direct_scan() -> None:
    column = center_column(2**9 + 2**10 + 64)  # (1600,)
    for k, offset in dyadic_witnesses(10, column):
        low, period = 2 ** (k - 1), 2**k
        m = low + offset
        assert column[m] != column[m + period]
        assert all(column[i] == column[i + period] for i in range(low, m))


def test_ray_flips_against_direct_scan() -> None:
    column = center_column(3000)  # (3000,)
    for k, flipping, deepest in ray_flip_depths(8, column):
        low, period = 2 ** (k - 1), 2**k
        count, worst = 0, -1
        for r in range(period):
            ray = [int(column[m]) for m in range(low + r, len(column), period)]
            ray = ray[: (len(column) - low) // period]
            flips = [i for i, v in enumerate(ray) if v != ray[0]]
            if flips:
                count += 1
                worst = max(worst, flips[0])
        assert (flipping, deepest) == (count, worst)
