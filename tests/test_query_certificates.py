"""Sensitivity, certificate complexity and fixed answers of the cone function, against plain recursions."""

from __future__ import annotations

import itertools
from functools import lru_cache

import numpy as np

from computations import query_certificates as qc
from computations.query_depth import exact_depth
from computations.rule30 import step


def direct_table(t: int) -> np.ndarray:
    """c_t for every cone row by stepping the row as an integer with `step`; bit i of the index is x_{-t+i}."""
    n = 2 * t + 1
    origin = t + 1  # bit of cell -t; white cells pad both sides
    table = np.zeros(1 << n, dtype=np.uint8)  # (2^n,)
    for index in range(1 << n):
        row = index << origin
        for _ in range(t):
            row = step(row)
        table[index] = (row >> (origin + t)) & 1
    return table  # (2^n,)


def brute_certificate(table: np.ndarray, n: int) -> int:
    """max over rows of the least |S| such that fixing the cells of S to the row makes the function constant, by
    grouping the rows on their values in S for every S."""
    index = np.arange(1 << n)  # (2^n,)
    best = np.full(1 << n, n, dtype=np.int64)  # (2^n,)
    for subset in range(1 << n):
        key = index & subset  # (2^n,)
        ones = np.bincount(key, weights=table, minlength=1 << n)  # (2^n,)
        total = np.bincount(key, minlength=1 << n)  # (2^n,)
        constant = (ones[key] == 0) | (ones[key] == total[key])  # (2^n,)
        best = np.where(constant, np.minimum(best, bin(subset).count("1")), best)
    return int(best.max())


def brute_fixed_answer(table: np.ndarray, n: int, variable: int, answer: int) -> bool:
    """The adversary game by plain recursion over partial assignments: the adversary must answer `variable` with
    `answer`, and wins when the function is not constant on the last free variable."""

    @lru_cache(maxsize=None)
    def wins(partial: tuple[int | None, ...]) -> bool:
        free = [i for i, v in enumerate(partial) if v is None]
        values = set()
        for bits in itertools.product((0, 1), repeat=len(free)):
            full = list(partial)
            for i, b in zip(free, bits):
                full[i] = b
            values.add(int(table[sum(b << i for i, b in enumerate(full))]))
        if len(values) == 1:
            return False
        if len(free) == 1:
            return True
        for i in free:
            options = [answer] if i == variable else [0, 1]
            if not any(wins(partial[:i] + (b,) + partial[i + 1:]) for b in options):
                return False
        return True

    return wins((None,) * n)


def test_sensitivity_profile_against_direct_runs() -> None:
    for t in range(1, 4):
        n = 2 * t + 1
        table = direct_table(t)  # (2^n,)
        flips = [[int(table[r] != table[r ^ (1 << i)]) for i in range(n)] for r in range(1 << n)]
        expected = (max(sum(f) for f in flips), sum(all(f[n - 3:]) for f in flips), sum(all(f[: n - 2]) for f in flips))
        assert qc.sensitivity_profile(t) == expected


def test_right_corner_has_no_sensitive_row() -> None:
    # Lean `right_corner`: for t >= 2 no row is sensitive to all three rightmost cells
    assert [qc.sensitivity_profile(t)[1] for t in range(2, 7)] == [0, 0, 0, 0, 0]
    assert qc.sensitivity_profile(1)[1] == 2


def test_certificate_complexity_against_subsets() -> None:
    for t in range(1, 4):
        n = 2 * t + 1
        table = direct_table(t)
        assert qc.certificate_complexity(table, n) == brute_certificate(table, n)
    assert [qc.certificate_complexity(direct_table(t), 2 * t + 1) for t in range(1, 4)] == [3, 4, 6]


def test_certificate_complexity_quoted_values() -> None:
    from computations.cone_screening import cone_table

    values = [qc.certificate_complexity(cone_table(t), 2 * t + 1) for t in range(1, 6)]
    assert values == [3, 4, 6, 7, 10]
    assert all(c <= 2 * t for t, c in zip(range(2, 6), values[1:]))


def test_evasive_against_exact_depth() -> None:
    rng = np.random.default_rng(0)
    for n in range(1, 5):
        for _ in range(20):
            table = rng.integers(0, 2, 1 << n).astype(np.uint8)  # (2^n,)
            assert qc.evasive(table, n) == (exact_depth(table, n) == n)


def test_fixed_answers_against_recursion() -> None:
    for t in (1, 2):
        n = 2 * t + 1
        table = direct_table(t)
        expected = {j: [b for b in (0, 1) if brute_fixed_answer(table, n, j + t, b)] for j in range(-t, t + 1)}
        assert qc.fixed_answer_cells(t) == expected
    cells = qc.fixed_answer_cells(3)
    assert cells[2] == [] and cells[3] == [] and cells[-3] == [0, 1]


def test_one_step_against_direct_composition() -> None:
    rng = np.random.default_rng(1)
    for m in (1, 2, 3):
        table = rng.integers(0, 2, 1 << m).astype(np.uint8)  # (2^m,)
        lifted = qc.one_step(table, m)  # (2^(m+2),)
        for index in range(1 << (m + 2)):
            x = [(index >> i) & 1 for i in range(m + 2)]
            y = sum((x[j] ^ (x[j + 1] | x[j + 2])) << j for j in range(m))
            assert lifted[index] == table[y]


def test_lift_failures_quoted() -> None:
    total = sum(exact_depth(np.array([(c >> b) & 1 for b in range(8)], dtype=np.uint8), 3) == 3 for c in range(256))
    assert qc.lift_failures(3) == (total, 24)
    assert total == 194
