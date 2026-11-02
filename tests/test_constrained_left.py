"""The constrained left-half search against cell-by-cell runs, and the sideways columns against forward runs."""

from __future__ import annotations

import math

import numpy as np

from computations.constrained_left import (CONDITIONS, column_anf, columns_from, count_words, entropy, forced_cells,
                                           periodic_half, tree_failures)


def naive_step(cells: list[int], boundary: int) -> list[int]:
    """One step of the left half, cell by cell: cells[j] is cell -1 - j, the center replaced by `boundary`, white
    beyond the list, which grows by one cell."""
    ext = cells + [0, 0]
    new = []
    for j in range(len(cells) + 1):
        right = boundary if j == 0 else ext[j - 1]
        new.append(ext[j + 1] ^ (ext[j] | right))
    return new


def naive_first_failure(name: str, half: int, phase: int, limit: int) -> int:
    """The first step at which column -1 leaves the pattern or the readings, as a string, contain a word."""
    cond = CONDITIONS[name]
    block, period = cond.block, len(cond.block)
    boundary = [int(block[t] == "1" and block[(t + 1) % period] == "1") for t in range(period)]
    cells = [(half >> j) & 1 for j in range(max(half.bit_length(), 1))]
    text = ""
    for t in range(limit):
        p = (t + phase) % period
        after = int(block[(p + 1) % period])
        value = cells[0]
        if block[p] == "1":
            if value == after:
                return t
        else:
            reading = value ^ after
            if dict(cond.pins).get(p, reading) != reading:
                return t
            text += str(reading)
            if any(text.endswith(w) for w in cond.words):
                return t
        cells = naive_step(cells, boundary[p])
    return limit


def test_tree_against_naive() -> None:
    """For every condition and phase, the latest first failure by support and the branch counts up to 9 cells equal
    a cell-by-cell run of every half, and the branch counts equal the allowed words of column -1."""
    support = 9
    for name, cond in CONDITIONS.items():
        for phase in range(len(cond.block)):
            latest, branches, histogram = tree_failures(cond, support, phase)
            fails = [naive_first_failure(name, u, phase, 200) for u in range(1 << support)]  # (2^support,)
            assert latest == [max(fails[1 << (m - 1):1 << m]) for m in range(1, support + 1)], (name, phase)
            assert branches == [sum(f >= m for f in fails[:1 << m]) for m in range(1, support + 1)], (name, phase)
            assert branches == count_words(cond, phase, support)
            exact = sorted(f for f in fails[1 << (support - 1):] if f >= support)
            assert sorted(t for t, c in histogram[-1].items() for _ in range(c)) == exact


def test_entropy() -> None:
    """The kit's conditions have one free reading in three steps; 00 forbidden gives the golden mean; runs of 1s of
    at least 2 and of 0s of at least 3 give the root of x^5 = (1 - x)^2, x = 1 / lambda."""
    assert abs(entropy(CONDITIONS["001-kit"]) - 1 / 3) < 1e-9
    assert abs(entropy(CONDITIONS["011-kit"]) - 1 / 3) < 1e-9
    assert abs(entropy(CONDITIONS["011-no00"]) - math.log2((1 + math.sqrt(5)) / 2) / 3) < 1e-9
    roots = np.roots([1, 0, 0, -1, 2, -1])  # x^5 - (1 - x)^2 = x^5 - x^2 + 2x - 1
    x = min(r.real for r in roots if abs(r.imag) < 1e-12 and 0 < r.real < 1)
    assert abs(entropy(CONDITIONS["001-runs"]) + math.log2(x) / 3) < 1e-9


def solve_half(name: str, column: list[int]) -> int:
    """The left half, modulo 2^n, whose column -1 reads `column` from phase 0: bit t fixed by running the half."""
    cond = CONDITIONS[name]
    period = len(cond.block)
    boundary = [int(cond.block[t] == "1" and cond.block[(t + 1) % period] == "1") for t in range(period)]
    half = 0
    for t in range(len(column)):
        for bit in (0, 1):
            u = half | (bit << t)
            for s in range(t):
                u = (u >> 1) ^ (u | (u << 1) | boundary[s % period])
            if u & 1 == column[t]:
                half |= bit << t
                break
    return half


def test_sideways_columns() -> None:
    """Columns -1 .. -10 from the sideways map equal a forward run of the half that the readings determine."""
    rng = np.random.default_rng(5)
    for name in ("001-runs", "011-no00"):
        cond = CONDITIONS[name]
        period = len(cond.block)
        for _ in range(3):
            free = rng.integers(0, 2, 12)  # (12,)
            white = [p for p in range(period) if cond.block[p] == "0"]
            readings = tuple(dict(cond.pins).get(p, int(free[i])) for i in range(12) for p in white)
            cols = columns_from(cond, readings, 10)
            n = len(cols[0])
            half = solve_half(name, cols[0])
            boundary = [int(cond.block[t] == "1" and cond.block[(t + 1) % period] == "1") for t in range(period)]
            u = half
            for t in range(n - 10):
                for k in range(10):
                    assert (u >> k) & 1 == cols[k][t]
                u = (u >> 1) ^ (u | (u << 1) | boundary[t % period])


def test_forced_and_anf() -> None:
    """The kit's patterns, and columns -2 to -4 of 001 worked by hand: (not b0, b0, 1), (1, 0, b1), (1, b0 + b1, 0)."""
    rows = forced_cells(CONDITIONS["001-kit"], 9, 5)
    assert rows[:4] == ["0*1", "**1", "10*", "1*0"]
    assert forced_cells(CONDITIONS["011-kit"], 1, 3) == ["*01"]
    anf = column_anf(CONDITIONS["001-kit"], 4, 3)
    assert anf[1] == ["1 + b0", "b0", "1"] and anf[2] == ["1", "0", "b1"] and anf[3] == ["1", "b0 + b1", "0"]


def test_periodic_half() -> None:
    """A half whose readings repeat runs back to itself after a period of the readings, with column -1 on the
    pattern; constant readings give spatial period 12, the period-three ether."""
    for name, word in (("001-runs", (0, 1)), ("011-no00", (1,)), ("011-kit", (0, 1))):
        cond = CONDITIONS[name]
        period = len(cond.block)
        start, spatial, row = periodic_half(cond, word, 400)
        if len(word) == 1 or name == "001-runs":
            assert spatial == 12
        boundary = [int(cond.block[t] == "1" and cond.block[(t + 1) % period] == "1") for t in range(period)]
        q = len(columns_from(cond, word, 1)[0])
        u = sum(b << j for j, b in enumerate(row))
        column = columns_from(cond, word, 1)[0]
        for t in range(q):
            assert u & 1 == column[t]
            u = (u >> 1) ^ (u | (u << 1) | boundary[t % period])
        assert all((u >> j) & 1 == row[j] for j in range(300))
