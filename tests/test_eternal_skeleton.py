"""eternal_skeleton against a direct rule 30 run of random rows, a brute-force periodic-point search, the single cell's
diagonal periods, and the uniform onsets of seed-uniform-onsets."""

from __future__ import annotations

import numpy as np

from computations.eternal_skeleton import cycle_lengths, left_step, limit_set, seed_cycle, table


def _rule30_row(row: list[int], steps: int) -> list[list[int]]:
    """Rows of rule 30 from `row` (white beyond its ends), each padded by `steps` cells on both sides."""
    width = len(row) + 2 * steps + 2
    x = [0] * (steps + 1) + row + [0] * (steps + 1)
    out = [x]
    for _ in range(steps):
        x = [(x[i - 1] if i > 0 else 0) ^ (x[i] | (x[i + 1] if i + 1 < width else 0)) for i in range(width)]
        out.append(x)
    return out


def test_left_step_is_rule30() -> None:
    rng = np.random.default_rng(1)
    n, steps = 10, 12
    for _ in range(20):
        row = [1] + [int(v) for v in rng.integers(0, 2, size=n + 2 * steps)]
        rows = _rule30_row(row, steps)
        lo = steps + 1  # the edge cell of the row
        s = np.array([sum(row[d] << d for d in range(n))], dtype=np.int64)  # (1,)
        for t in range(steps + 1):
            diag = sum(rows[t][lo - t + d] << d for d in range(n))  # diagonal d at time t
            assert int(s[0]) == diag
            s = left_step(s, n)


def test_limit_set_against_brute_force() -> None:
    # the periodic points of G_n among states with bit 0 set, found by iterating each state 2^n times
    for n in range(2, 9):
        brute = set()
        for s0 in range(1, 1 << n, 2):
            s = np.array([s0], dtype=np.int64)  # (1,)
            for _ in range(1 << n):
                s = left_step(s, n)
            start = int(s[0])
            y = left_step(s, n)
            while int(y[0]) != start:
                y = left_step(y, n)
            brute.add(start)
        states, _ = limit_set(n)
        assert set(int(v) for v in states) == brute
        cyc = cycle_lengths(states, n)
        assert all(c & (c - 1) == 0 for c in cyc)  # powers of two


def test_single_cycle_and_numbers() -> None:
    rows = table(14, progress=False)
    assert all(r.single for r in rows)
    assert [r.seed_length for r in rows if r.n in (3, 4, 8, 9, 14)] == [1, 2, 2, 4, 4]
    # the period of the single cell's first n diagonals: 2 from diagonal 3, 4 from diagonal 8
    # uniform settling: the largest onset over every seed, max of M_j for j < n (seed-uniform-onsets)
    m = [0, 1, 2, 2, 4, 5, 6, 8, 7, 11, 12, 14, 14, 16, 17, 19]
    for r in rows:
        assert r.settle == max(m[: r.n])
    cyc, onset = seed_cycle(9)
    assert len(cyc) == 4 and onset == 2
