"""Tests of computations.right_half: `lock_breaks` against the right half stepped as 64-bit words."""

from __future__ import annotations

import numpy as np


def test_lock_breaks() -> None:
    """`right_half.lock_breaks` against the right half stepped as 64-bit words by `absorption.step_rows`: driven by
    01111, start 2 holds column 1 with period 10 at the white times from step 6,000 until step 13,000."""
    from computations import absorption, right_half
    start = right_half.random_starts(30, 64)[2]
    steps = 14000
    _, count, first = right_half.lock_breaks("01111", start, steps, 10, 6000)
    rows = np.zeros((1, (64 + steps) // 64 + 2), dtype=np.uint64)  # (1, words)
    rows[0, 0] = np.uint64(start)
    column = np.zeros(steps, dtype=np.uint8)  # (steps,)
    for t in range(steps):
        column[t] = int(rows[0, 0]) & 1
        rows = absorption.step_rows(rows, int("01111"[t % 5]))  # (1, words)
    white = np.array(["01111"[t % 5] == "0" for t in range(steps - 10)])  # (steps - 10,)
    breaks = np.flatnonzero((column[:-10] != column[10:]) & white)  # (b,)
    late = breaks[breaks > 6000]  # (c,)
    assert first == 13000 == int(late[0]) and count == late.size
