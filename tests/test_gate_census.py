"""The traps beside an alternating center against direct runs of Python integers."""

from __future__ import annotations

import re
from pathlib import Path

import numpy as np

from computations import absorption
from computations.gate_census import (LOCK_WIDTH, LOCK_WORD, census, double_step, double_steps, gap_entry, lean_classes,
                                      seven_lock)


def run(half: int, phase: int, steps: int) -> list[int]:
    """The rows of the driven right half at times 0 .. steps - 1, by stepping a Python integer."""
    rows, row = [], half
    for t in range(steps):
        rows.append(row)
        center = 1 if (t + phase) % 2 == 0 else 0
        row = ((row << 1) | center) ^ (row | (row >> 1))
    return rows


def test_double_step_matches_run() -> None:
    rng = np.random.default_rng(1)
    for _ in range(40):
        half = int(rng.integers(0, 1 << 40))
        rows = run(half, 0, 40)
        for t in range(1, 37, 2):  # white steps of phase 0
            x1, x2 = (rows[t] >> 32) & 1, (rows[t + 1] >> 32) & 1
            assert double_step(rows[t] & 0xFFFFFFFF, 32, x1, x2) == rows[t + 2] & 0xFFFFFFFF
    windows = np.arange(64)
    succ = double_steps(windows, 6)  # (64, 4)
    for w in range(64):
        assert succ[w].tolist() == [double_step(w, 6, a, b) for a in (0, 1) for b in (0, 1)]


def test_seven_lock_is_closed_and_forces_the_word() -> None:
    classes, word = seven_lock(steps=2000)
    assert word == LOCK_WORD and [len(c) for c in classes] == [22, 22, 24, 34, 37, 32, 24]
    member = {w: k for k, cls in enumerate(classes) for w in cls}
    for w, k in member.items():
        assert w & 1 == int(LOCK_WORD[k])
        for x1 in (0, 1):
            for x2 in (0, 1):
                assert member[double_step(w, LOCK_WIDTH, x1, x2)] == (k + 1) % 7


def test_lock_example_of_the_lean_file() -> None:
    """The half 489 enters class 4 of the lock at step 29 (`example_enters`), and column 1 then repeats the word."""
    classes, _ = seven_lock(steps=2000)
    rows = run(489, 0, 29 + 2 * 300)
    assert rows[29] & 0xFFFFFFFF in classes[4]
    later = [rows[29 + 2 * n] & 1 for n in range(300)]
    assert later == [int(LOCK_WORD[(4 + n) % 7]) for n in range(300)]


def test_lean_file_lists_the_lock() -> None:
    classes, _ = seven_lock(steps=2000)
    text = Path(__file__).resolve().parents[1].joinpath("Rule30Open/PeriodTwo/SevenLock.lean").read_text()
    assert lean_classes(classes) in text


def test_gap_trap_against_runs() -> None:
    """Every half of up to 8 cells that the census puts in the gap trap has gaps of 3 and 5 in a long direct run."""
    gap = gap_entry()  # (2^16,)
    for half in range(256):
        rows = run(half, 0, 1200)
        white = [rows[t] for t in range(1, 1200, 2)]
        entered = next((s for s, w in enumerate(white) if gap[w & 0xFFFF]), None)
        if entered is None:
            continue
        blacks = [s for s in range(entered, len(white)) if white[s] & 1]
        assert all(b - a in (3, 5) for a, b in zip(blacks, blacks[1:]))


def test_census_small() -> None:
    gap = gap_entry()  # (2^16,)
    classes, _ = seven_lock(steps=2000)
    wall = absorption.kit_wall()  # (4, 2^13)
    entry = census(6, 0, 1200, gap, classes, wall)
    entered = (entry["gap"] >= 0) | (entry["lock"] >= 0) | (entry["family"] >= 0)
    assert entered.all()
    assert int((entry["gap"] >= 0).sum()) == 62 and int((entry["family"] >= 0).sum()) == 2
    assert int(entry["gap"][0]) == 293  # the empty half, as in the kit's `u_empty_gaps` (window at time 293)
    for half in range(64):
        if entry["family"][half] >= 0:  # the kit's family keeps column 1 periodic: alternating at the white steps here
            rows = run(half, 0, 1600)
            col = [rows[t] & 1 for t in range(801, 1600, 2)]
            assert all(col[n] != col[n + 1] for n in range(len(col) - 1))
