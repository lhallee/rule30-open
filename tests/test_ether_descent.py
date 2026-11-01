"""The checker with descent of `Rule30Open.PeriodTwo.EtherCensus16`: each way of settling against direct runs, the
bound it gives against direct runs, its cost against the checker without descent and with blocks, and the Lean census
section against the module."""

from __future__ import annotations

from pathlib import Path

import numpy as np

from computations import defect_potential as dp
from computations import ether_certificate as ec
from computations import ether_descent as ed

BITS = ec.closed_bits()
MODULE = Path(__file__).resolve().parent.parent / "Rule30Open" / "PeriodTwo" / "EtherCensus16.lean"


def test_run_descent_against_direct_runs() -> None:
    """Every head of 6 cells settles, with descent below the head and below the first head of its block of 16; a
    descent reaches a head below the bound at the step it names, a repeat repeats, and a closed strip keeps the top at
    or below its cell for 120 more steps, all in direct runs with `step`."""
    hows = set()
    for a in range(4):
        for o in range(7):
            for head, below in [(h, h) for h in range(1 << 6)] + [(h, h // 16 * 16) for h in range(1 << 6)]:
                r = ed.run_descent(BITS, a, o, 61, 80, head, below)
                assert r["ok"] == 1
                hows.add(r["how"])
                n = head
                for t in range(r["step"]):
                    n = ec.step(a + t, o, n)
                if r["how"] == 3:
                    assert n == r["target"] < below
                elif r["how"] == 2:
                    assert r["step"] % 4 == 0
                    m = n
                    for t in range(r["period"]):
                        m = ec.step(a + r["step"] + t, o, m)
                    assert m == n
                else:
                    assert r["step"] % 4 == 0
                    for t in range(120):
                        n = ec.step(a + r["step"] + t, o, n)
                        assert n >> (r["cell"] + 1) == 0
    assert hows == {1, 2, 3}


def direct_runs(a: np.ndarray, o: np.ndarray, n: np.ndarray, steps: int, high: np.ndarray | None = None) -> np.ndarray:
    """The highest cell of each defect over `steps` steps, -1 for none, stepped all at once as two 64-bit words (cells
    0 .. 63 in `n` and 64 .. 126 in `high`, 0 if None) through the background of 128 cells, as `ec.step` steps one:
    the held map of the actual cells, xor the next background."""
    # a, o, n, high: (h,)
    words = np.array([[[ec.background(ph, off) >> (64 * k) & (2 ** 64 - 1) for k in (0, 1)] for off in range(7)]
                      for ph in range(4)], dtype=np.uint64)  # (4, 7, 2), the background as two words
    one, top = np.uint64(1), np.uint64(63)
    lo = n.astype(np.uint64)  # (h,)
    hi = np.zeros(n.size, dtype=np.uint64) if high is None else high.astype(np.uint64)  # (h,)
    highest = np.full(n.size, -1, dtype=np.int64)  # (h,)
    for t in range(steps):
        now, after = words[(a + t) % 4, o], words[(a + t + 1) % 4, o]  # (h, 2) each
        x_lo, x_hi = lo ^ now[:, 0], hi ^ now[:, 1]  # (h,) each
        up_lo, up_hi = (x_lo >> one) | (x_hi << top), x_hi >> one  # (h,) each, cell j + 1 at bit j
        down_lo, down_hi = x_lo << one, (x_hi << one) | (x_lo >> top)  # (h,) each, cell j - 1 at bit j
        lo = (up_lo ^ (x_lo | down_lo)) ^ after[:, 0]
        hi = ((up_hi ^ (x_hi | down_hi)) ^ after[:, 1]) & np.uint64(2 ** 63 - 1)  # cells 64 .. 126
        highest = np.maximum(highest, dp.tops128(lo, hi))  # the exact top of two words
    return highest  # (h,)


def test_direct_runs_against_step() -> None:
    """`direct_runs` against `ec.step` on sampled defects of 40 cells placed up to cell 119, in either word, at
    sampled alignments."""
    rng = np.random.default_rng(3)
    a, o = rng.integers(0, 4, 40), rng.integers(0, 7, 40)  # (40,) each
    heads = [int(rng.integers(0, 2 ** 40)) << int(rng.integers(0, 80)) for _ in range(40)]
    lo = np.array([head & (2 ** 64 - 1) for head in heads], dtype=np.uint64)  # (40,)
    hi = np.array([head >> 64 for head in heads], dtype=np.uint64)  # (40,)
    highest = direct_runs(a, o, lo, 30, hi)  # (40,)
    for k, head in enumerate(heads):
        n, best = head, -1
        for t in range(30):
            n = ec.step(int(a[k]) + t, int(o[k]), n)
            best = max(best, n.bit_length() - 1)
        assert best == highest[k]


def test_bound_against_direct_runs() -> None:
    """The bound the census with descent gives holds in direct runs (`direct_runs`): every head of 7 cells at every
    alignment keeps its defect below cell 61 for 500 steps, and the census with descent settles every one of them with
    the bound 61."""
    r = ed.census_descent(7, 0, 61, 80, 16)
    assert r["heads"] == 28 * 128 and r["failed"] == 0 and r["top"] <= 60
    a, o, head = np.meshgrid(np.arange(4), np.arange(7), np.arange(1 << 7), indexing="ij")  # (4, 7, 128) each
    assert direct_runs(a.reshape(-1), o.reshape(-1), head.reshape(-1), 500).max() < 61


def test_descent_is_cheaper() -> None:
    """With descent, the heads of 8 cells settle in fewer rounds than without, with the same highest top; descent
    below the first head of a block of 8 costs at most 10% more rounds than descent below the head itself."""
    without = ec.census(8, 61, 80)
    with_descent = ed.census_descent(8, 0, 61, 80, 1)
    blocks = ed.census_descent(8, 0, 61, 80, 8)
    assert with_descent["failed"] == 0 and blocks["failed"] == 0 and with_descent["heads"] == without["heads"]
    assert with_descent["rounds"] < 0.7 * without["rounds"]
    assert with_descent["rounds"] <= blocks["rounds"] <= 1.1 * with_descent["rounds"]
    assert with_descent["top"] <= without["top"] and blocks["top"] <= without["top"]


def test_lean_census_matches_module() -> None:
    """The census section of the Lean module is the one this module prints for heads of 16 cells."""
    text = MODULE.read_text()
    for line in ed.lean_descent_census(16, 1 << 12, 79, 110, 4096, 256).splitlines():
        assert line in text
