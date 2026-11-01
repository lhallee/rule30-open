"""The checker with descent of `Rule30Open.PeriodTwo.EtherCensus16`: each way of settling against direct runs, the
bound it gives against direct runs, its cost against the checker without descent and with blocks, and the Lean census
section against the module."""

from __future__ import annotations

from pathlib import Path

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


def test_bound_against_direct_runs() -> None:
    """The bound the census with descent gives holds in direct runs: every head of 7 cells at every alignment keeps its
    defect below cell 61 for 500 steps, and the census with descent settles every one of them with the bound 61."""
    r = ed.census_descent(7, 0, 61, 80, 16)
    assert r["heads"] == 28 * 128 and r["failed"] == 0 and r["top"] <= 60
    for a in range(4):
        for o in range(7):
            for head in range(1 << 7):
                n = head
                for t in range(500):
                    n = ec.step(a + t, o, n)
                    assert n >> 61 == 0


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
