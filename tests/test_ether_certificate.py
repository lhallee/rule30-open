"""The checker of `Rule30Open.PeriodTwo.EtherCensus`: the ether against the ring map, the defect step against the held
map on whole integers, the closed strips against `defect_potential` and direct runs, the head checker against direct
runs, and the Lean tables against the module."""

from __future__ import annotations

import random
from pathlib import Path

from computations import defect_potential as dp
from computations import ether_certificate as ec
from computations.held_shift import held, ring_next

BITS = ec.closed_bits()
MODULE = Path(__file__).resolve().parent.parent / "Rule30Open" / "PeriodTwo" / "EtherCensus.lean"


def test_ether_is_the_ring_cycle() -> None:
    """`eth` is the cycle of four states of the ring map on seven cells, read with the cell j - 1 as j + 6, the rule
    `eth_step` of the module."""
    for a in range(4):
        state = sum(int(ec.eth(a, j)) << j for j in range(7))
        assert ring_next(state, 7) == sum(int(ec.eth(a + 1, j)) << j for j in range(7))
        for j in range(7):
            assert ec.eth(a + 1, j) == (ec.eth(a, j + 1) ^ (ec.eth(a, j) | ec.eth(a, j + 6)))


def test_step_against_held_map() -> None:
    """The defect stepped with `step` is the whole integer stepped with the held map, xor the ether, on the cells below
    126, for random heads at random alignments."""
    rng = random.Random(3)
    width = 400
    for _ in range(20):
        a, o, p = rng.randrange(4), rng.randrange(7), rng.randrange(1, 13)
        head = rng.getrandbits(p)
        U = head | (ec.background(a, o, width) >> p << p)  # (width bits) the head, then the ether from cell p on
        n = head ^ (ec.background(a, o, p))
        for t in range(60):
            mask = (1 << 120) - 1
            assert n & mask == (U ^ ec.background(a + t, o, width)) & mask
            if n >> 120:
                break
            n = ec.step(a + t, o, n)
            U = held(U) & ((1 << (width - t - 1)) - 1)


def test_closed_strips() -> None:
    """The 1,915 closed strips, 433, 533, 344 and 605 at the four phases, all at residue 5, are `defect_potential`'s,
    pass the closure check, and `strip_step` is the defect step on the strip."""
    closed = dp.closed_strips(dp.STRIP)  # (4, 7, 2^13)
    assert [int(closed[a].sum()) for a in range(4)] == [433, 533, 344, 605]
    for a in range(4):
        for r in range(7):
            assert BITS[7 * a + r] == sum(1 << int(s) for s in closed[a, r].nonzero()[0])
            assert (BITS[7 * a + r] != 0) == (r == ec.RESIDUE)
    assert ec.closure_ok(BITS)
    rng = random.Random(5)
    for _ in range(200):
        a, o = rng.randrange(4), rng.randrange(7)
        c = 12 + rng.randrange(40)
        n = rng.getrandbits(c + 1)
        below = (n >> (c - 13)) & 1 if c >= 13 else int(ec.eth(a, o + 6))
        new, rise = ec.strip_step(a, (c + o) % 7, n >> (c - 12), below)
        after = ec.step(a, o, n)
        assert new == (after >> (c - 12)) & ((1 << 13) - 1)
        assert rise == (after >> (c + 1)) & 1


def test_closed_strip_keeps_the_top() -> None:
    """A defect that lies in a closed strip at c, with random cells below, keeps its top at or below c for 80 steps."""
    rng = random.Random(7)
    members = [s for s in range(1 << 13) if (BITS[7 * 0 + ec.RESIDUE] >> s) & 1]
    for _ in range(40):
        o = rng.randrange(7)
        c = 12 + ((5 - 12 - o) % 7) + 7 * rng.randrange(5)
        n = (rng.choice(members) << (c - 12)) | rng.getrandbits(c - 12)
        for t in range(80):
            n = ec.step(t, o, n)
            assert n >> (c + 1) == 0


def test_run_head_against_direct_runs() -> None:
    """Every head of 4 cells settles; a head settled by a repeat repeats in a direct run, and a head settled by a closed
    strip keeps its top at or below the strip's cell for 120 more steps."""
    for a in range(4):
        for o in range(7):
            for head in range(1 << 4):
                r = ec.run_head(BITS, a, o, 61, 80, head)
                assert r["ok"] == 1 and r["step"] % 4 == 0
                n = head
                for t in range(r["step"]):
                    n = ec.step(a + t, o, n)
                if r["how"] == 2:
                    m = n
                    for t in range(r["period"]):
                        m = ec.step(a + r["step"] + t, o, m)
                    assert m == n
                else:
                    for t in range(120):
                        n = ec.step(a + r["step"] + t, o, n)
                        assert n >> (r["cell"] + 1) == 0


def test_census_counts() -> None:
    """The census of heads of 5 cells: every head settles, by the same way as in `defect_potential.census`, which
    checks the closed strip at every step rather than at every fourth."""
    r = ec.census(5, 61, 80)
    assert r["heads"] == 28 * 32 and r["failed"] == 0
    closed = dp.closed_strips(dp.STRIP)
    strip = 0
    for a in range(4):
        for o in range(7):
            d = dp.census(5, a, o, 400, closed)
            assert (d["settled"] >= 0).all()
            strip += int((d["cell"] >= 0).sum())
    assert strip == r["strip"]


def test_lean_tables_match_module() -> None:
    """The tables of the Lean module are the ones this module prints."""
    text = MODULE.read_text()
    for line in ec.lean_tables().splitlines():
        assert line in text
    assert "theorem census (a o : Nat)" in ec.lean_census(4, 49, 70, 8)
