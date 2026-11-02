"""Tests for computations/k_survivors.py: the tree filter against the walk and `break_run` of `ether_k_tree`, the wide
filter and the exact run against the held map on whole integers, the preimages against a step forward, the counts of
true points against the tail census and the backward closure, and the census section of `EtherKTree32` against the
module."""

from __future__ import annotations

import functools
from pathlib import Path

import numpy as np

from computations import k_survivors as ks
from computations.ether_certificate import background, held
from computations.ether_k_tree import tree_leaves
from computations.no_k_tails16 import break_run

MODULE = Path(__file__).resolve().parent.parent / "Rule30Open" / "PeriodTwo" / "EtherKTree32.lean"
CELLS = 600  # cells of a whole half in the direct runs


@functools.cache
def census24() -> dict[str, object]:
    """`classify` at heads of 24 cells, computed once for the tests that read it."""
    return ks.classify(24)


def whole_half(a: int, o: int, d: int, cells: int = CELLS) -> int:
    """The half with defect d against the ether at (a, o), on the cells 0 .. cells - 1."""
    return d ^ background(a, o, cells)


def direct_break(u: int, steps: int, cells: int = CELLS) -> int:
    """The first odd step t <= steps with bit 0 of H^t(u) equal to 0, or -1, on a whole integer of `cells` cells (bit 0
    at step t reads the cells up to t, so it is right while t < cells)."""
    assert steps < cells
    for t in range(1, steps + 1):
        u = held(u)
        if t % 2 == 1 and u & 1 == 0:
            return t
    return -1


def test_tree_filter_against_walk() -> None:
    """At heads of 12 and 13 cells and three alignments, the survivors of step 63 are the leaves of `tree_leaves` on
    which `break_run` finds no break in 32 rounds, and the chunked tree gives the same survivors."""
    for head in (12, 13):
        for a, o in [(0, 0), (1, 5), (3, 2)]:
            leaves, _ = tree_leaves(head, a, o)
            expect = sorted(n for n in leaves if break_run(n, 32)[0] < 0)
            assert ks.tree_survivors(head, a, o).tolist() == expect
            assert ks.tree_survivors(head, a, o, chunk=4).tolist() == expect


def test_wide_filter_and_settle_against_direct_runs() -> None:
    """For every head of 24 cells that passes step 63 at four alignments: the wide filter and the exact run give the
    break at the same odd step as a run of the held map on the whole integer, and a head they call a true point has no
    break in 500 steps, and its half after `start + period` steps equals its half after `start` steps on the cells
    the run still reads right."""
    head = 24
    for a, o in [(0, 0), (1, 5), (2, 0), (3, 5)]:
        surv = ks.tree_survivors(head, a, o)  # (m,)
        wide, broke = ks.wide_survivors(surv, a, o, 128)  # (k,)
        assert sum(broke.values()) + len(wide) == len(surv)
        low = (1 << head) - 1
        for n in surv.tolist():
            d0 = (n & low) ^ background(a, o, head)
            u = whole_half(a, o, d0)
            first = direct_break(u, 500)
            r = ks.settle(d0, a, o)
            if first > 0:
                assert r["how"] == 0 and r["step"] == first
                assert (n in wide.tolist()) == (first > 127)
            else:
                assert r["how"] == 1 and n in wide.tolist()
                x, y = u, u
                for _ in range(r["start"]):
                    x = held(x)
                for _ in range(r["start"] + r["period"]):
                    y = held(y)
                safe = CELLS - r["start"] - r["period"] - 2
                assert (x ^ y) & ((1 << safe) - 1) == 0


def test_preimages_against_a_step_forward() -> None:
    """Every preimage that `preimage` returns maps onto its image under the held map on the cells a whole integer
    reads right, and agrees with the ether from its bit length on; the preimages in K with an ether tail of every other
    true point of up to 24 cells are in K for 300 steps."""
    rng = np.random.default_rng(5)
    for _ in range(60):
        a, o = int(rng.integers(4)), int(rng.integers(7))
        d = int(rng.integers(1 << 20))
        for c in (0, 1):
            w = ks.preimage(d, a, o, c)
            if w < 0:
                continue
            u = whole_half(a - 1, o, w)
            assert u & 1 == c
            assert (held(u) ^ whole_half(a, o, d)) & ((1 << (CELLS - 2)) - 1) == 0
    for a, o, d0, _ in census24()["points"][::2]:
        for u in ks.k_preimages(d0, a, o):
            assert direct_break(whole_half(a - 2, o, u), 300) < 0


def test_counts_and_closure() -> None:
    """The true points of up to 16 cells are the 34 heads that the tail census finds reaching a periodic point of K;
    up to 24 cells there are 54, on four periodic orbits of 14 periodic points of K; their backward closure has 303
    points, of which the 54 with at most 24 cells are exactly the true points, each settled by the exact run, 74 of
    them raising their top and 47 growing under H^2 (that step checked on whole integers); with any
    tail of period 7 the closure has 406 points, 278 of them with a preperiod of at most 57, the count of points with
    denominator 127 in item 7 of the shift model, none of them an integer."""
    r = census24()
    pts = {(a, o, d0) for a, o, d0, _ in r["points"]}
    assert sum(d0.bit_length() <= 16 for _, _, d0 in pts) == 34 and not r["undecided"]
    assert len(pts) == 54
    seeds = ks.periodic_seeds(r["points"])
    assert len(seeds) == 14
    orbits = {ks.orbit_key(ks.cycle_states(d0, a, o, rr), o) for a, o, d0, rr in r["points"]}
    assert len(orbits) == 4
    closure = ks.backward_closure(seeds)
    assert len(closure) == 303 and max(k[2].bit_length() for k in closure) == 78
    assert {k for k in closure if k[2].bit_length() <= 24} == pts
    for a, o, d in closure:
        assert ks.settle(d, a, o)["how"] == 1
    shape = ks.closure_shape(closure, seeds)
    assert (shape["repeat"], shape["depth"], shape["gap"]) == (36, 14, 11)
    assert shape["preimages"] == {0: 150, 1: 3, 2: 150}
    assert {k[:2] for k in closure} == {k[:2] for k in pts}
    rise, grow = ks.monotone_counts(closure)
    assert sum(v for k, v in rise.items() if k > 0) == 74 and max(rise) == 5
    assert sum(v for k, v in grow.items() if k > 0) == 47 and grow[0] == 52
    for a, o, d in list(closure)[::20]:
        u = whole_half(a, o, d)
        twice = ks.dstep(ks.dstep(d, a, o), a + 1, o)
        assert (held(held(u)) ^ whole_half(a + 2, o, twice)) & ((1 << (CELLS - 4)) - 1) == 0
    tails = ks.tail7_closure(seeds)
    assert len(tails) == 406 and sum(q <= 57 for _, q in tails) == 278
    ether = set()
    for a, o, d in closure:
        u = d ^ background(a, o, d.bit_length() + 14)
        ether.add(ks.periodic7([(u >> j) & 1 for j in range(d.bit_length() + 14)], d.bit_length()))
    assert ether <= tails
    words = {tuple(ks.tail_cell(x, j) for j in range(200, 207)) for x in tails}
    assert (0,) * 7 not in words and (1,) * 7 not in words


def test_lean_section_matches_module() -> None:
    """The census section of `EtherKTree32` is the one `lean_section32` prints, and the walk of `lean_roots` at one
    alignment, on heads of 12 cells, reaches the subtree roots that the tree of `ether_k_tree` passes through at cell 6."""
    text = MODULE.read_text()
    assert ks.lean_section32() in text
    roots = [n for _, n, _ in ks.lean_roots(1, 3, head=12)]
    leaves, _ = tree_leaves(12, 1, 3)
    assert len(roots) == 8
    assert sorted(roots) == sorted({n & ((1 << 6) - 1) | ks.ether_tail(12, 1, 3) for n in leaves})
