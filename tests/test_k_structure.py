"""Tests for computations/k_structure.py: the head count against every integer below 2^h, the exact rationals against
the held map on long integers, the periodic points against the shift-model table, the closures against the tree search
and the counts of the k-ether-points finding, and the descent census against runs of whole integers."""

from __future__ import annotations

import functools
from fractions import Fraction
from pathlib import Path

import numpy as np

from computations import k_structure as ks
from computations.ether_certificate import background, held
from computations.held_shift import cycle_class


@functools.cache
def zoo4() -> frozenset[ks.Rat]:
    """The periodic points of H^2 in K with itinerary period at most 4 and tail period at most 14."""
    return frozenset(ks.zoo_points(4, 14))


@functools.cache
def seeds() -> frozenset[ks.Rat]:
    """The periodic points of H^2 in K with itinerary period at most 4, other than the stripes: the 14 of the ether."""
    return frozenset(x for x in zoo4() if not ks.is_stripe(x))


@functools.cache
def closure7() -> dict[ks.Rat, int]:
    """The closure of the 14 periodic points over tails of period 7."""
    return ks.closure(set(seeds()), 7)


def test_head_count_against_integers() -> None:
    """For h <= 12 the heads of h cells that keep bit 0 odd at every odd step below h, found by stepping every integer
    below 2^h (bit 0 at step t reads the cells 0 .. t only), number 2^ceil(h/2), as `head_count` says."""
    for h in range(1, 13):
        x = np.arange(1 << h, dtype=np.uint64)  # (2^h,)
        ok = np.ones(1 << h, dtype=bool)  # (2^h,)
        for t in range(1, h):
            x = (x >> np.uint64(1)) ^ (x | (x << np.uint64(1)))  # (2^h,)
            if t % 2 == 1:
                ok &= (x & np.uint64(1)) == 1
        assert int(ok.sum()) == ks.head_count(h) == 2 ** ((h + 1) // 2)


def test_stripe_heads_cover_the_tree() -> None:
    """Every head of 10 and 12 cells of the tree of K is the head of a point of K with a stripe tail."""
    assert ks.stripe_heads(10, 4) == 32
    assert ks.stripe_heads(12, 5) == 64


def test_rationals_against_integers() -> None:
    """For random rationals: `rat_step` agrees with the held map on 202 cells of the integer, each `rat_preimage` has
    the asked cell 0 and maps onto the rational, `canon` of a longer form is the same rational, and `denominator`
    agrees with the fraction."""
    rng = np.random.default_rng(5)
    for _ in range(40):
        p, q = int(rng.integers(0, 20)), int(rng.integers(1, 15))
        x = ks.canon(int(rng.integers(0, 1 << (p + q))), p, q)
        assert ks.rat_cells(ks.rat_step(x), 200) == held(ks.rat_cells(x, 202)) & ks.mask(200)
        for c in (0, 1):
            u = ks.rat_preimage(x, c)
            assert u[2] & 1 == c
            assert held(ks.rat_cells(u, 302)) & ks.mask(300) == ks.rat_cells(x, 300)
        assert ks.canon(ks.rat_cells(x, x[0] + 3 + 2 * x[1]), x[0] + 3, 2 * x[1]) == x
        p, q, cells = x
        value = Fraction(cells & ks.mask(p)) - Fraction((cells >> p) << p, (1 << q) - 1)
        assert ks.denominator(x) == value.denominator


def test_run_rat_against_direct_runs() -> None:
    """The exact run gives the first odd step with bit 0 equal to 0 as a run on 400 cells of the integer, and a point it
    calls a point of K has no such step in 150 steps."""
    rng = np.random.default_rng(7)
    points = [ks.canon(int(rng.integers(0, 1 << 20)), 13, 7) for _ in range(20)] + sorted(seeds())[::2]
    for x in points:
        r = ks.run_rat(x)
        u, first = ks.rat_cells(x, 400), -1
        for t in range(1, 151):
            u = held(u)
            if t % 2 == 1 and u & 1 == 0:
                first = t
                break
        assert (r["how"], r["step"]) == (0, first) if first > 0 else r["how"] == 1


def test_zoo_against_shift_model() -> None:
    """The points of period dividing 4 under H^2 are 16 (item 2 of the shift model: spatial periods 2 and 7, with 2 and
    14 points), each fixed by H^8, the 14 of period 7 on the ether."""
    z = zoo4()
    assert len(z) == 16
    for x in z:
        y = x
        for _ in range(4):
            y = ks.h2(y)
        assert y == x
    assert sorted((x[1], ks.ring_class(x)) for x in z).count((7, (7, 4))) == 14


def test_closure_seven() -> None:
    """The closure of the 14 periodic points over tails of period 7 has the 406 points of `k_survivors.tail7_closure`,
    303 of them with a tail on the ether cycle (the closure of the k-ether-points finding), depth 14 and preperiods up
    to 78, all with denominator 127."""
    cl = closure7()
    assert len(cl) == 406 and max(cl.values()) == 14 and max(x[0] for x in cl) == 78
    assert {ks.denominator(x) for x in cl} == {127}
    ether = {background(a, o, 7) for a in range(4) for o in range(7)}  # cells 7 k .. 7 k + 6 of each alignment
    start = {x: x[0] + (-x[0]) % 7 for x in cl}  # the first multiple of 7 at or above the preperiod
    assert sum(ks.rat_cells(x, start[x] + 7) >> start[x] in ether for x in cl) == 303
    rows, _, _ = ks.closure_levels(set(seeds()), 14, 6)
    assert [r["points"] for r in rows] == [14, 14, 28, 56, 112, 224, 384]


def test_closure_against_tree_search() -> None:
    """The rational points of K with least period at most 14 and p + q <= 18, found by the tree of K and exact runs,
    are the stripe-tailed ones and the points of the closure of period 14 in that range."""
    tree = ks.tree_rationals(18, 14)
    cl = ks.closure(set(seeds()), 14, max_pre=24)
    assert {x for x in tree if not ks.is_stripe(x)} == {x for x in cl if x[0] + x[1] <= 18}
    assert {x[1] for x in tree} == {2, 7, 14}


def test_descent_against_direct_runs() -> None:
    """At heads of 12 cells and two alignments, the breaks and descents by step agree with runs of the held map on the
    integers of 120 cells, the defect read against the ether."""
    h, cells = 12, 120
    for a, o in [(0, 5), (2, 0)]:
        r = ks.descent(h, a, o, max_steps=40)
        broke: dict[int, int] = {}
        fell: dict[int, int] = {}
        x = np.array([background(a, o, 64) & ~ks.mask(h)], dtype=np.uint64)
        leaves = ks.extend(x, h, 0, h).tolist()
        eth_head = background(a, o, h)
        leaves = [n for n in leaves if ((n & ks.mask(h)) ^ eth_head) >> (h - 1) == 1]
        assert len(leaves) == r["leaves"]
        for n in leaves:
            u = (n & ks.mask(h)) | (background(a, o, cells) & ~ks.mask(h))
            for t in range(1, 41):
                u = held(u) & ks.mask(cells)
                if t % 2 == 1 and u & 1 == 0:
                    broke[t] = broke.get(t, 0) + 1
                    break
                if t % 2 == 0 and ((u ^ background(a + t, o, cells)) & ks.mask(cells - t)).bit_length() - 1 < h - 1:
                    fell[t] = fell.get(t, 0) + 1
                    break
        assert {t: v for t, v in r["broke"].items() if v} == broke
        assert {t: v for t, v in r["fell"].items() if v} == fell


def test_search_points(tmp_path: Path) -> None:
    """A line of the search's output for a point of the closure is read back as that point, and a hit that breaks K is
    counted as a break."""
    x = max((y for y in closure7() if y[0] <= 57), key=lambda y: (y[0], y[2]))
    cells = ks.rat_cells(x, 64)
    path = tmp_path / "hits.txt"
    path.write_text(f"7 {cells >> 64:016x} {cells & ks.mask(64):016x}\n7 0 2\n")
    found, how = ks.search_points(str(path), 64)
    assert found == {x} and how == {1: 1, 0: 1}


def test_ring_transients_against_cycle_class() -> None:
    """The longest transient to each background on rings of 7 and 8 cells agrees with `held_shift.cycle_class`, which
    follows each word on its own (the ether's is 2 on 7 cells)."""
    for q in (7, 8):
        expect: dict[tuple[int, int], int] = {}
        for word in range(1 << q):
            transient, length, _, period = cycle_class(word, q)
            expect[(period, length)] = max(expect.get((period, length), 0), transient)
        assert ks.ring_transients(q) == expect
    assert ks.ring_transients(7)[(7, 4)] == 2
