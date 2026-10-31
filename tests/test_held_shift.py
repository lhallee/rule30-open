"""The shift model of the period-two condition against stepping integers directly."""

from __future__ import annotations

import random
from fractions import Fraction

import numpy as np

from computations.held_shift import (attractors, ether_window, front_rate, greedy_rise, column_zero, cycle_class, defect_tops, degree_profile, domain,
                                     domain_integer, eventual_period, forced_halves, held, itinerary, kicked_step,
                                     rational_points, replicate, ring_cycle, ring_next, stripe_invariant, stripe_window, verified_hits)


def survivors(depth: int) -> set[int]:
    """Every U below 2^depth with H^t(U) odd at the odd t below depth, by stepping Python integers."""
    kept = set()
    for U in range(1 << depth):
        V, alive = U, True
        for t in range(1, depth):
            V = held(V)
            if t % 2 == 1 and V & 1 == 0:
                alive = False
                break
        if alive:
            kept.add(U)
    return kept


def test_forced_halves() -> None:
    """The tree of forced bits is the set of survivors, with 2^ceil(depth / 2) of them."""
    assert {int(u) for u in forced_halves(12)} == survivors(12)
    assert len(forced_halves(13)) == 1 << 7


def test_itinerary_is_a_shift() -> None:
    """The itineraries of the survivors modulo 2^16 are the 2^8 words of eight readings, each once, and H^2 shifts."""
    halves = [int(u) for u in forced_halves(16)]
    words = {tuple(itinerary(u, 8)) for u in halves}
    assert len(words) == 1 << 8
    for u in halves[:20]:
        assert itinerary(held(held(u)), 7) == itinerary(u, 8)[1:]


def test_domains_are_periodic_and_keep_the_condition() -> None:
    """Each periodic point returns after its period under the kicked map and reads the column it was built from."""
    for block, max_n in (("01", 3), ("011", 3), ("001", 2)):
        period = len(block)
        for n in range(1, max_n + 1):
            for word in range(1 << (n * block.count("0"))):
                pre, per = domain(block, word, n)
                bits = 400
                U = domain_integer(pre, per, bits)
                column, boundary = column_zero(block, word, n)
                length = n * period
                V = U
                for t in range(length):
                    assert (V & 1) == (column >> t) & 1, (block, n, word, t)
                    V = kicked_step(V, (boundary >> t) & 1) & ((1 << bits) - 1)
                assert (V ^ U) & ((1 << (bits - length - 5)) - 1) == 0, (block, n, word)


def test_stripes_and_ether() -> None:
    """The fixed points of the shift are the stripes 1010.. and 0101.., and period 2 gives the period 7 of the ether."""
    assert domain("01", 1, 1) == ([], [1, 0])
    assert domain("01", 0, 1) == ([], [0, 1])
    assert sorted(len(domain("01", w, 2)[1]) for w in range(4)) == [2, 2, 7, 7]
    assert sorted(len(domain("01", w, 4)[1]) for w in range(16)).count(7) == 14


def test_rational_points() -> None:
    """The stripes are rational points with value -1/3 and -2/3, all points are preperiodic with a short itinerary."""
    found = rational_points(24, 120)
    assert Fraction(-1, 3) in found and Fraction(-2, 3) in found and Fraction(-1, 127) in found
    assert all(q in (2, 7, 14) for (_, q) in found.values())
    for value in found:
        code = (value.numerator * pow(value.denominator, -1, 1 << 300)) & ((1 << 300) - 1)
        assert eventual_period(itinerary(code, 60), settle=5) is not None
    assert 0 not in found and Fraction(1) not in found


def test_degree_profile() -> None:
    """The degree and term count of the forced bits against a Moebius transform by sets of Python integers."""
    rows = degree_profile(12)
    halves = [int(u) for u in forced_halves(12)]
    for position, degree, terms in rows:
        monomials = set()
        for mask in range(1 << 6):
            coefficient = 0
            for sub in range(1 << 6):
                if sub & mask == sub:
                    coefficient ^= (halves[sub] >> position) & 1
            if coefficient:
                monomials.add(mask)
        assert (degree, terms) == (max(m.bit_count() for m in monomials), len(monomials))
    assert [row[1] for row in rows] == [1, 2, 3, 4, 5, 6]


def test_ring_attractors() -> None:
    """The stripes are fixed points of the ring map, the ether is a cycle of four on seven cells, and the tails of
    the rational points of K reach only those two attractors."""
    assert ring_cycle(0b01, 2) == (0, [0b01]) and ring_cycle(0b10, 2) == (0, [0b10])
    transient, cycle = ring_cycle(0b0000001, 7)
    assert transient == 0 and len(cycle) == 4 and ring_next(cycle[-1], 7) == cycle[0]
    assert cycle_class(0b0000001, 7)[1:] == (4, 1, 7)
    census = attractors(rational_points(20, 100))
    assert {(block, period) for (block, period, _) in census} == {(1, 2), (1, 7)}


def test_defect_top_climbs_only_above_a_zero() -> None:
    """The top of the defect rises by at most one cell, and by exactly one when the background reads 0 above it."""
    rng = random.Random(7)
    for tail, length in ((0b01, 2), (0b0000001, 7), (0b0010011, 7), (0b1, 1), (0b0, 1), (0b011, 3)):
        for _ in range(30):
            p = rng.randrange(3, 12)
            head = rng.getrandbits(p)
            tops = defect_tops(head, p, tail, length, 40)
            ring = tail
            for t in range(39):
                top = tops[t]
                assert tops[t + 1] <= top + 1
                shift = p % length
                anchored = ((ring << shift) | (ring >> (length - shift))) & ((1 << length) - 1)
                if top >= 0 and (replicate(anchored, length, top + 2) >> (top + 1)) & 1 == 0:
                    assert tops[t + 1] == top + 1, (head, p, tail, t)
                ring = ring_next(ring, length)


def test_stripe_confines_every_defect() -> None:
    """On a stripe the defect never passes the cell above the head, so the orbit lives in a finite window and its
    itinerary is eventually periodic."""
    assert stripe_window(6) == 0
    for tail in (0b01, 0b10):
        for p in range(1, 6):
            for head in range(1 << p):
                tops = defect_tops(head, p, tail, 2, 30)
                assert all(tops[t + 2] <= tops[t] for t in range(28)), (head, p, tail)
    rng = random.Random(3)
    for _ in range(20):
        p = rng.randrange(1, 25)
        code = (rng.getrandbits(p) | (int("01" * 400, 2) << p)) & ((1 << 900) - 1)
        assert eventual_period(itinerary(code, 150), settle=3) is not None


def test_verified_hits() -> None:
    """A hit that is the stripe is kept as -1/3, and a prefix whose periodic extension breaks the condition is dropped."""
    found, failed = verified_hits(["2 0000000000000000 0000000055555555", "1 0000000000000000 0000000000000001"], 32)
    assert found == {Fraction(-1, 3): (0, 2)} and failed == 1


def test_ether_defects_stop_climbing() -> None:
    """Every defect of two cells on the ether climbs for a while and then stops: the last window of steps adds nothing."""
    first, middle, last = ether_window(2, 300)
    assert last <= middle and 0 < first <= middle


def test_front_automaton() -> None:
    """The bound on the speed of a front is the vacuum's 1, close to 0 on a stripe, and positive on the ether, where
    the greedy chase also never stops. At window 5 the longest walk of 2,500 steps gains more than the 452 nodes of the
    graph, so the graph has a cycle of positive gain, the certificate `--front 8 --rounds 20000` gives at window 8."""
    assert front_rate([0], 1, 3, 100) == 1.0
    assert front_rate([0b01], 2, 4, 100) <= 0.01
    _, cycle = ring_cycle(0b1000000, 7)
    assert front_rate(cycle, 7, 5, 200) > 0.2 and greedy_rise(cycle, 7, 500) > 200
    assert round(front_rate(cycle, 7, 5, 2500) * 2500) > 4 * 7 * 2 ** 4 + 4 - 1


def test_stripe_invariant_set() -> None:
    """Every point of K with a stripe tail and a head of up to 12 cells falls onto the stripe, for both stripes; the
    first others appear at 5 cells for A (E = 3 and 20 beyond the stripe) and at 5 cells for B."""
    for stripe_a in (True, False):
        for head in range(1, 13):
            states, stuck = stripe_invariant(head, stripe_a)
            assert stuck == 0 and states[0] == 0
    assert stripe_invariant(5, True)[0] == [0, 3, 20] and stripe_invariant(5, False)[0] == [0, 27]
    assert stripe_invariant(12, True)[0][:6] == [0, 3, 20, 879, 880, 883]
