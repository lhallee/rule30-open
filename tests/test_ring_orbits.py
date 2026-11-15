"""Tests of computations.ring_orbits: periodic orbits on rings against a step-by-step search of every state."""

from __future__ import annotations

import numpy as np


def test_ring_orbits() -> None:
    """The periodic orbits on rings, against a step-by-step search of every state on rings of up to 10 cells, and the
    ether's ring of 7 cells: its alternating column has a left neighbor of period 4."""
    from computations import ring_orbits

    def brute(cells: int) -> int:
        full = (1 << cells) - 1

        def nxt(s: int) -> int:
            left = ((s << 1) | (s >> (cells - 1))) & full
            right = ((s >> 1) | (s << (cells - 1))) & full
            return left ^ (s | right)

        states = np.arange(1 << cells, dtype=np.int64)  # (2^M,), every start, stepped together
        for _ in range(1 << cells):
            states = ((((states << 1) | (states >> (cells - 1))) & full)
                      ^ (states | (((states >> 1) | (states << (cells - 1))) & full)))
        cyclic = set(states.tolist())  # after 2^M steps the state is on its cycle
        classes = set()
        for s in cyclic:
            orbit, x = [s], nxt(s)
            while x != s:
                orbit.append(x)
                x = nxt(x)
            classes.add(min(((y << r) | (y >> (cells - r))) & full for y in orbit for r in range(cells)))
        return len(classes)

    for cells in range(1, 11):
        assert len(ring_orbits.orbits(cells)) == brute(cells)
    found, counts = ring_orbits.witnessed(14, 16)
    assert found == {"01": 7} and counts[6] == 3
