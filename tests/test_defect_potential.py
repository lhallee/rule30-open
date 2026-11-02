"""The top of a defect on the ether: the bit-parallel defect against the held map on whole integers, the closed strips
against the mirror wall sets and direct runs, the census and the local tree against direct runs, and the window
automaton against `held_shift.front_rate`."""

from __future__ import annotations

import random

import numpy as np

from computations import background_halves as bh
from computations import defect_potential as dp
from computations.held_shift import defect_tops, front_rate

CLOSED = dp.closed_strips(dp.STRIP)


def test_defect_step_against_held_map() -> None:
    """The defect stepped as two 64-bit words, and as a Python integer, gives the tops of `held_shift.defect_tops`, which
    steps the whole integer with the tail repeated and compares it with the ring evolution of the tail."""
    rng = random.Random(1)
    for _ in range(12):
        p, state = rng.randrange(1, 14), rng.randrange(4)
        head = rng.getrandbits(p)
        tops = defect_tops(head, p, dp.ETHER[state], 7, 120)
        offset = (-p) % 7  # the tail starts at cell p: cell j is ring cell j - p
        D = head ^ dp.background(state, offset, 0, p)
        lo, hi = np.array([D], dtype=np.uint64), np.zeros(1, dtype=np.uint64)
        for t in range(120):
            assert dp.top(D) == tops[t] == int(dp.tops128(lo, hi)[0])
            D = dp.defect_step(D, state + t, offset, 200)
            lo, hi = dp.step128(lo, hi, state + t, offset)
            assert int(lo[0]) | (int(hi[0]) << 64) == D


def test_closed_strips() -> None:
    """No closed strip of 12 cells or fewer; at 13 cells 1,915, at one residue, with the phase counts of the mirror
    `background_halves.wall_set` beside the ether up to a rotation of the phases; and a defect that lies in one keeps its
    top at or below the strip's cell over 60 steps, whatever lies below it."""
    assert not dp.closed_strips(12).any()
    assert int(CLOSED.sum()) == 1915 and [int(CLOSED[:, r].sum()) for r in range(7)].count(0) == 6
    ours = [int(CLOSED[a].sum()) for a in range(4)]
    ether = [ring for ring in bh.rings(4) if len(ring) == 7][0]
    mirror = [int(bh.wall_set(ether, 4, 3, 13)[a].sum()) for a in range(4)]
    assert any(ours == mirror[k:] + mirror[:k] for k in range(4))
    rng = random.Random(2)
    for _ in range(25):
        a = rng.randrange(4)
        r = int(np.flatnonzero(CLOSED[a].any(axis=1))[0])
        strip = int(rng.choice(np.flatnonzero(CLOSED[a, r])))
        offset = rng.randrange(7)
        c = 40 + ((r - 40 - offset) % 7)  # a cell with (c + offset) mod 7 = r
        D = (strip << (c - dp.STRIP + 1)) | rng.getrandbits(c - dp.STRIP + 1)
        assert dp.closed_cell_int(D, a, offset, CLOSED) == c
        for t in range(60):
            D = dp.defect_step(D, a + t, offset, 200)
            assert dp.top(D) <= c


def test_census_against_direct_runs() -> None:
    """Every head of 6 cells at two alignments is settled; a repeat is a repeat of the integer run, and a head settled
    by a closed strip keeps its top at or below the bound for 150 more steps."""
    for phase, offset in ((0, 0), (3, 5)):
        r = dp.census(6, phase, offset, 4096, CLOSED)
        assert (r["settled"] >= 0).all() and not r["overflow"].any()
        for d in range(0, 64, 5):
            D, history = d, [d]
            for t in range(int(r["settled"][d]) + 150):
                D = dp.defect_step(D, phase + t, offset, 260)
                history.append(D)
                assert dp.top(D) <= r["bound"][d]
            s = int(r["settled"][d])
            assert max(dp.top(x) for x in history[:s + 1]) == r["top"][d]
            if r["cell"][d] < 0:
                assert history[s] == history[s - int(r["period"][d])] and r["period"][d] % 4 == 0
            else:
                assert dp.closed_cell_int(history[s], phase + s, offset, CLOSED) == r["cell"][d]


def test_local_entry_is_sound() -> None:
    """A word that `local_entry` settles keeps its top at or below the strip's cell, measured from the word, whatever
    cells lie below it, here random cells over random depths down to the held wall."""
    rng = random.Random(3)
    n, phase, offset = 12, 1, 2
    words = np.arange(1 << (n - 1), 1 << n, dtype=np.uint64)  # (2^(n-1),)
    when = dp.local_entry(words, phase, offset, CLOSED)
    settled = np.flatnonzero(when >= 0)
    assert 0 < len(settled) < len(words)
    for i in rng.sample(settled.tolist(), 6):
        w, s = int(words[i]), int(when[i])
        D = w
        for t in range(s):
            D = dp.defect_step(D, phase + t, offset, 200)
        c = dp.closed_cell_int(D, phase + s, offset, CLOSED)
        assert c - dp.STRIP + 1 >= s
        for depth in (0, 5, 20):
            below = rng.getrandbits(depth) if depth else 0
            E = (w << depth) | below  # the word raised by `depth` cells, random cells under it
            off = (offset - depth) % 7
            for t in range(s + 80):
                E = dp.defect_step(E, phase + t, off, 260)
                if t + 1 >= s:
                    assert dp.top(E) <= c + depth


def test_window_automaton() -> None:
    """`front_graph` is the automaton of `held_shift.front_rate`: the longest walk of 2,500 steps gains the same at
    window 5. Karp's largest mean gain is 0.28 there, attained on the cycle it returns, and the longest walk per step
    lies between it and it plus the number of nodes over the steps."""
    src, dst, gain, nodes = dp.front_graph(5)
    rounds = 2500
    value = np.zeros(nodes, dtype=np.int64)  # (nodes,)
    for _ in range(rounds):
        step = value.copy()
        np.maximum.at(step, dst, value[src] + gain)
        value = step
    assert value.max() / rounds == front_rate(dp.ETHER, 7, 5, rounds)
    rate, cycle = dp.max_mean_gain(src, dst, gain, nodes)
    assert abs(rate - 0.28) < 1e-12
    edge = {(int(s), int(d)): int(g) for s, d, g in zip(src, dst, gain)}
    total = sum(edge[(cycle[i], cycle[(i + 1) % len(cycle)])] for i in range(len(cycle)))
    assert abs(total / len(cycle) - rate) < 1e-12
    assert rate <= value.max() / rounds <= rate + nodes / rounds
    used = dp.realized_edges(5, 20, 60, np.random.default_rng(0), 4)
    assert used and used <= set(edge)
