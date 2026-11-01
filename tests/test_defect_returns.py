"""Returns of a real defect to its own top window, the bottom of the walled defect, and the Nerode count: the recorded
return against `defect_potential.defect_step` and `held_shift.defect_tops` cell by cell, the cycle counts against a
hand count, the bottoms and highest tops against direct runs, and the class count against a dictionary of outcome
vectors."""

from __future__ import annotations

import random

import numpy as np

from computations import defect_potential as dp
from computations import defect_returns as dr
from computations.held_shift import defect_tops

CLOSED = dp.closed_strips(dp.STRIP)


def test_recorded_return() -> None:
    """Head 0x8f7ff206dd at phase 3, offset 0: the defect has top 52 at step 112 and top 66 at step 272, with the same
    phase, the same residue of the top modulo 7 and the same 24 actual cells at the top, the top stays at least 50 in
    between, and it enters a closed strip first at step 354. The stepping agrees with `defect_step` cell by cell and
    with the tops of `held_shift.defect_tops`, which steps the whole integer with the ether tail from cell 42 on."""
    D0, phase, offset = 0x8F7FF206DD, 3, 0
    p = 42  # the tail starts at cell 42 = 0 mod 7, so offset 0
    head = D0 ^ dp.background(phase, offset, 0, p)
    whole = defect_tops(head, p, dp.ETHER[phase], 7, 273)
    D, trace = D0, []
    for t in range(355):
        assert (dp.closed_cell_int(D, phase + t, offset, CLOSED) >= 0) == (t == 354)
        if t <= 272:
            assert dp.top(D) == whole[t]
        trace.append(D)
        E = dr.step(D, phase + t, offset)
        assert E == dp.defect_step(D, phase + t, offset, 400)
        D = E
    j, i = 112, 272
    assert (dp.top(trace[j]), dp.top(trace[i])) == (52, 66)
    assert (i - j) % 4 == 0 and (66 - 52) % 7 == 0
    cells = [[((trace[s] >> (dp.top(trace[s]) - c)) & 1) ^ dp.ether_cell(phase + s, dp.top(trace[s]) - c + offset)
              for c in range(24)] for s in (j, i)]
    assert cells[0] == cells[1]
    assert min(dp.top(d) for d in trace[j:i + 1]) == 50
    assert dr.first_return(trace[:354], dr.window_keys(trace[:354], phase, offset, 24)) == (j, i)
    assert dr.example(24, 4, 40, 2000, 7) == (D0, phase, offset, j, i, 354)


def test_cycle_counts() -> None:
    """Three passes through one cycle of three window states with the top rising by one per step: the largest gain is
    6, first from step 0 to 6, and the passes in a row number 3; a stretch broken by a step near the wall restarts."""
    trace = [1 << (40 + t) for t in range(9)]
    keys: list[tuple[int, int, int] | None] = [(0, 0, t % 3) for t in range(9)]
    assert dr.best_return(trace, keys) == (6, 0, 6)
    assert dr.back_to_back(trace, keys) == 3
    assert dr.first_return(trace, keys) == (0, 3)
    keys[2] = None
    assert dr.best_return(trace, keys) == (3, 3, 6)
    assert dr.first_return(trace, keys) == (3, 6)


def test_bottoms_against_direct_runs() -> None:
    """The bottom words of `bottoms` against `defect_step` on every defect of 6 cells at two alignments, the spread of
    bottoms against a dictionary grouping, and the actual cell 0 against x'(0) = x(0) xor x(1)."""
    m, t_max = 2, 4
    for phase, offset in ((1, 3), (2, 6)):
        b = dr.bottoms(m, t_max, phase, offset)  # (t_max + 1, 2^(m + t_max))
        groups: dict[int, set[int]] = {}
        for D in range(1 << (m + t_max)):
            E = D
            for t in range(t_max + 1):
                assert b[t, D] == E & 3
                x = E ^ dp.background(phase + t, offset, 0, 4)
                E2 = dp.defect_step(E, phase + t, offset, 40)
                x2 = E2 ^ dp.background(phase + t + 1, offset, 0, 4)
                assert x2 & 1 == (x & 1) ^ ((x >> 1) & 1)
                E = E2
            if D < 1 << (m + 3):
                groups.setdefault(D >> 2, set()).add(int(b[3, D]))
        sizes = [len(v) for v in groups.values()]
        assert dr.bottom_spread(b[3], m, 3, 3) == (max(sizes), float(np.mean([s == 1 for s in sizes])))


def test_highest_tops_and_classes() -> None:
    """`highest_tops` against direct runs on a sample of defects, and `nerode_classes` against a dictionary of
    outcome vectors on a random table, read from both ends."""
    tops = dr.highest_tops(6, 60)  # (28, 64)
    rng = random.Random(3)
    for a in (5, 22):
        for D in rng.sample(range(64), 6):
            E, best = D, dp.top(D)
            for t in range(60):
                E = dp.defect_step(E, divmod(a, 7)[0] + t, a % 7, 100)
                best = max(best, dp.top(E))
            assert tops[a, D] == best
    table = np.random.default_rng(5).integers(0, 2, size=(2, 1 << 6))  # (2, 64)
    for low in (True, False):
        vectors = set()
        for q in range(8):
            words = [q | (s << 3) if low else s | (q << 3) for s in range(8)]
            vectors.add(tuple(int(table[r, w]) for r in range(2) for w in words))
        assert dr.nerode_classes(table, 3, 3, low) == len(vectors)
