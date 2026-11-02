"""The channel ladder and the channel-constrained C3 search against independent constructions on small widths."""

from __future__ import annotations

import math

import numpy as np

from computations import channel_ladder as cl
from computations import channel_left as cle
from computations.game import component_periods
from computations.limit_windows import limit_sets as plain_limit_sets
from computations.limit_windows import window_moves


def test_ladder_against_full_limit() -> None:
    """At widths 6 to 8 the limit sets widened cell by cell from width 4 equal those computed from all 2^W windows by
    iterating images (`limit_windows.limit_sets`), at every phase, for the three words of period four."""
    for word in ("0001", "0011", "0111"):
        ladders = cl.limit_sets(word, [6, 7, 8], base=4, progress=False)
        for width in (6, 7, 8):
            plain = plain_limit_sets(word, window_moves(width))
            for k in range(4):
                assert np.array_equal(ladders[width].sets[k], plain[k]), (word, width, k)


def brute_words(ladder: cl.Ladder, reads: tuple[int, ...], periods: int) -> list[int]:
    """The distinct words of readings of the plays of the limit set from phase 0, over 1 .. `periods` periods, by
    following (word, window) pairs one step at a time, cell by cell."""
    block, width = ladder.block, ladder.width
    members = [set(s.tolist()) for s in ladder.sets]
    moves = {}  # (phase, window) -> the two windows after one step, cell by cell
    for k, ch in enumerate(block):
        for w in members[k]:
            after = []
            for free in (0, 1):
                cells = [int(ch)] + [(w >> j) & 1 for j in range(width)] + [free]  # columns 0 .. W + 1
                after.append(sum((cells[x - 1] ^ (cells[x] | cells[x + 1])) << (x - 1) for x in range(1, width + 1)))
            assert set(after) <= members[(k + 1) % len(block)]  # the limit set is closed under moves
            moves[k, w] = after
    pairs = {("", w) for w in members[0]}
    counts = []
    for _ in range(periods):
        for k in range(len(block)):
            pairs = {(text + str(w & 1) if k in reads else text, after) for text, w in pairs for after in moves[k, w]}
        counts.append(len({text for text, _ in pairs}))
    return counts


def automaton_words(ladder: cl.Ladder, reads: tuple[int, ...], periods: int) -> list[int]:
    """The same counts from the subset automaton of the whole limit set, period by period: paths from its start."""
    nodes = np.arange(ladder.succ.shape[0])
    start, word, successors = cl.period_graph(ladder, nodes, reads)
    states, sources, targets, _, complete = cl.subset_automaton(word, successors, [np.arange(start.size)],
                                                               progress=False)
    assert complete
    vector = np.zeros(states, dtype=np.int64)  # (states,)
    vector[0] = 1
    counts = []
    for _ in range(periods):
        nxt = np.zeros(states, dtype=np.int64)  # (states,)
        np.add.at(nxt, targets, vector[sources])
        vector = nxt
        counts.append(int(vector.sum()))
    return counts


def test_word_counts_against_brute_force() -> None:
    """The output words of 1 to 8 periods from the limit set at width 6, counted by brute force, equal the paths of the
    subset automaton, for the white readings and for column 1 at every phase."""
    ladder = cl.limit_sets("0001", [6], base=6, progress=False)[6]
    for reads in (cl.white_reads("0001"), (0, 1, 2, 3)):
        assert automaton_words(ladder, reads, 8) == brute_words(ladder, reads, 8)


def test_classes_against_game() -> None:
    """The components with a move, their cyclic periods and whether the readings mix in a class equal those of
    `game.component_periods` on the full graph of 2^W windows, which reads column -1 at every phase."""
    for word, width in (("0001", 8), ("0011", 7)):
        ladder = cl.limit_sets(word, [width], base=width, progress=False)[width]
        mine = sorted((c.nodes.size, c.cycle, not c.passes) for c in cl.classes(ladder, cl.white_reads(word)))
        theirs = sorted((size, cycle, mixed) for size, cycle, _, mixed in component_periods(word, width))
        assert mine == theirs


def test_growth_against_plain_construction() -> None:
    """The growth of the largest component at width 10 equals a plain subset construction with dense eigenvalues, and
    the value the entry quotes."""
    ladder = cl.limit_sets("0001", [10], base=10, progress=False)[10]
    reads = cl.white_reads("0001")
    comp = cl.classes(ladder, reads)[0]
    growth = cl.component_growth(ladder, comp, reads, progress=False)
    assert growth.complete and math.isclose(growth.high, cl.simple_growth(ladder, comp, reads), rel_tol=1e-6)
    assert math.isclose(growth.high, 1.39053, abs_tol=1e-5)


def test_channel_census_against_naive() -> None:
    """With the channel at width 9, the census of halves of up to 8 cells equals `run_half` on every half, the branch
    counts equal the allowed words, with and without the kit's no11_0001, and the minimal automaton allows the same
    words as the unminimized one; with no11 no word reads 1 at phase 1 in two consecutive periods."""
    ladder = cl.limit_sets("0001", [9], base=9, progress=False)[9]
    full = cle.channel_dfa(ladder)
    small = cle.minimize(full)
    support = 8
    for phase in range(4):
        assert cle.count_words(full, "0*01", phase, 12) == cle.count_words(small, "0*01", phase, 12)
        for channel in (small, cle.with_no11(small), None):
            latest, branches = cle.tree_failures(channel, "0001", support, phase)
            fails = [cle.run_half(channel, "0001", u, phase, 200) for u in range(1 << support)]  # (2^support,)
            assert latest == [max(fails[1 << (m - 1):1 << m]) for m in range(1, support + 1)]
            assert branches == [sum(f >= m for f in fails[:1 << m]) for m in range(1, support + 1)]
            assert branches == cle.count_words(channel, "0*01", phase, support)
    paired = cle.with_no11(small)
    for state in range(paired.phase.size):
        if paired.phase[state] == 1 and paired.delta[state, 1] >= 0:
            later = {int(paired.delta[state, 1])}
            for _ in range(3):
                later = {int(paired.delta[x, v]) for x in later for v in (0, 1) if paired.delta[x, v] >= 0}
            assert all(paired.delta[x, 1] < 0 for x in later)


def test_constrained_entropy_against_component_growth() -> None:
    """At width 9 the entropy of the column -1 sequences that the kit's pattern for 0001 and the minimized whole-graph
    automaton allow, per period, equals log2 of the growth of the largest component by the plain per-period subset
    construction (`simple_growth`), a different automaton and a dense eigenvalue."""
    ladder = cl.limit_sets("0001", [9], base=9, progress=False)[9]
    reads = cl.white_reads("0001")
    channel = cle.minimize(cle.channel_dfa(ladder))
    comp = cl.classes(ladder, reads)[0]
    assert math.isclose(4 * cle.entropy(channel, "0*01"), math.log2(cl.simple_growth(ladder, comp, reads)),
                        abs_tol=1e-5)
    assert cle.entropy(None, "0*01") == 0.25


def test_wall_component_at_16() -> None:
    """Beside 0001 at width 16 the one terminal component of 109 nodes passes the class test, and its windows hold the
    kit's wall states on columns 4 to 16."""
    ladder = cl.limit_sets("0001", [16], base=8, progress=False)[16]
    comps = cl.classes(ladder, cl.white_reads("0001"))
    terminal = [c for c in comps if c.terminal]
    assert [(c.nodes.size, c.cycle, c.passes) for c in terminal] == [(109, 8, True)]
    assert cl.kit_wall_cells(ladder, terminal[0])
    assert not comps[0].terminal and not comps[0].passes
