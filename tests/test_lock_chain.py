"""Tests of computations.lock_chain: its traps, walls, chains and Lean generators against direct runs with `step`, the
finite game, forward and backward searches, and the text of the repository's Lean files."""

from __future__ import annotations

import re
import numpy as np
import pytest

from computations import game
from computations.cyclic_words import least_period, least_rotation
from computations.rule30 import step
from references import ROOT, lean_states, packed_fields


def test_lock_backgrounds() -> None:
    """`lock_chain.lock_backgrounds` against `space_time_periodic`: at period 8 every locked window of 13 cells leads to
    the kit's ether, of 7 cells, one of the backgrounds of `backgrounds(8)`, and the period of each lock's chain is a
    cycle of `column_map`, the map built from the rule without the chain's code."""
    from computations import lock_chain
    from computations import space_time_periodic as stp

    found = lock_chain.survey([8], 13)
    backgrounds = lock_chain.lock_backgrounds(found)
    assert set(backgrounds) == {8} and set(backgrounds[8]) == {7}
    ends, reach = backgrounds[8][7]
    assert ends == set(found) and len(ends) == 8 and len(reach) == 8
    assert 7 in {length for length, _, _ in stp.backgrounds(8)}
    f = stp.column_map(8)  # (4^8,)

    def bits(word: str) -> int:
        return int(word[::-1], 2)  # bit ph is the letter at phase ph

    for block, entries in found.items():
        for columns, values in entries:
            assert stp.ring_period(lock_chain.background_row(columns[-1] if columns else block, values), 8) == 4
            _, cycle = lock_chain.chain_cycle(columns[-1] if columns else block, values)
            for i in range(len(cycle)):
                right, here, left = cycle[i], cycle[(i + 1) % len(cycle)], cycle[(i + 2) % len(cycle)]
                assert int(f[bits(here) << 8 | bits(right)]) == bits(left) << 8 | bits(here)


def test_lock_chain() -> None:
    """`lock_chain` against a step of the rule, the game and the kit. `left_column` inverts `step` on random columns;
    the bottom components of the locked nodes of 0000011101, 0011111101 and 0000000101 at width 13 have columns 1 .. 5,
    1 .. 4 and 1 .. 7 fixed by the phase, the last repeating 0 1^9, and `chain` from it, white at its white phase, gives
    the others and the block; the blocks of period 8 with a locked node at width 13 are the chain of 0 1^7 at distances
    0 to 7; that chain is the kit's ether from distance 8, and the bottom components of 01110111 at width 13 are the
    kit's wall states, read from its source; from the wall, the white phase of 0 1^8 finds cell 1 white and then black,
    as an exact run from the wall does, and those of 0 1^7 and 0 1^9 find it white. The kit's trap for 001 is the chain
    of its column 38; `is_lock` agrees with `locks.lock_info` on the wall and fails once one node is dropped, and passes
    the chain locks of 001 modulo 15 and of 001011 modulo 12."""
    from computations import lock_chain, locks
    rng = np.random.default_rng(11)
    for _ in range(50):
        period = int(rng.integers(2, 13))
        column = "".join(map(str, rng.integers(0, 2, period).tolist()))
        right = "".join(map(str, rng.integers(0, 2, period).tolist()))
        left = lock_chain.left_column(column, right)
        for ph in range(period):
            row = int(left[ph]) | int(column[ph]) << 1 | int(right[ph]) << 2  # bit 0 is the left cell
            assert (step(row) >> 1) & 1 == int(column[(ph + 1) % period])
    for block, frozen in (("0000011101", 5), ("0011111101", 4), ("0000000101", 7)):
        components = lock_chain.frozen_columns(block, 13)
        assert components
        for _, columns in components:
            assert len(columns) == frozen and least_rotation(columns[-1]) == "0111111111"
            assert lock_chain.chain(columns[-1], "0" * 10, frozen) == columns[::-1] + [block]
    seeds, placed = lock_chain.classify(lock_chain.survey([8], 13), 26)
    assert seeds == {"01111111": ["00000000"]}
    chain8 = [least_rotation(column) for column in lock_chain.chain("01111111", "0" * 8, 7)]
    assert {block: set(entries) for block, entries in placed.items()} == {
        block: {("01111111", distance)} for distance, block in enumerate(chain8)}
    assert lock_chain.ether_from("01111111", "0" * 8, 8, 21)
    wall = lean_states("wallStates")
    components = lock_chain.bottom_components("01110111", 13)
    assert len(components) == 2
    for members in components:
        assert {(((int(x) >> 13) - 2) % 4, int(x) & 8191) for x in members} == wall
    assert lock_chain.wall_returns(9, 11, 3) == ["0", "1", "01"]
    assert lock_chain.wall_returns(8, 11, 12) == ["0"] * 12 == lock_chain.wall_returns(10, 11, 12)
    cells = 200
    for period, returns in ((8, [0, 0, 0]), (9, [0, 1]), (10, [0, 0, 0])):
        row = sum(1 << j for j in range(2, cells, 2))  # bit j is cell j, bit 0 the column: the wall
        seen = []
        for t in range(len(returns) * period + 1):
            row = (row & ~1) | int(t % period != 0)
            if t and t % period == 0:
                seen.append((row >> 1) & 1)
            row = step(row) & ((1 << cells) - 1)
        assert seen == returns
    seed, _, rebuilt, single, least = lock_chain.t001_as_chain()
    assert least_rotation(seed) == "000001011111111111101" and rebuilt and single and least == 9
    block, nodes = lock_chain.chain_lock("01111111", 5, 8)
    locked, _ = locks.lock_info(block, 13)  # (8 2^13,)
    assert block == "01110111" and all(locked[ph << 13 | window] for ph, window in nodes)
    assert lock_chain.is_lock(block, nodes, 13) and not lock_chain.is_lock(block, nodes[1:], 13)
    for seed, distance, word in (("000010111111111", 47, "001"), ("000111111111", 24, "001011")):
        block, nodes = lock_chain.chain_lock(seed, 5, distance)
        assert least_rotation(block[:len(word)]) == word and lock_chain.is_lock(block, nodes, distance + 5)


def test_word_traps(monkeypatch: pytest.MonkeyPatch) -> None:
    """The traps of `WordTraps.lean` and `NineTraps.lean` are the entries that `lock_chain.lean_trap` prints (all of
    `WordTraps`) and `lock_chain.lean_nine` prints (restricted to the distances 1 and 21, the first and the last), and
    their packed tables, read back from the Lean sources, pass the modules' check by `step`: each listed successor is
    the window one step of the rule later, beside the block at the label's phase, with the label one more, and at a
    white phase the first cell is the label's bit of `u`; checked for every trap of `WordTraps` and for `nine1`,
    `nine21` and `trap001010011` of `NineTraps`."""
    import sys
    from computations import lock_chain
    word_traps = (ROOT / "Rule30Open" / "Columns" / "WordTraps.lean").read_text(encoding="utf-8")
    nine_traps = (ROOT / "Rule30Open" / "Columns" / "NineTraps.lean").read_text(encoding="utf-8")
    digits = sys.get_int_max_str_digits()
    sys.set_int_max_str_digits(0)  # the packed tables have thousands of digits
    try:
        names = [entry[0] for entry in lock_chain.TRAPS + lock_chain.NATURAL[:1]]
        for name in names:
            assert lock_chain.lean_trap(name) in word_traps
        distances = [d for d in lock_chain.nine_distances() if d]
        for kept in ([distances[0]], [distances[-1]]):
            monkeypatch.setattr(lock_chain, "nine_distances", lambda kept=kept: [0] + kept)
            assert lock_chain.lean_nine() in nine_traps
        monkeypatch.undo()
        assert lock_chain.lean_trap("trap001010011") in nine_traps
        sources = [(name, word_traps) for name in names]
        sources += [(f"nine{d}", nine_traps) for d in (distances[0], distances[-1])]
        sources += [("trap001010011", nine_traps)]
        for name, lean in sources:
            body = lean.split(f"def {name} : WTrap :=", 1)[1].split("}", 1)[0]
            fields = dict(re.findall(r"(\w+) := (\[[^\]]*\]|\d+)", body))
            block = [cell.strip() == "true" for cell in fields["b"].strip("[]").split(",")]
            cells, modulus, n, lb, ib, u, windows, labels, nexts = (
                int(fields[key]) for key in ("K", "m", "n", "lb", "ib", "u", "R", "L", "S"))
            period, mask = len(block), (1 << cells) - 1
            assert modulus % period == 0
            window_of, label_of = packed_fields(windows, cells, n), packed_fields(labels, lb, n)
            next_of = packed_fields(nexts, ib, 2 * n)
            for i in range(n):
                window, label = window_of[i], label_of[i]
                here = int(block[label % period])
                assert label < modulus and (here or (window & 1) == (u >> label) & 1)
                for free in (0, 1):
                    j = next_of[2 * i + free]
                    row = here | window << 1 | free << (cells + 1)  # bit 0 the block's column, bit x cell x
                    assert j < n and window_of[j] == (step(row) >> 1) & mask
                    assert label_of[j] == (label + 1) % modulus
    finally:
        sys.set_int_max_str_digits(digits)


def test_trap_entry() -> None:
    """`lock_chain.entry_steps`, which steps packed rows, against a direct run of each half with `step` on one integer,
    checked against the trap's states at every step, for the traps of 01, 001011 and 01111 (whose 107 cells span two
    words) and the halves of up to four cells, from every phase."""
    from computations import lock_chain
    for name in ("trap01", "trap001011", "trap01111"):
        word, cells, states = lock_chain.trap_states(name)
        period, mask = len(word), (1 << cells) - 1
        halves = list(range(16))
        for phase in range(period):
            got = lock_chain.entry_steps(name, halves, phase, 400)  # (16,)
            for half, first in zip(halves, got.tolist(), strict=True):
                row, found = half << 1, -1  # bit 0 is the driven column, bit x cell x
                for t in range(400):
                    row = (row & ~1) | int(word[(t + phase) % period])
                    if ((t + phase) % period, (row >> 1) & mask) in states:
                        found = t
                        break
                    row = step(row)
                assert first == found


def test_natural_trap() -> None:
    """`lock_chain.natural_trap` rebuilds the kit's trap for 001: from the empty right half, the closure of the true
    window of 47 cells with the phase counted modulo 21 is, at step 1,500, exactly the states of `t001`, read from the
    kit's source, as pairs of the phase modulo 21 and the window; and two values of column 1 at one white phase are
    rejected, while at a black phase they are not."""
    from computations import lock_chain
    found = lock_chain.natural_trap("001", 0, [1500], [47], [21])
    assert found is not None and found[1:] == (47, 21, 815)
    row = 0
    for t in range(1500):
        row = ((row << 1) | int("001"[t % 3])) ^ (row | (row >> 1))
    nodes = lock_chain.closure("001", 21, 47, 1500, row & ((1 << 47) - 1), 20000)
    kit = {(label % 21, strip) for strip, label in lock_chain.t001_states()}
    shifts = [d for d in range(0, 21, 3) if {((ph + d) % 21, w) for ph, w in nodes} == kit]
    assert len(shifts) == 1
    assert not lock_chain.fixes_left("001", {(3, 0), (3, 1)}) and lock_chain.fixes_left("001", {(2, 0), (2, 1)})


def test_period_nine_wall() -> None:
    """The wall of period 9: from the random start that `NATURAL` names, a run of 001011111 is inside a closed set of
    233 windows of 43 cells, with the phase modulo 9, that fixes column 1 at the white phases, and enters it at step
    6,084 by a direct run with `step`; its chain holds 21 blocks of period 9 at the distances `nine_distances` gives and
    repeats from distance 10 with spatial period 135 in the background that the chain of 0 1^8 enters, columns of the
    two cycles agreeing as sets, each column there being the one 15 places right of it shifted by 8 steps; and the trap
    carried to distance 16 is a lock by `is_lock`."""
    from computations import lock_chain, right_half
    name, word, start, time, cells, modulus = lock_chain.NATURAL[0]
    assert start == right_half.random_starts(30, 64)[13]
    assert lock_chain.natural_trap(word, start, [time], [cells], [modulus]) == (time, cells, modulus, 233)
    _, _, states = lock_chain.trap_states(name)
    row, entered = start << 1, -1
    for t in range(time):
        row = (row & ~1) | int(word[t % 9])
        if (t % 9, (row >> 1) & ((1 << cells) - 1)) in states:
            entered = t
            break
        row = step(row)
    assert entered == 6084
    assert lock_chain.nine_distances() == list(range(19)) + [20, 21]
    values = "".join(str((lock_chain.tables(name)["first"] >> ph) & 1) if word[ph] == "0" else "0" for ph in range(9))
    assert values == "010000000"
    begin, cycle = lock_chain.chain_cycle(word, values)
    begin8, cycle8 = lock_chain.chain_cycle("011111111", "0" * 9)
    assert (begin, len(cycle), begin8, len(cycle8)) == (10, 135, 8, 135) and set(cycle) == set(cycle8)
    columns = lock_chain.chain(word, values, 160)
    assert all(columns[d + 15] == columns[d][8:] + columns[d][:8] for d in range(10, 145))
    t16 = lock_chain.carried(name, 16)
    assert t16["word"] == "000101011" and lock_chain.is_lock(t16["word"], t16["states"], t16["cells"])


def test_white_lock() -> None:
    """`lock_chain.white_lock`: the white right half driven by 001 locks column 1 with period 21 from every phase and is
    then inside a trap of 815 windows of 47 cells modulo 21, the size of the kit's `t001` (the search over cell counts
    restricted to 47; the full search, 16 to 64, is the entry's reproduce command); driven by 0001 from phase 0
    it locks with period 4 inside 109 windows of 16 cells; driven by 01 it does not lock within 20,000 steps; and for
    001 from phase 1 column 1 computed by `step` repeats with period 21 at the white times over the second half."""
    from computations import lock_chain
    for phase in range(3):
        lock, last, trap = lock_chain.white_lock("001", phase, 20000, range(47, 48))
        assert lock == 21 and last < 1000 and trap is not None and trap[1:] == (47, 21, 815)
    lock, _, trap = lock_chain.white_lock("0001", 0, 20000)
    assert lock == 4 and trap is not None and trap[1:] == (16, 4, 109)
    assert lock_chain.white_lock("01", 0, 20000) == (0, None, None)
    turned, row, column = "010", 0, []
    for t in range(20000):
        row = (row & ~1) | int(turned[t % 3])
        column.append((row >> 1) & 1)
        row = step(row)
    assert all(column[t] == column[t + 21] for t in range(10000, 20000 - 21) if turned[t % 3] == "0")


def test_period_two_fourteen() -> None:
    """A second trap for 01: the random start that `NATURAL` names, driven by 01, is at step 12,000 inside the closure
    of its window of 31 cells with the phase modulo 14, 225 states that fix column 1 at the white phases, and none of
    29 or 30 cells is a trap; the same states, up to the labels, are the 6-cell lock of 0^4 1 0 1^8, of period 14,
    carried 25 columns by `chain_lock`, a lock by `is_lock`; and its column 1 at the white phases has black values
    two white phases apart."""
    from computations import lock_chain, right_half
    name, word, start, time, cells, modulus = lock_chain.NATURAL[2]
    assert start == right_half.random_starts(300, 64)[79]
    assert lock_chain.natural_trap(word, start, [time], list(range(29, 32)), [modulus]) == (time, 31, 14, 225)
    block, nodes = lock_chain.chain_lock("00001011111111", 6, 25)
    assert least_rotation(block[:2]) == "01" and len(nodes) == 225 and lock_chain.is_lock(block, nodes, 31)
    t = lock_chain.tables(name)
    windows = {window for _, window in t["states"]}
    assert windows == {window for _, window in nodes}
    gate = [(t["first"] >> label) & 1 for label in range(0, 14, 2)]  # column 1 at the white labels
    blacks = [i for i, bit in enumerate(gate) if bit]
    assert any((b - a) % 7 == 2 for a in blacks for b in blacks)


def test_coin_entry() -> None:
    """`lock_chain.coin_entry`: the halves and phases with support in cells 1 to 6 whose windows are already inside
    `trap001011` when the coin takes over at step 200 are exactly those that `entry_steps`, with the rule throughout,
    finds inside by step 200, and with the coin no other enters within 2,000 steps."""
    from computations import lock_chain
    coin = lock_chain.coin_entry("trap001011", 6, 200, 2000)  # (384,)
    real = np.concatenate([lock_chain.entry_steps("trap001011", list(range(64)), phase, 201)
                           for phase in range(6)])  # (384,)
    assert set(np.flatnonzero(coin == 0).tolist()) == set(np.flatnonzero(real >= 0).tolist())
    assert (coin == 0).sum() == 3 and (coin > 0).sum() == 0


def test_white_runs() -> None:
    """`lock_chain.white_runs`: under 001011111 the white half's runs from the 9 phases are, at step 100, the six that a
    white letter joins to the next phase, and by step 2,100 the runs from phases 3 to 7 agree on columns 1 to 2,000,
    as a direct run with `step` of the runs from phases 3 and 5 shows."""
    from computations import lock_chain
    word = "001011111"
    assert lock_chain.white_runs(word, 100, 2000) == [[0, 1, 2], [3, 4], [5], [6], [7], [8]]
    assert lock_chain.white_runs(word, 2100, 2000) == [[0, 1, 2], [3, 4, 5, 6, 7], [8]]
    windows = []
    for phase in (3, 5):
        row = 0
        for t in range(2100 - phase):
            row = (row & ~1) | int(word[(phase + t) % 9])
            row = step(row)
        windows.append((row >> 1) & ((1 << 2000) - 1))
    assert windows[0] == windows[1]


def test_nine_white() -> None:
    """`NineWhite.lean`: for each run of `lock_chain.WHITE_RUNS`, the row its first part ends on, cut to the cells that
    can reach the window, is what a direct run of 16,384 steps with `step` gives; and the shortest run, the white half
    under 001010011 from phase 7, enters its wall at step 91,086 by a direct run with `step` on one integer (cut every
    1,024 steps to the cells that can still reach the window by then), and at no earlier step."""
    import sys
    from computations import lock_chain
    lean = (ROOT / "Rule30Open" / "Columns" / "NineWhite.lean").read_text(encoding="utf-8")
    digits = sys.get_int_max_str_digits()
    sys.set_int_max_str_digits(0)  # the rows have tens of thousands of digits
    try:
        for prefix, name, phase, total in lock_chain.WHITE_RUNS:
            word, cells, _ = lock_chain.trap_states(name)
            literal = int(re.search(rf"def {prefix}1 : Nat := (\d+)", lean).group(1))
            row = 0
            for t in range(lock_chain.PART):
                row = (row & ~1) | int(word[(t + phase) % 9])
                row = step(row)
            assert (row >> 1) % (1 << (total - lock_chain.PART + cells)) == literal
        word, cells, states = lock_chain.trap_states("trap001010011")
        row, entered = 0, -1
        for t in range(91087):
            if t % 1024 == 0:
                row &= (1 << (cells + 1 + 91087 - t)) - 1  # bit i reaches cell `cells` only after i - cells steps
            row = (row & ~1) | int(word[(t + 7) % 9])
            if ((t + 7) % 9, (row >> 1) & ((1 << cells) - 1)) in states:
                entered = t
                break
            row = step(row)
        assert entered == 91086
    finally:
        sys.set_int_max_str_digits(digits)


def gap_lists(lean: str, prefix: str) -> list[list[tuple[int, int]]]:
    """The entry lists `<prefix>0`, `<prefix>1`, ... of a gap module, read from its source, each a list of (step, state
    index), one per right half of at most eight cells."""
    found = re.findall(rf"def {prefix}(\d+) : List \(Nat × Nat\) := \[\n(.*?)\]", lean, re.S)
    assert [int(phase) for phase, _ in found] == list(range(len(found)))
    return [[(int(a), int(b)) for a, b in re.findall(r"\((\d+), (\d+)\)", body)] for _, body in found]


def test_ten_gap() -> None:
    """`TenGap.lean`: `lean_ten_gap`, restricted to phase 3, is the text of its entries (the kernel checks every list
    of the module); for sampled halves of at most eight cells and every phase, a direct run with `step` (the row with
    the center as bit 0) is, at the step the module lists, in the listed state of the wall `ten0` with the label of its
    phase, and in no state of it at any earlier step; the latest entry is at step 3,042 and the white half's at step
    74."""
    from computations import lock_chain
    lean = (ROOT / "Rule30Open" / "Columns" / "TenGap.lean").read_text(encoding="utf-8")
    assert lock_chain.lean_ten_gap(phases=(3,)) in lean
    entries = gap_lists(lean, "tenGap")
    assert len(entries) == 10 and all(len(es) == 256 for es in entries)
    assert lock_chain.ten_gap_entries(phases=(3,)) == [entries[3]]
    trap = lock_chain.carried("trap0000010001", 0)
    word, states = trap["word"], trap["states"]
    members = set(states)
    for phase in range(10):
        for r in (0, 37, 255):
            when, index = entries[phase][r]
            row = r << 1  # (cells 0 .. ), cell 0 the center
            for t in range(when + 1):
                row = (row & ~1) | int(word[(t + phase) % 10])
                state = ((t + phase) % 10, (row >> 1) & 0xFFFF)
                assert (state in members) == (t == when), (phase, r, t)
                row = step(row)
            assert states[index] == state
    assert max(e[0] for es in entries for e in es) == 3042
    assert max(es[0][0] for es in entries) == 74


def test_wall_gaps() -> None:
    """`WallGaps.lean`: `lean_gap`, restricted to one phase of each wall of `WALL_GAPS` (phase 4 and phase 7), is the
    text of its entries (the kernel checks every list of the module), and each bound is the latest listed entry plus
    16; and for sampled halves of at most eight cells and every phase, a direct run with `step` is, at the listed step,
    in the listed state of the wall with the label of its phase, and in no state of it earlier."""
    from computations import lock_chain
    lean = (ROOT / "Rule30Open" / "Columns" / "WallGaps.lean").read_text(encoding="utf-8")
    for (name, trap, bound, prefix), phase in zip(lock_chain.WALL_GAPS, (4, 7), strict=True):
        assert lock_chain.lean_gap(name, trap, bound, prefix, phases=(phase,)) in lean
        t = lock_chain.carried(name, 0)
        word, states, period = t["word"], t["states"], len(t["word"])
        entries = gap_lists(lean, prefix)
        assert len(entries) == period and all(len(es) == 256 for es in entries)
        assert bound == max(e[0] for es in entries for e in es) + 16
        members = set(states)
        for phase in range(period):
            for r in (0, 101, 255):
                when, index = entries[phase][r]
                row = r << 1  # cell 0 the center
                for u in range(when + 1):
                    row = (row & ~1) | int(word[(u + phase) % period])
                    state = ((u + phase) % period, (row >> 1) & 0xFFFF)
                    assert (state in members) == (u == when), (name, phase, r, u)
                    row = step(row)
                assert states[index] == state


def test_edge_periods() -> None:
    """`lock_chain.edge_periods`: next to the kit's ether, white to the right, the edge column repeats; next to the
    background of period 9 no column near the edge does; for both, the column at the edge, run directly with `step`,
    agrees on whether it repeats with a period up to 64 over the second half of 512 steps."""
    from computations import lock_chain
    t = lock_chain.tables("trap001011111")
    values = "".join(str((t["first"] >> ph) & 1) if t["word"][ph] == "0" else "0" for ph in range(9))
    cases = [(lock_chain.chain("01111111", "0" * 8, 800), 8, True), (lock_chain.chain(t["word"], values, 900), 10, False)]
    for columns, distance, repeats in cases:
        periods = lock_chain.edge_periods(columns, distance, 0, 512)
        assert any(p is not None for p in periods) == repeats
        reach = 512 + 64
        row = sum(int(columns[distance + reach - i][0]) << i for i in range(reach + 1))
        edge = []
        for _ in range(512):
            edge.append((row >> reach) & 1)
            row = step(row)
        tail = edge[256:]
        found = next((p for p in range(1, 65) if tail[p:] == tail[:-p]), None)
        assert found == periods[6]


def test_carried_blocks() -> None:
    """`lock_chain.carried_block`, the block of a carried trap from its chain alone, is the block of the tables that
    `carry` builds, for the period-9 and period-10 walls at distances 0 to 11 and for the first wall of
    `FIFTEEN_DISTANCES` at its listed distance."""
    from computations import lock_chain
    for name in ("trap001011111", "trap0000010001"):
        for distance in range(12):
            assert lock_chain.carried_word(name, distance) == lock_chain.carried(name, distance)["word"]
    wall, distance = lock_chain.FIFTEEN_DISTANCES[0]
    block = lock_chain.carried_block(lock_chain.fifteen_wall(wall), distance)
    assert block == lock_chain.fifteen_tables(wall, distance)["word"]


def test_ten_traps(monkeypatch: pytest.MonkeyPatch) -> None:
    """The wall of period 10: its chain repeats with period 155 from the start, its columns at distances 20 to 28 are
    the nine blocks of period 10 with a locked window of 13 cells (`locks.has_lock`, checked for three of them and three
    other blocks of period 10), and its trap carried to the first, the seventh and the last of the 25 distances of
    `ten_distances` is a lock by `is_lock`, a direct check with the rule, with 100 states; the least natural trap of
    0001110011 is the carried one at distance 7; `lean_ten`, restricted to distances 0 and 7, is text of TenTraps.lean.
    `parse_natural`, `natural_summary` and `wall_chains` read back a saved scan line."""
    from computations import lock_chain, locks
    t = lock_chain.tables("trap0000010001")
    full = t["word"] * (t["modulus"] // len(t["word"]))
    values = "".join(str((t["first"] >> label) & 1) if full[label] == "0" else "0" for label in range(t["modulus"]))
    start, cycle = lock_chain.chain_cycle(full, values)
    assert (start, len(cycle)) == (0, 155)
    columns = lock_chain.chain(full, values, 28)
    near = {least_rotation(c[:least_period(c)]) for c in columns[20:29]}
    assert len(near) == 9 and near <= set(game.necklaces(10))
    others = [b for b in game.necklaces(10) if b not in near]
    assert all(locks.has_lock(b, 13) for b in sorted(near)[::4])
    assert not any(locks.has_lock(b, 13) for b in others[::len(others) // 3][:3])
    distances = lock_chain.ten_distances()
    assert len(distances) == 25 and distances[:4] == [0, 1, 2, 3]
    for d in (distances[0], distances[7], distances[-1]):
        carried = lock_chain.carried("trap0000010001", d)
        assert len(carried["states"]) == 100 and lock_chain.is_lock(carried["word"], carried["states"], 16 + d)
    natural = lock_chain.natural_tables("0001110011", 0, 12000, 23, 10)
    assert natural["states"] == lock_chain.carried("trap0000010001", 7)["states"]
    lean = (ROOT / "Rule30Open" / "Columns" / "TenTraps.lean").read_text(encoding="utf-8")
    for kept in (0, 7):
        monkeypatch.setattr(lock_chain, "ten_distances", lambda kept=kept: [kept])
        assert lock_chain.lean_ten() in lean
    monkeypatch.undo()
    line = "0000010001: column 1 locks for 31 of 31 starts; natural traps [(0, 12000, 16, 10, 100)]"
    rows = lock_chain.parse_natural(line)
    assert rows == {10: [("0000010001", 31, [(0, 12000, 16, 10, 100)])]}
    assert lock_chain.natural_summary(10, rows[10], 1).startswith("period 10: 99 words, 1 lock for some start, 1 have")
    [(size, word, cells, start, spatial, blocks)] = lock_chain.wall_chains(10, rows[10], count=1)
    assert (size, word, cells, start, spatial) == (100, "0000010001", 16, 0, 155)
    assert blocks == {lock_chain.carried("trap0000010001", d)["word"] for d in range(31)
                      if len(lock_chain.carried("trap0000010001", d)["word"]) == 10}


def test_eleven_twelve_traps(monkeypatch: pytest.MonkeyPatch) -> None:
    """The walls of periods 11 to 14: the trap of each in `WALLS` has the size the natural scan reports, the traps that
    `wall_distances` carries within `WALL_DEPTHS` columns are 57, 83, 53 and 101 with distinct blocks none of which is
    the kit's, every tenth of them and the last is a lock by `is_lock`, a direct check with the rule, for its block,
    and `lean_walls`, restricted to the first and to the last of each period, is text of ElevenTraps.lean,
    TwelveTraps.lean, ThirteenTraps.lean and FourteenTraps.lean; the walls of periods 13 and 14 reach the blocks of
    period 13 of the background of 689 cells and of period 14 of that of 728, the cycles their chains repeat with."""
    from computations import lock_chain
    sizes = {name: len(lock_chain.tables(name)["states"]) for period in (11, 12, 13, 14)
             for name in lock_chain.WALLS[period]}
    assert sizes == {"trap00000011011": 313, "trap00110100111": 103, "trap00001101001": 138,
                     "trap001011100111": 119, "trap000110110011": 116, "trap000010011111": 150,
                     "trap0001110010011": 213, "trap00011100101011": 225}
    real = lock_chain.wall_distances
    for period, module, prefix, count in ((11, "ElevenTraps", "el", 57), (12, "TwelveTraps", "tw", 83),
                                          (13, "ThirteenTraps", "th", 53), (14, "FourteenTraps", "fo", 101)):
        found = real(period, lock_chain.WALL_DEPTHS[period])
        assert len(found) == count and len({word for _, _, word in found}) == count
        assert not {word for _, _, word in found} & set(game.kit_blocks(period))
        for name, distance, word in found[::10] + found[-1:]:
            t = lock_chain.carried(name, distance)
            assert t["word"] == word and lock_chain.is_lock(word, t["states"], 16 + distance)
        lean = (ROOT / "Rule30Open" / "Columns" / f"{module}.lean").read_text(encoding="utf-8")
        piece, check = (1 << 16, True) if period >= 13 else (0, False)
        for kept in (found[:1], found[-1:]):
            monkeypatch.setattr(lock_chain, "wall_distances", lambda p, d, kept=kept: kept)
            assert lock_chain.lean_walls(period, lock_chain.WALL_DEPTHS[period], prefix, piece, check) in lean
        monkeypatch.undo()
    for period, length in ((13, 689), (14, 728)):
        t = lock_chain.tables(lock_chain.WALLS[period][0])
        values = "".join(str((t["first"] >> label) & 1) if t["word"][label] == "0" else "0" for label in range(period))
        start, cycle = lock_chain.chain_cycle(t["word"], values)
        background = {least_rotation(c) for c in cycle if least_period(c) == period}
        assert start <= 1 and len(cycle) == length
        assert background == {word for _, _, word in real(period, lock_chain.WALL_DEPTHS[period])}


def test_far_walls(monkeypatch: pytest.MonkeyPatch) -> None:
    """The traps of FarWalls: each carries a wall of `WALLS` past `WALL_DEPTHS` and is a lock by `is_lock`, a direct
    check with the rule, for its block; the blocks are distinct, none is the kit's or a block of another trap module,
    three of them are excluded by no game at width 6, 10 or 14, and all lie in the chain of their wall, which repeats
    with the 60 cells of its background; and `lean_far`, restricted to the first and to the last entry, is text of
    FarWalls.lean."""
    from computations import coverage, lock_chain
    others = {block for block, module in coverage.trap_blocks().items() if module != "FarWalls"}
    words = []
    for period, entries in lock_chain.FAR_WALLS.items():
        for name, distance in entries:
            assert name in lock_chain.WALLS[period] and distance > lock_chain.WALL_DEPTHS[period]
            t = lock_chain.carried(name, distance)
            assert len(t["word"]) == period and lock_chain.is_lock(t["word"], t["states"], 16 + distance)
            words.append(t["word"])
    assert len(words) == len(set(words)) == 12
    assert not set(words) & (set(game.kit_blocks(12)) | others)
    assert all(game.first_width(word, [6, 10, 14]) is None for word in words[::5])
    t = lock_chain.tables("trap001011100111")
    values = "".join(str((t["first"] >> label) & 1) if t["word"][label] == "0" else "0" for label in range(12))
    start, cycle = lock_chain.chain_cycle(t["word"], values)
    assert len(cycle) == 60
    held = {least_rotation(c) for c in lock_chain.chain(t["word"], values, start + len(cycle))}
    assert set(words) <= held
    lean = (ROOT / "Rule30Open" / "Columns" / "FarWalls.lean").read_text(encoding="utf-8")
    entries = lock_chain.FAR_WALLS[12]
    for kept in (entries[:1], entries[-1:]):
        monkeypatch.setattr(lock_chain, "FAR_WALLS", {12: kept})
        assert lock_chain.lean_far() in lean


def test_census_traps(monkeypatch: pytest.MonkeyPatch) -> None:
    """The traps of CensusTraps13, CensusTraps14, CensusTraps15, CensusTrapsLarge and CensusTrapsLarge15: the 971
    blocks are distinct and none is the kit's or a block of another trap module, and a sample of 7 is excluded by no
    game at width 6, 10 or 14. The trap of a census entry is a bottom component of the locked windows of 16 cells of
    its source block, carried by its chain (`component_tables`): for the first entry of CensusTraps13 it has the entry's
    block, is a lock by `is_lock`, a direct check with the rule, is not one of the large ones (3,000 states or fewer),
    and `lean_census`, restricted to that entry, is text of CensusTraps13.lean. The same construction on a block of
    period 8 at 13 cells with the chain carried 3 columns gives a lock by `is_lock` as well."""
    from computations import coverage, lock_chain
    others = {block for block, module in coverage.trap_blocks().items()
              if not module.startswith("CensusTraps") and module != "NaturalTrapsLongLarge"}
    groups = [(13, lock_chain.CENSUS_TRAPS[13]), (14, lock_chain.CENSUS_TRAPS[14]), (15, lock_chain.CENSUS_TRAPS[15]),
              (0, lock_chain.CENSUS_LARGE), (0, lock_chain.CENSUS_LARGE15)]
    words = [block for _, entries in groups for block, *_ in entries]
    assert len(words) == len(set(words)) == 124 + 232 + 569 + 22 + 24
    assert not set(words) & (set(game.kit_blocks(15)) | others)
    assert all(game.first_width(word, [6, 10, 14]) is None for word in words[::160])
    entry = lock_chain.CENSUS_TRAPS[13][0]
    t = lock_chain.census_tables(entry)
    assert t["word"] == entry[0] and len(t["states"]) <= 3000
    assert lock_chain.is_lock(t["word"], t["states"], 16 + entry[3])
    monkeypatch.setattr(lock_chain, "CENSUS_TRAPS", {13: [entry]})
    assert lock_chain.lean_census(13) in (ROOT / "Rule30Open" / "Columns" / "CensusTraps13.lean").read_text(
        encoding="utf-8")
    small = lock_chain.component_tables("01110111", 13, 0, 3)
    assert lock_chain.is_lock(small["word"] * (small["modulus"] // len(small["word"])), small["states"], 16)


def test_missed_traps(monkeypatch: pytest.MonkeyPatch) -> None:
    """`trap_reach` and `miss_tables`: only a share of the nodes of the game of 16 cells reaches the natural traps of
    0010101111111 and 0001101101011, 0.346 and 0.954; for each of these two, the closed set of `miss_tables`, checked
    with `step`, is closed under both values of the cell beyond and apart from the trap, and a right half started in
    it, run with `step` for 3,000 steps, keeps its first cells in it and never enters the trap; and `lean_missed`,
    restricted to the first natural trap, is the text of its entries in MissedTraps.lean. The census traps of
    MissedTraps take 4 s each to build and are left to the module's reproduce command."""
    from computations import lock_chain
    for word, share in (("0010101111111", (0.34, 0.35)), ("0001101101011", (0.95, 0.96))):
        t = lock_chain.extra_tables(word)
        assert share[0] < lock_chain.trap_reach(t) < share[1]
        period = len(word)
        s = lock_chain.miss_tables(t)
        width, states = s["cells"], set(s["states"])
        assert s["word"] == word and s["modulus"] == period and width < t["cells"]
        for label, window in states:
            for free in (0, 1):
                row = step(int(word[label]) | window << 1 | free << (width + 1))
                assert ((label + 1) % period, (row >> 1) & ((1 << width) - 1)) in states
        assert not {(label, window & ((1 << width) - 1)) for label, window in t["states"]} & states
        label, window = s["states"][0]
        trap = set(t["states"])
        row = window << 1  # bit 0 the block's column, bit i column i
        for time in range(3000):
            phase = (label + time) % period
            row = (row & ~1) | int(word[phase])
            assert (phase, (row >> 1) & ((1 << width) - 1)) in states
            assert (phase, (row >> 1) & ((1 << t["cells"]) - 1)) not in trap
            row = step(row)
    monkeypatch.setattr(lock_chain, "MISSED_NATURAL", lock_chain.MISSED_NATURAL[:1])
    monkeypatch.setattr(lock_chain, "MISSED_CENSUS", [])
    text = lock_chain.lean_missed()
    assert text in (ROOT / "Rule30Open" / "Columns" / "MissedTraps.lean").read_text(encoding="utf-8")


def test_trap_reach_lifted() -> None:
    """`trap_reach` at widths below, at and above the trap's own, against a direct search: the nodes of the game,
    built cell by cell with the rule, from which some values of the cell beyond reach a node whose first cells, as many
    as the trap has, form a state with the label modulo the period; on random sets of states of small blocks."""
    import random
    from computations import lock_chain

    def direct(word: str, states: set[tuple[int, int]], cells: int, width: int) -> float:
        p, cut = len(word), min(cells, width)
        wanted = {(label % p, window & ((1 << cut) - 1)) for label, window in states}
        moves = {}
        for phase in range(p):
            for window in range(1 << width):
                column = [int(word[phase])] + [(window >> i) & 1 for i in range(width)]  # columns 0 to width
                ends = []
                for free in (0, 1):
                    c = column + [free]
                    new = [c[i - 1] ^ (c[i] | c[i + 1]) for i in range(1, width + 1)]
                    ends.append(((phase + 1) % p, sum(bit << i for i, bit in enumerate(new))))
                moves[(phase, window)] = ends
        reached = {node for node in moves if (node[0], node[1] & ((1 << cut) - 1)) in wanted}
        grown = True
        while grown:
            grown = False
            for node, ends in moves.items():
                if node not in reached and any(end in reached for end in ends):
                    reached.add(node)
                    grown = True
        return len(reached) / len(moves)

    rng = random.Random(1)
    for _ in range(12):
        word = rng.choice(["001", "0001", "00111", "0101"])
        cells = rng.randint(2, 5)
        states = {(rng.randrange(2 * len(word)), rng.randrange(1 << cells)) for _ in range(rng.randint(1, 4))}
        t = {"word": word, "cells": cells, "states": sorted(states)}
        for width in range(max(cells - 1, 1), cells + 4):
            assert lock_chain.trap_reach(t, width=width) == pytest.approx(direct(word, states, cells, width), abs=1e-12)


def test_t001_coin() -> None:
    """`t001_coin` at 6 and 7 cells against the spectral radius of the coin's step on the nodes outside `t001` cut to
    the width, from the matrix built cell by cell with the rule."""
    from computations import lock_chain

    states = lock_chain.t001_states()
    for width in (6, 7):
        inside = {(label % 3, strip & ((1 << width) - 1)) for strip, label in states}
        outside = [(ph, w) for ph in range(3) for w in range(1 << width) if (ph, w) not in inside]
        index = {node: i for i, node in enumerate(outside)}
        step = np.zeros((len(outside), len(outside)))  # (m, m), the coin's step among the nodes outside
        for (ph, w), i in index.items():
            cells = [int("001"[ph])] + [(w >> k) & 1 for k in range(width)]
            for coin in (0, 1):
                row = cells + [coin]
                new = sum((row[k - 1] ^ (row[k] | row[k + 1])) << (k - 1) for k in range(1, width + 1))
                j = index.get(((ph + 1) % 3, new))
                if j is not None:
                    step[i, j] += 0.5
        radius = float(np.abs(np.linalg.eigvals(step)).max())
        (got_width, factor), = lock_chain.t001_coin((width,))
        assert got_width == width and factor == pytest.approx(radius, abs=1e-6)


def test_apart_closed() -> None:
    """`lock_chain.apart_closed` for the two traps of 001 and for the natural trap and the wall trap of `00001111111`,
    and for `trap001c` against the list of the first two, against the largest closed set computed from the rule on
    integers instead of the successor tables; and the right half of a state of `trap001fifteen`, stepped under Rule 30
    itself, stays in it and out of `t001` for 3,000 steps."""
    from computations import lock_chain

    def step(window: int, center: int, beyond: int, width: int) -> int:
        row = center | window << 1 | beyond << (width + 1)  # bit i is cell i, the column at bit 0
        return (row ^ ((row >> 1) | (row >> 2))) & ((1 << width) - 1)  # bit i - 1: cell i - 1 ^ (cell i | i + 1)

    def closed_apart(a: dict | list[dict], b: dict) -> set:
        period, alive = len(b["word"]), set(b["states"])
        for c in a if isinstance(a, list) else [a]:
            k = min(c["cells"], b["cells"])
            cut = {(label % period, w & ((1 << k) - 1)) for label, w in c["states"]}
            alive = {(label, w) for label, w in alive if (label % period, w & ((1 << k) - 1)) not in cut}
        # each state's two successors, stepped cell by cell once and read again in every round
        after = {(label, w): [((label + 1) % b["modulus"], step(w, int(b["word"][label % period]), z, b["cells"]))
                              for z in (0, 1)] for label, w in alive}
        while True:
            kept = {state for state in alive if all(nxt in alive for nxt in after[state])}
            if kept == alive:
                return alive
            alive = kept

    entries = {(m, n): b for m, n, b in lock_chain.module_entries()}
    t001, fifteen = lock_chain.kit_t001(), entries[("WordTraps", "trap001fifteen")]()
    natural, wall = entries[("NaturalTrapsWalls", "natw00001111111")](), entries[("ElevenTraps", "el0_19")]()
    third = dict(lock_chain.traps001_tables())["trap001c"]
    for a, b in ((t001, fifteen), (fifteen, t001), (natural, wall), (wall, natural), ([t001, fifteen], third)):
        got = {s for s, keep in zip(b["states"], lock_chain.apart_closed(a, b), strict=True) if keep}
        assert got == closed_apart(a, b)
    assert lock_chain.apart_closed(t001, fifteen).all() and lock_chain.apart_closed(fifteen, t001).all()
    assert lock_chain.apart_closed(natural, wall).all() and lock_chain.apart_closed(wall, natural).any()
    inside = set(fifteen["states"])
    kit = {(w, label % 3) for label, w in t001["states"]}
    label, row = fifteen["states"][0]
    for t in range(3000):
        assert ((label + t) % 15, row & ((1 << 52) - 1)) in inside
        assert (row & ((1 << 47) - 1), (label + t) % 3) not in kit
        row = ((row << 1) | int("001"[(label + t) % 3])) ^ (row | (row >> 1))


def test_traps001() -> None:
    """The four traps for 001 of `Rule30Open.Columns.Traps001`: each a lock by `is_lock`, with the phase modulo its
    labels' modulus, each apart as a whole from each other (`apart_closed`), and the right half of state 0 of each,
    stepped under Rule 30 itself for 2,000 steps, inside it and never in a state of another, cut to that one's width,
    at a label of the same phase; `lean_traps001` gives the declarations of the module."""
    from computations import lock_chain

    traps = lock_chain.traps001_tables()
    assert [(name, t["cells"], t["modulus"], len(t["states"])) for name, t in traps] == [
        ("t001W", 47, 21, 815), ("trap001fifteen", 52, 15, 153), ("trap001b", 144, 21, 879),
        ("trap001c", 304, 21, 258)]
    for name, t in traps:
        assert t["word"] == "001" and lock_chain.is_lock("001" * (t["modulus"] // 3), t["states"], t["cells"])
        assert all(lock_chain.apart_closed(c, t).all() for other, c in traps if other != name)
        inside = set(t["states"])
        cuts = [(c["cells"], {(label % 3, w) for label, w in c["states"]}) for other, c in traps if other != name]
        label, row = t["states"][0]
        for step in range(2000):
            assert ((label + step) % t["modulus"], row & ((1 << t["cells"]) - 1)) in inside
            assert all(((label + step) % 3, row & ((1 << k) - 1)) not in cut for k, cut in cuts)
            row = ((row << 1) | int("001"[(label + step) % 3])) ^ (row | (row >> 1))
    lean = (ROOT / "Rule30Open" / "Columns" / "Traps001.lean").read_text(encoding="utf-8")
    assert lock_chain.lean_traps001() in lean


def test_apart_traps(monkeypatch: pytest.MonkeyPatch) -> None:
    """Every fourth of the 40 entries of `lock_chain.APART_TRAPS` whose other trap is not a census trap (a census trap
    takes 1 to 5 s to build; every entry is the module's reproduce command `--lean-apart-traps`): the refuted trap and
    the other are of the named block and the other is apart from it as a whole (`apart_closed`); the coverage holds each
    block through `ApartTraps` and counts the refuted trap as refuted; and `lean_apart_traps`, restricted to the first
    two entries, gives declarations of `Rule30Open.Columns.ApartTraps`."""
    from computations import coverage, lock_chain

    entries = {(m, n): b for m, n, b in lock_chain.module_entries()}
    cheap = [entry for entry in lock_chain.APART_TRAPS if not entry[3].startswith("Census")]
    assert len(cheap) == 40
    for block, module, name, other_module, other in cheap[::4]:
        c, s = entries[(module, name)](), entries[(other_module, other)]()
        assert c["word"] == s["word"] == block and lock_chain.apart_closed(c, s).all()
    for block, module, *_ in lock_chain.APART_TRAPS:
        assert block in lock_chain.apart_refuted()[module]
    assert len(lock_chain.APART_TRAPS) == 48 == len({block for block, *_ in lock_chain.APART_TRAPS})
    held = set(coverage.module_blocks())
    assert all((block, "ApartTraps") in held for block, *_ in lock_chain.APART_TRAPS)
    lean = (ROOT / "Rule30Open" / "Columns" / "ApartTraps.lean").read_text(encoding="utf-8")
    monkeypatch.setattr(lock_chain, "APART_TRAPS", cheap[:2])
    assert lock_chain.lean_apart_traps() in lean


def test_chain_trap_01111() -> None:
    """The lock of 5 cells of the seed `00000001101111111111`, carried 160 cells (by the lock values among those of
    its bottom components for which the carried block is `01111`), is a trap of 165 cells for `01111`, with labels
    modulo 20, a lock by `is_lock`, apart as a whole from `trap01111` of WordTraps and it from it (`apart_closed`); the
    right half of its state 0, stepped under Rule 30 itself for 3,000 steps, stays in it and never has its first 107
    cells in a state of `trap01111` at a label of the same phase."""
    from computations import lock_chain

    seed, distance = "00000001101111111111", 160
    carried = [lock_chain.trap_tables(seed, 5, distance, values) for _, values in lock_chain.lock_values(seed, 5)]
    [t] = [c for c in carried if c["word"] == "01111"]
    w = lock_chain.tables("trap01111")
    assert (t["word"], t["cells"], t["modulus"], len(t["states"])) == ("01111", 165, 20, 197)
    assert lock_chain.is_lock("01111" * 4, t["states"], 165)
    assert lock_chain.apart_closed(w, t).all() and lock_chain.apart_closed(t, w).all()
    inside, other = set(t["states"]), {(label % 5, window) for label, window in w["states"]}
    label, row = t["states"][0]
    for step in range(3000):
        assert ((label + step) % 20, row & ((1 << 165) - 1)) in inside
        assert ((label + step) % 5, row & ((1 << 107) - 1)) not in other
        row = ((row << 1) | int("01111"[(label + step) % 5])) ^ (row | (row >> 1))


def test_chain_family_01111() -> None:
    """`chain_family` for `01111` with `trap01111` of WordTraps: the chains of the long-run seeds of period 20 with at
    most 6 other cells give 6 more traps of 140 to 428 cells, each a lock by `is_lock`, and 5 of the 7 are pairwise
    apart; two of the family, stepped under Rule 30 itself from state 0 of each, stay out of the other's states for
    2,000 steps."""
    from computations import lock_chain

    traps, family = lock_chain.chain_family("01111", periods=(20,), rest=6, lean=[("trap01111",
                                                                                  lock_chain.tables("trap01111"))])
    assert len(traps) == 7 and len(family) == 5
    assert sorted(t["cells"] for name, t in traps if name != "trap01111")[::5] == [140, 428]
    assert all(lock_chain.is_lock("01111" * (t["modulus"] // 5), t["states"], t["cells"]) for _, t in traps)
    (_, a), (_, b) = traps[family[0]], traps[family[1]]
    for start, other in ((a, b), (b, a)):
        cut = {(label % 5, w) for label, w in other["states"]}
        label, row = start["states"][0]
        for step in range(2000):
            assert ((label + step) % 5, row & ((1 << other["cells"]) - 1)) not in cut
            row = ((row << 1) | int("01111"[(label + step) % 5])) ^ (row | (row >> 1))


def test_scan_six() -> None:
    """The long-run seeds of period 12 whose chains reach 001011 (`scan_block` with the first plan of `SCAN6` cut to
    period 12) give `trap001011` of WordTraps and traps of 33 and 35 cells, and the seed of period 24 with a lock of 9
    cells one of 154: each a lock by `is_lock`; read from the states, their first 22 cells are one set of 12 nodes, two
    at each phase, which `trap_nodes` finds as well; no one of the four is apart from another (`apart_closed`); and no
    node of the game of 15 cells, with the phase counted modulo 6 or 12, is locked (`locks.has_lock`)."""
    from computations import lock_chain, locks

    found = lock_chain.scan_block("001011", plans=(([12], 5, 12),))
    assert sorted(distance for *_, distance in found) == [24, 28, 30]
    traps = [lock_chain.trap_tables(seed, width, distance, values) for seed, values, width, distance in found]
    traps.append(lock_chain.trap_tables("001110011111111111111011", 9, 145, "110000000000000000000000"))
    assert sorted((t["cells"], t["modulus"], len(t["states"])) for t in traps) == [
        (29, 12, 116), (33, 12, 110), (35, 12, 114), (154, 24, 1721)]
    w = lock_chain.tables("trap001011")
    assert any(set(t["states"]) == set(w["states"]) for t in traps)
    mask = (1 << 22) - 1
    cuts = [{(label % 6, window & mask) for label, window in t["states"]} for t in traps]
    assert all(cut == cuts[0] for cut in cuts) and len(cuts[0]) == 12
    assert sorted(phase for phase, _ in cuts[0]) == [phase for phase in range(6) for _ in range(2)]
    nodes = lock_chain.trap_nodes((traps[0],), 22)  # (6 2^22,)
    assert set(np.flatnonzero(nodes).tolist()) == {(phase << 22) | window for phase, window in cuts[0]}
    assert not any(lock_chain.apart_closed(a, b).any() for a in traps for b in traps)
    assert all(t["word"] == "001011" and lock_chain.is_lock("001011" * (t["modulus"] // 6), t["states"], t["cells"])
               for t in traps)
    assert not any(locks.has_lock("001011" * repeat, 15, wide=True) for repeat in (1, 2))


def test_back_tables() -> None:
    """`back_tables` gives the set that `Rule30Open.Columns.ReachRefuted` checks: each label's windows in increasing
    order, every node with a move into the set in it, by `game.moves`, the trap's states cut to the width in it, and the
    node it names outside it; for the natural trap of 0010101111111 at 8 cells, 2,167 of the 3,328 nodes."""
    from computations import game, lock_chain

    t = lock_chain.extra_tables("0010101111111")
    s = lock_chain.back_tables((t,), 8)
    period = len(s["word"])
    assert sum(len(row) for row in s["rows"]) == 2167
    assert all(row == sorted(set(row)) for row in s["rows"])
    inside = np.zeros(period << 8, dtype=bool)  # (p n,)
    for label, row in enumerate(s["rows"]):
        inside[[label << 8 | w for w in row]] = True
    source, target = game.moves(s["word"], 8)
    assert not (inside[target] & ~inside[source]).any()
    assert all(inside[(label % period) << 8 | window & 255] for label, window in t["states"])
    l0, w0 = s["miss"]
    assert not inside[l0 << 8 | w0]


def test_six_refuted() -> None:
    """`lean_six` gives the declarations of `Rule30Open.Columns.SixRefuted`. Its set, the nodes of the game of 22 cells
    for 001011 that can reach `trap001011`, 28,666, against `successors`, forward: no node outside it, sampled one in
    97, has a move into it, the trap's states cut to 22 cells are in it, and the white window at phase 0 is not."""
    from computations import lock_chain

    t = lock_chain.tables("trap001011")
    s = lock_chain.back_tables((t,), 22)
    assert sum(len(row) for row in s["rows"]) == 28666 and s["miss"] == (0, 0)
    inside = np.zeros(6 << 22, dtype=bool)  # (6 2^22,)
    for label, row in enumerate(s["rows"]):
        inside[[label << 22 | w for w in row]] = True
    outside = np.arange(0, 6 << 22, 97, dtype=np.uint64)  # (6 2^22 / 97,), one node in 97
    outside = outside[~inside[outside.astype(np.int64)]]  # (m,)
    after = lock_chain.successors("001011", 22, outside)  # (2, m)
    assert not inside[after.astype(np.int64)].any()
    assert all(inside[(label % 6) << 22 | window & ((1 << 22) - 1)] for label, window in t["states"])
    assert not inside[0]
    lean = (ROOT / "Rule30Open" / "Columns" / "SixRefuted.lean").read_text(encoding="utf-8")
    assert lock_chain.lean_six() in lean


def test_own_locks() -> None:
    """`own_components`, found among the locked nodes alone, against `bottom_components`, which builds the game's list
    of moves, for 0111 at 13 cells and 0001 at 16; the bottom component of 0111 at 13 cells as a trap (`own_tables`),
    a lock by `is_lock` that every node of the game can reach (`trap_reach`); and the lists of `WIDE_CENSUS`: the block
    `00100111011`, whose traps in the trap modules all fail, is in `UNREACHED` for ElevenTraps, its carried trap
    `el0_27` of `CENSUS_APART` is built, every block of `CENSUS_APART` is one of `WIDE_CENSUS`, and every block of
    `WIDE_CENSUS` is one whose traps all fail, which the coverage counts as such until the blocks are checked in Lean.
    The bottom components of 20 and 22 cells of these blocks (`own_check`, minutes) are the entry's reproduce
    command."""
    from computations import coverage, lock_chain

    for block, width in (("0111", 13), ("0001", 16)):
        mine = [members.tolist() for members in lock_chain.own_components(block, width)]
        assert sorted(mine) == sorted(sorted(c.tolist()) for c in lock_chain.bottom_components(block, width))
    [t] = lock_chain.own_tables("0111", 13)
    assert (t["word"], t["cells"], t["modulus"]) == ("0111", 13, 4)
    assert lock_chain.is_lock("0111", t["states"], 13) and lock_chain.trap_reach(t, width=13) == 1.0
    block = "00100111011"
    assert block in lock_chain.WIDE_CENSUS and block in lock_chain.UNREACHED["ElevenTraps"]
    [(module, name)] = lock_chain.CENSUS_APART[block]
    c = next(build() for m, n, build in lock_chain.module_entries() if (m, n) == (module, name))
    assert (c["word"], c["cells"], len(c["states"])) == (block, 30, 313)
    assert set(lock_chain.CENSUS_APART) <= set(lock_chain.WIDE_CENSUS) <= coverage.refuted_blocks()


def test_module_entries() -> None:
    """`lock_chain.module_entries`: 1,595 traps, each named by a declaration `def <name> : WTrap` of its module's Lean
    file, the wall of period 9 at distance 0 by that of WordTraps; the names are distinct within a module; and the
    builders of three carried traps give the walls carried to the distances their names say."""
    from computations import lock_chain
    entries = lock_chain.module_entries()
    assert len(entries) == 1595
    columns = ROOT / "Rule30Open" / "Columns"
    names: dict[str, set[str]] = {}
    for module in {m for m, _, _ in entries}:
        names[module] = set(re.findall(r"^def ([A-Za-z0-9_]+) : WTrap", (columns / f"{module}.lean").read_text(
            encoding="utf-8"), re.M))
    words = set(re.findall(r"^def ([A-Za-z0-9_]+) : WTrap", (columns / "WordTraps.lean").read_text(encoding="utf-8"),
                           re.M))
    for module, name, _ in entries:
        assert name in names[module] or (module == "NineTraps" and name == "trap001011111" and name in words)
    for module in names:
        listed = [name for m, name, _ in entries if m == module]
        assert len(listed) == len(set(listed))
    picks = {("TenTraps", "ten10"): ("trap0000010001", 10), ("ThirteenTraps", "th0_3"): (lock_chain.WALLS[13][0], 3),
             ("FarWalls", "far12_41"): ("trap001011100111", 41)}
    for module, name, build in entries:
        if (module, name) in picks:
            assert build() == lock_chain.carried(*picks[(module, name)])


def test_refuted_traps() -> None:
    """The closed set of RefutedTraps for `nine15`, the period-9 wall carried 15 columns: `miss_tables` gives 21 windows
    of 2 cells with labels modulo 9; stepped with the rule cell by cell, under both values of cell 3, each goes to one of
    them with the next label; none is the first two cells of a state of the trap with a label of the same phase; and
    `lean_refuted` writes it as the module does."""
    from computations import lock_chain
    t = lock_chain.carried("trap001011111", 15)
    s = lock_chain.miss_tables(t)
    assert (t["word"], s["cells"], s["modulus"], len(s["states"])) == ("001101111", 2, 9, 21)
    states = set(s["states"])
    for label, window in states:
        c0, c1, c2 = int(t["word"][label % 9]), window & 1, (window >> 1) & 1
        for c3 in (0, 1):
            moved = (c0 ^ (c1 | c2)) | ((c1 ^ (c2 | c3)) << 1)
            assert ((label + 1) % 9, moved) in states
    assert not {(label % 9, window & 3) for label, window in t["states"]} & {(label % 9, w) for label, w in states}
    entry = ("NineTraps", "nine15", t, s)
    assert lock_chain.lean_refuted([entry]) in (ROOT / "Rule30Open" / "Columns" / "RefutedTraps.lean").read_text(
        encoding="utf-8")


def test_trap_sets(monkeypatch: pytest.MonkeyPatch) -> None:
    """`lock_chain.APART` and `TRAP_SETS`: each listed block is one of a trap or pair of its module; each block of the 29
    sets has every other trap refuted, by `UNREACHED` or `APART`; for 0000110110001 the scan's one half that locks is
    inside a natural trap of 30 cells apart from `th0_45` (`halves_apart`), that trap is a lock by `is_lock`, and every
    node of the game of 16 cells can reach one of the set's two traps; the natural traps of 193 states of period 15 are
    for the blocks of the chain of the narrowest, at the distances their widths give (`trap_chain`); and
    `lean_trap_sets`, restricted to the first set, is text of the module."""
    from computations import coverage, lock_chain
    held = set(coverage.module_blocks())
    assert all((block, module) in held for module, blocks in lock_chain.APART.items() for block in blocks)
    assert sum(len(v) for v in lock_chain.APART.values()) == 29 and len(lock_chain.TRAP_SETS) == 29
    for block, *_ in lock_chain.TRAP_SETS:
        others = {m for b, m in held if b == block} - {"TrapSets"}
        assert others and all(block in lock_chain.UNREACHED.get(m, ()) or block in lock_chain.APART.get(m, ())
                              for m in others)
    block = "0000110110001"
    traps = lock_chain.set_tables(block)
    assert [(m, n) for m, n, _ in traps] == [("ThirteenTraps", "th0_45"), ("TrapSets", f"sets{block}_0")]
    apart = lock_chain.halves_apart(traps[0][2], 3000)  # the scan over 3,000 steps; the entry's runs are 20,000
    assert [(cells, size, away) for _, cells, _, size, away in apart] == [(30, 162, True)]
    natural = traps[1][2]
    assert (natural["cells"], len(natural["states"])) == (30, 162) and lock_chain.is_lock(block, natural["states"], 30)
    assert lock_chain.trap_reach(*[t for *_, t in traps], width=16) == 1
    # the natural traps of 193 states of period 15 are one wall carried: their blocks lie on the chain of the narrowest
    wall = lock_chain.natural_tables("000111111011101", 0, 12000, 27, 15)
    blocks = lock_chain.trap_chain(wall, 12)
    for block, _, natural in lock_chain.TRAP_SETS:
        if len(block) == 15:
            for start, cells, modulus in natural:
                t = lock_chain.natural_tables(block, start, 12000, cells, modulus)
                if len(t["states"]) == 193:
                    assert blocks[t["cells"] - 27] == block
    monkeypatch.setattr(lock_chain, "TRAP_SETS", lock_chain.TRAP_SETS[:1])
    assert lock_chain.lean_trap_sets() in (ROOT / "Rule30Open" / "Columns" / "TrapSets.lean").read_text(encoding="utf-8")


def test_fifteen_walls(monkeypatch: pytest.MonkeyPatch) -> None:
    """The traps of FifteenWalls: the two walls have 27 and 37 cells and 193 and 652 states; both chains end in the
    background of spatial period 2,145, the second only from distance 152; each carried trap is for the block of its
    wall's chain at its distance (`trap_chain`), checked for every tenth of the 86 and the last, and the 86 blocks are
    distinct, 81 of no other module and 5 whose other traps are all refuted; the trap carried 2 columns is a lock by
    `is_lock` and every node of the game of 16 cells can reach it; and `lean_fifteen`, restricted to the first and to
    the last entry, is text of the module."""
    from computations import coverage, lock_chain
    walls = [lock_chain.fifteen_wall(k) for k in (0, 1)]
    assert [(w["cells"], len(w["states"])) for w in walls] == [(27, 193), (37, 652)]
    for wall, start in zip(walls, (0, 152), strict=True):
        full = wall["word"] * (wall["modulus"] // 15)
        values = "".join(str((wall["first"] >> label) & 1) if full[label] == "0" else "0" for label in range(15))
        assert (lambda found: (found[0], len(found[1])))(lock_chain.chain_cycle(full, values)) == (start, 2145)
    chains = [lock_chain.trap_chain(w, 120) for w in walls]
    blocks = [chains[wall][distance] for wall, distance in lock_chain.FIFTEEN_DISTANCES]
    for wall, distance in lock_chain.FIFTEEN_DISTANCES[::10] + lock_chain.FIFTEEN_DISTANCES[-1:]:
        t = lock_chain.fifteen_tables(wall, distance)
        assert t["word"] == chains[wall][distance] and t["cells"] == walls[wall]["cells"] + distance
    assert len(blocks) == len(set(blocks)) == 86
    held = [(b, m) for b, m in coverage.module_blocks()
            if m not in ("FifteenWalls", "ApartTraps") and b in set(blocks)]
    assert all(b in lock_chain.UNREACHED.get(m, ()) or b in lock_chain.APART.get(m, ()) for b, m in held)
    assert len({b for b, _ in held}) == 5
    near = lock_chain.fifteen_tables(1, 2)
    assert lock_chain.is_lock(near["word"], near["states"], near["cells"])
    assert lock_chain.trap_reach(near, width=16) == 1
    lean = (ROOT / "Rule30Open" / "Columns" / "FifteenWalls.lean").read_text(encoding="utf-8")
    for kept in (lock_chain.FIFTEEN_DISTANCES[:1], lock_chain.FIFTEEN_DISTANCES[-1:]):
        monkeypatch.setattr(lock_chain, "FIFTEEN_DISTANCES", kept)
        assert lock_chain.lean_fifteen() in lean


def test_unreached() -> None:
    """`lock_chain.UNREACHED`: each listed block is one of a trap of its module; the traps `trap01` and `trap001fifteen`
    and the period-10 wall carried 10 columns fail the test of reach already at 16, 16 and 12 cells; the natural trap of
    16 cells of 0001111110011 passes in the game of 16 cells and fails in that of 17, where the cell after it follows the
    rule; the 35 entries of `UNREACHED_WIDE` (whose games of 22 cells, minutes, are the entry's reproduce command) are
    each the block of a trap or pair of their module; and `coverage.refuted_blocks` holds the 200 blocks of periods 2
    to 15 with no trap that passes, 01 and 001011 among them and 001, which keeps the four traps of Traps001, not."""
    from collections import Counter
    from computations import coverage, lock_chain
    held = set(coverage.module_blocks())
    assert lock_chain.REACH_WIDTH == 20 and sum(len(v) for v in lock_chain.UNREACHED.values()) == 240
    assert all((block, module) in held for module, blocks in lock_chain.UNREACHED.items() for block in blocks)
    assert {"01", "001"} == set(lock_chain.UNREACHED["WordTraps"])
    assert lock_chain.trap_reach(lock_chain.tables("trap01"), width=16) < 1
    assert lock_chain.trap_reach(lock_chain.tables("trap001fifteen"), width=16) < 1
    ten = lock_chain.carried("trap0000010001", 10)
    assert ten["word"] in lock_chain.UNREACHED["TenTraps"] and lock_chain.trap_reach(ten, width=12) < 1
    natural = lock_chain.extra_tables("0001111110011")  # 16 cells
    assert "0001111110011" in lock_chain.UNREACHED["NaturalTrapsLong"] and natural["cells"] == 16
    assert lock_chain.trap_reach(natural) == 1 > lock_chain.trap_reach(natural, width=17)
    refuted = coverage.refuted_blocks()
    assert "0010011110101" in lock_chain.UNREACHED_WIDE["NaturalTrapsWalls"] and lock_chain.WIDE_WIDTH == 22
    assert sum(len(v) for v in lock_chain.UNREACHED_WIDE.values()) == 35
    assert all((block, module) in held for module, blocks in lock_chain.UNREACHED_WIDE.items() for block in blocks)
    assert len(refuted) == 200 and {"01", "001011"} <= refuted and "001" not in refuted
    assert sorted(Counter(len(b) for b in refuted).items()) == [(2, 1), (6, 1), (9, 7), (10, 4), (11, 17), (12, 17),
                                                                (13, 45), (14, 46), (15, 62)]


def test_reach_wide_carried() -> None:
    """`reach_nodes` against `locks.back_closure` over `game.moves`, for the natural trap of 0001111110011, 16 cells,
    which passes the test of reach at 16 cells and fails at 17, where 22,979 of the 13 * 2^17 nodes cannot reach it: the
    nodes that cannot reach form a set that no move leaves, with the moves recomputed cell by cell from the rule on a
    sample, and the least part of them that no move leaves (`fwd_tables`), 718 states, is closed under `successors` and
    holds no node that reaches the trap."""
    from computations import lock_chain, locks

    t = lock_chain.extra_tables("0001111110011")
    assert t["cells"] == 16 and lock_chain.trap_reach(t) == 1.0
    width = 17
    reach = lock_chain.reach_nodes((t,), width)  # (13 2^17,)
    source, target = game.moves("0001111110011", width)
    assert (locks.back_closure(lock_chain.trap_nodes((t,), width), source, target) == reach).all()
    assert not (~reach[source] & reach[target]).any()
    rng = np.random.default_rng(2)
    for node in rng.choice(np.flatnonzero(~reach), size=300, replace=False).tolist():
        phase, window = divmod(node, 1 << width)
        cells = [int("0001111110011"[phase])] + [(window >> i) & 1 for i in range(width)]
        for free in (0, 1):
            row = cells + [free]
            new = sum((row[i - 1] ^ (row[i] | row[i + 1])) << (i - 1) for i in range(1, width + 1))
            assert not reach[((phase + 1) % 13 << width) + new]
    assert int((~reach).sum()) == 22979
    s = lock_chain.fwd_tables((t,), width)
    assert len(s["states"]) == 718
    keys = np.array(sorted((label % 13) << width | w for label, w in s["states"]), dtype=np.uint64)
    assert np.isin(lock_chain.successors("0001111110011", width, keys), keys).all()
    assert not reach[keys.astype(np.int64)].any()


def test_wide_walls() -> None:
    """`fwd_tables`, which builds each wall of `WIDE_WALLS` at 22 cells, on the natural trap of 0001111110011 at 17 cells,
    where it fails the test of reach: the wall is a lock by `is_lock` for the block, closed under both values of the cell
    beyond by the moves of `successors`, and none of its nodes can reach the trap in the game of 17 cells; it shares
    no window of 17 cells, at a label of the same phase, with the trap it refutes, so no node of the wall can reach
    that trap; the trap is apart from the wall as a whole (`apart_closed`). Of the three walls of `WIDE_WALLS`: each is
    a carried trap of ElevenTraps or FourteenTraps, `WideWalls.lean` declares `wide_<name>` and its check for each, and
    the coverage holds their blocks; the walls at 22 cells (`lean_wide_walls`, minutes) are the entry's reproduce
    command."""
    from computations import coverage, lock_chain

    t = lock_chain.extra_tables("0001111110011")
    wall = lock_chain.fwd_tables((t,), 17)
    word, period = wall["word"], len(wall["word"])
    assert word == t["word"] and wall["cells"] == 17
    nodes = list(wall["states"])
    assert lock_chain.is_lock(word * (wall["modulus"] // period), nodes, 17)
    keys = np.array(sorted((label % period) << 17 | w for label, w in nodes), dtype=np.uint64)  # (states,)
    assert np.isin(lock_chain.successors(word, 17, keys), keys).all()
    assert not lock_chain.reach_nodes((t,), 17)[keys.astype(np.int64)].any()  # no node of the wall reaches the trap
    cut = {(label % period, window & ((1 << 17) - 1)) for label, window in t["states"]}
    assert not cut & {(label % period, window) for label, window in nodes}
    assert lock_chain.apart_closed(wall, t).all()
    lean = (ROOT / "Rule30Open" / "Columns" / "WideWalls.lean").read_text(encoding="utf-8")
    entries = {(m, n): b for m, n, b in lock_chain.module_entries()}
    assert len(lock_chain.WIDE_WALLS) == 3
    held = set(coverage.module_blocks())
    for module, name in lock_chain.WIDE_WALLS:
        assert module in ("ElevenTraps", "FourteenTraps") and (module, name) in entries
        assert f"theorem wide_{name}_check :" in lean and f"theorem wide_{name}_not_absorption :" in lean
        assert (entries[(module, name)]()["word"], "WideWalls") in held


def test_wall_natural(monkeypatch: pytest.MonkeyPatch) -> None:
    """The traps of NaturalTrapsWalls: every twelfth of `WALL_NATURAL` (five of the 54) is a lock by `is_lock` for its
    block, with labels modulo the period; its half, driven by the block with `step`, has its window in the trap at step
    12,000; the block of each of the 54 and 6 is one whose only traps, walls carried to it, fail the test of reach; for
    the first block of `WALL_SPLIT`, its two traps are locks, with labels modulo their own multiple of the period, apart
    from each other at the narrower width, so a half inside either never enters the other, and every node of the game of
    16 cells can reach one of the two; the two traps of 000000101101 have 150 and 116 states (that three halves of its
    scan are inside the second, apart from the first, takes a scan of 10,000 steps and more, the entry's reproduce
    command `--halves-apart`; `test_trap_sets` runs `halves_apart` on a shorter scan); and `lean_wall_natural`,
    restricted to the first trap of `WALL_NATURAL` and to the first block of `WALL_SPLIT`, is text of the module."""
    from computations import coverage, lock_chain
    walls = {"TenTraps", "ElevenTraps", "TwelveTraps", "ThirteenTraps", "FourteenTraps"}
    held: dict[str, set[str]] = {}
    for block, module in coverage.module_blocks():
        held.setdefault(block, set()).add(module)
    assert len(lock_chain.WALL_NATURAL) == 54 and len(lock_chain.WALL_SPLIT) == 6
    for word, start, cells, _ in lock_chain.WALL_NATURAL[::12]:
        t = lock_chain.extra_tables(word)
        assert (t["word"], t["cells"], t["modulus"]) == (word, cells, len(word)) and cells <= 18
        assert lock_chain.is_lock(word, t["states"], cells) and natural_inside(word, start, cells, t)
    for word, _ in lock_chain.WALL_SPLIT[:1]:
        pair = lock_chain.split_tables(word)
        assert all(lock_chain.is_lock(word * (t["modulus"] // len(word)), t["states"], t["cells"]) for t in pair)
        cut = min(t["cells"] for t in pair)
        sets = [{(lab % len(word), w & ((1 << cut) - 1)) for lab, w in t["states"]} for t in pair]
        assert not sets[0] & sets[1] and lock_chain.trap_reach(*pair, width=16) == 1
    for word, *_ in lock_chain.WALL_NATURAL + lock_chain.WALL_SPLIT:
        others = held[word] - {"NaturalTrapsWalls", "ApartTraps"}
        assert others and others <= walls and all(word in lock_chain.UNREACHED[m] for m in others)
    # the trap of 17 cells of 000000101101 passes the test of reach at 20 cells, but three halves of its scan are inside
    # the trap of 26 cells, apart from it (`--halves-apart`)
    first, second = lock_chain.split_tables("000000101101")
    assert (first["cells"], len(first["states"]), second["cells"], len(second["states"])) == (17, 150, 26, 116)
    lean = (ROOT / "Rule30Open" / "Columns" / "NaturalTrapsWalls.lean").read_text(encoding="utf-8")
    entries, split = lock_chain.WALL_NATURAL, lock_chain.WALL_SPLIT
    for kept, kept_split in ((entries[:1], []), ([], split[:1])):
        monkeypatch.setattr(lock_chain, "WALL_NATURAL", kept)
        monkeypatch.setattr(lock_chain, "WALL_SPLIT", kept_split)
        assert lock_chain.lean_wall_natural() in lean


def test_trap_pairs(monkeypatch: pytest.MonkeyPatch) -> None:
    """The traps of TrapPairs: each block of `PAIRS` is that of a natural trap of MissedTraps; for the first, it has two
    bottom components of locked windows of 16 cells, the second that natural trap, each a lock by `is_lock` with its own
    values of column 1 at the white phases; some node of the game cannot reach either alone, every node can reach one of
    the two (the union of the nodes that `reach_nodes` finds for each); and `lean_pairs`, restricted to that block, is
    the text of its entries in TrapPairs.lean."""
    from computations import lock_chain
    assert [word for word, *_ in lock_chain.MISSED_NATURAL] == lock_chain.PAIRS
    block = lock_chain.PAIRS[0]
    traps = lock_chain.pair_tables(block)
    assert len(traps) == 2 and all(t["word"] == block and t["cells"] == 16 for t in traps)
    assert set(traps[1]["states"]) == set(lock_chain.extra_tables(block)["states"])
    assert all(lock_chain.is_lock(block, t["states"], 16) for t in traps)
    values = [{(label, window & 1) for label, window in t["states"] if block[label] == "0"} for t in traps]
    assert values[0] != values[1]
    reach = [lock_chain.reach_nodes((t,), 16) for t in traps]  # (13 2^16,) each, the nodes that can reach each trap
    assert max(float(r.mean()) for r in reach) < 1 and (reach[0] | reach[1]).all()
    monkeypatch.setattr(lock_chain, "PAIRS", [block])
    assert lock_chain.lean_pairs() in (ROOT / "Rule30Open" / "Columns" / "TrapPairs.lean").read_text(encoding="utf-8")


def test_natural_traps(monkeypatch: pytest.MonkeyPatch) -> None:
    """The traps of NaturalTraps, NaturalTrapsLarge, NaturalTrapsLong and NaturalTrapsLongLarge, on a sample of each
    (every eighth of the 35 natural traps, every fourteenth of the 70 long ones, the first three of the 12 long large ones;
    the large one, of 61,857 states, is the reproduce command `--lean-large`): a lock by `is_lock`, a direct check
    with the rule, for its block, and for the natural and the long ones its half, driven by the block with `step`, has
    its window in the trap at step 12,000; the sampled natural traps have 107 to 15,752 states, the long ones 3,000 or
    fewer and the long large ones more. From the lists alone: the 35 blocks of periods 10 to 12 and the 70 of periods 13
    and 14 are distinct, and neither the kit's nor a block of another trap module; the 12 large ones of periods 13 and
    14 are census blocks too. `lean_extra`, restricted to the first entry, `lean_extra` for the first long one and
    `lean_long_large` restricted to its third entry are text of the modules (`lean_large` writes the 61,857 states of
    the large one by the same `lean_parts`, in 5 s, and is left to the entry's reproduce command); and `lean_number`
    writes numbers in pieces that sum back to them."""
    from computations import coverage, lock_chain
    entries = lock_chain.EXTRA_TRAPS + lock_chain.LARGE_TRAPS
    assert len(entries) == 35 and sorted(len(word) for word, *_ in entries) == [10] * 3 + [11] * 14 + [12] * 18
    assert entries[-1][0] == "00010001011" and "00010001011" not in [word for word, *_ in entries[::8]]
    for word, start, cells, modulus in entries[::8]:
        t = lock_chain.extra_tables(word)
        assert (t["word"], t["cells"], t["modulus"]) == (word, cells, modulus)
        assert lock_chain.is_lock(word * (modulus // len(word)), t["states"], cells)
        assert 107 <= len(t["states"]) <= 15752
        assert natural_inside(word, start, cells, t)
    walls = {word for word, module in coverage.trap_blocks().items()
             if module in ("TenTraps", "ElevenTraps", "TwelveTraps")}
    assert not {word for word, *_ in entries} & (walls | set(game.kit_blocks(12)))
    lean_dir = ROOT / "Rule30Open" / "Columns"
    monkeypatch.setattr(lock_chain, "EXTRA_TRAPS", entries[:1])
    assert lock_chain.lean_extra() in (lean_dir / "NaturalTraps.lean").read_text(encoding="utf-8")
    long_entries = lock_chain.LONG_TRAPS
    long_blocks = [word for word, *_ in long_entries]
    assert sorted(len(word) for word in long_blocks) == [13] * 31 + [14] * 39 and len(set(long_blocks)) == 70
    others = {word for word, module in coverage.trap_blocks().items() if module != "NaturalTrapsLong"}
    assert not set(long_blocks) & (others | set(game.kit_blocks(14)))
    for word, start, cells, modulus in long_entries[::14]:
        t = lock_chain.extra_tables(word)
        assert (t["word"], t["cells"], t["modulus"]) == (word, cells, modulus) and len(t["states"]) <= 3000
        assert lock_chain.is_lock(word, t["states"], cells) and natural_inside(word, start, cells, t)
    assert lock_chain.lean_extra(long_entries[:1]) in (lean_dir / "NaturalTrapsLong.lean").read_text(encoding="utf-8")
    census = {word for word, *_ in lock_chain.CENSUS_TRAPS[13] + lock_chain.CENSUS_TRAPS[14]}
    assert len(lock_chain.LONG_LARGE) == 12
    for word, _, cells, modulus in lock_chain.LONG_LARGE[:3]:
        t = lock_chain.extra_tables(word)
        assert (t["word"], t["cells"], t["modulus"]) == (word, cells, modulus) and len(t["states"]) > 3000
        assert lock_chain.is_lock(word, t["states"], cells) and word in census
    assert {word for word, *_ in lock_chain.LONG_LARGE}.isdisjoint(set(long_blocks))
    monkeypatch.setattr(lock_chain, "LONG_LARGE", lock_chain.LONG_LARGE[2:3])  # the smallest of the three, 3,377 states
    assert lock_chain.lean_long_large() in (lean_dir / "NaturalTrapsLongLarge.lean").read_text(encoding="utf-8")
    for x in (0, 5, (7 << 40) + 3, 3 ** 200):
        terms = lock_chain.lean_number(x, 16).split("+")
        assert sum(int(a) << (int(b) if b else 0) for a, _, b in (term.strip().partition(" <<< ") for term in terms)) == x


def test_second_nine_wall() -> None:
    """The second wall of period 9: from the random start that `NATURAL` names, a run of 001010011 is inside a closed
    set of 5,710 windows of 41 cells, with the phase modulo 27, that fixes column 1 at the white phases, by `is_lock`;
    no width from 16 to 40 gives a trap of at most 10,000 states at that step (the scan's cap, 100,000, takes five times
    as long and is the entry's reproduce command); and the run enters the set at step 7,622 by a direct run with `step`.
    """
    from computations import lock_chain, right_half
    name, word, start, time, cells, modulus = lock_chain.NATURAL[1]
    assert start == right_half.random_starts(30, 64)[2]
    assert lock_chain.natural_trap(word, start, [time], list(range(16, cells + 1)), [modulus],
                                   cap=10000) == (time, cells, 27, 5710)
    t = lock_chain.tables(name)
    assert t["word"] == word and lock_chain.is_lock(word * 3, t["states"], cells)
    _, _, states = lock_chain.trap_states(name)
    row, entered = start << 1, -1
    for t in range(time):
        row = (row & ~1) | int(word[t % 9])
        if (t % 9, (row >> 1) & ((1 << cells) - 1)) in states:
            entered = t
            break
        row = step(row)
    assert entered == 7622


def natural_inside(word: str, start: int, cells: int, t: dict, time: int = 12000) -> bool:
    """Whether the half `start`, driven by `word` with `step`, has its first `cells` cells in a state of the trap `t`
    at step `time`, with the label modulo the period."""
    row = start << 1  # bit 0 the block's column, bit i column i
    for s in range(time):
        if s % 1024 == 0:
            row &= (1 << (cells + 1 + time - s)) - 1  # bit i reaches cell `cells` only after i - cells steps
        row = step((row & ~1) | int(word[s % len(word)]))
    inside = {(label % len(word), window) for label, window in t["states"]}
    return (time % len(word), (row >> 1) & ((1 << cells) - 1)) in inside
