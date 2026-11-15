"""Tests of computations.bit_game: the bit tables and phase rounds against the finite game of `game`, and the
BitBlocks generators against their Lean files."""

from __future__ import annotations

import re
import numpy as np

from computations import game
from references import ROOT


def test_bit_phases() -> None:
    """`bit_game.phase_rounds` against the game: up to period 8 at width 6 every phase empties a side exactly when
    `game.bad_pairs` finds no component showing both values at a phase, after the rounds of the same refinement with
    each closure grown one move at a time over every node (`phase_rounds` grows it by one breadth-first search). For one
    block of `WIDE`, `lean_block` is the text of its checks in BitPhases.lean, and the lists of the four modules hold
    exactly the 75 blocks of `WIDE`."""
    from computations import bit_game

    def rounds_by_moves(pattern: str, width: int) -> list[int] | None:
        source, target, _, _, column = game.game_graph(pattern, width)  # (2 p n,), (2 p n,), (p n,)
        phase_of = np.arange(column.size) >> width  # (p n,)

        def close(seed: np.ndarray, src: np.ndarray, tgt: np.ndarray) -> np.ndarray:
            # seed: (p n,); src, tgt: (2 p n,), the moves in the direction searched
            found, frontier = np.zeros(column.size, dtype=bool), seed.copy()  # (p n,) each
            while frontier.any():
                reached = np.zeros(column.size, dtype=bool)  # (p n,)
                reached[tgt[frontier[src]]] = True
                frontier = reached & ~found
                found |= frontier
            return found  # (p n,)

        rounds = []
        for phase in range(len(pattern)):
            ones, zeros = (phase_of == phase) & column, (phase_of == phase) & ~column  # (p n,) each
            count = 0
            while ones.any() and zeros.any():
                new_zeros = zeros & close(ones, source, target) & close(ones, target, source)
                new_ones = ones & close(zeros, source, target) & close(zeros, target, source)
                if (new_zeros == zeros).all() and (new_ones == ones).all():
                    return None
                zeros, ones, count = new_zeros, new_ones, count + 1
            rounds.append(count)
        return rounds

    for period in range(2, 9):
        for pattern in game.necklaces(period):
            try:
                rounds = bit_game.phase_rounds(pattern, 6)
            except ValueError:
                rounds = None
            assert (rounds is not None) == (game.bad_pairs(pattern, 6) == 0), pattern
            assert rounds == rounds_by_moves(pattern, 6), pattern
    lean = {name: (ROOT / "Rule30Open" / "Columns" / f"{name}.lean").read_text(encoding="utf-8")
            for name in ("BitPhases", "BitPhases19", "BitPhases20", "BitPhases21")}
    block = "000101111111111001"  # one block, the fastest to build, tests the generator; the kernel checks every one
    assert bit_game.lean_block(block, bit_game.WIDE[block]) in lean["BitPhases"]
    listed = {}
    for text in lean.values():
        for n, bits, width in re.findall(r"\(\((\d+), 0b([01]+)\), (\d+)\)", text):
            listed[bits] = int(width)
            assert len(bits) == int(n)
    assert listed == bit_game.WIDE


def test_bit_blocks() -> None:
    """The BitBlocks modules of period 19 to 21: `lean_bit_blocks`, given the entries of each module's lists, is the
    text of its checks and exclusions; the last entry of each list passes `criterion` with the listed images and rounds,
    and the game, by `bad_pairs`, excludes the block at the listed width (the kernel checks every entry); and the
    period-21 modules hold the 268 new blocks of width at most 12 and the 111 of WallSets."""
    from computations import bit_game, wall_segments
    found: dict[str, list[str]] = {}
    for name, period in (("19", 19), ("19Wide", 19), ("20", 20), ("20Mid", 20), ("20Wide", 20), ("21", 21),
                         ("21Mid", 21), ("21Wide", 21)):
        text = (ROOT / "Rule30Open" / "Columns" / f"BitBlocks{name}.lean").read_text(encoding="utf-8")
        rows = [(block, int(width), int(steps), int(rounds)) for block, width, steps, rounds
                in re.findall(r"\(\(\d+, 0b([01]+)\), \((\d+), (\d+), (\d+), 300\)\)", text)]
        listed = re.search(r"def wallBlocks\d+ : List Nat := \[(.*?)\]", text, re.S)
        walls = re.findall(r"0b([01]+)", listed.group(1)) if listed else []
        assert bit_game.lean_bit_blocks(period, name, rows, walls) in text
        for block, width, steps, rounds in rows[-1:]:
            assert len(block) == period
            assert bit_game.criterion(block, width, steps)[:3] == (True, steps, rounds)
            assert game.bad_pairs(block, width) == 0
        assert all(wall_segments.in_set_family(block) for block in walls[:3])
        found.setdefault(f"rows{period}", []).extend(block for block, *_ in rows)
        found.setdefault(f"walls{period}", []).extend(walls)
    assert (len(found["rows21"]), len(set(found["rows21"])), len(found["walls21"])) == (268, 268, 111)


def test_bit_game() -> None:
    """The check of `BitGame` against the finite game: on every primitive block of period at most 9, at widths 5 and 6,
    it decides exactly the blocks the game excludes; and the bit tables' images and preimages agree with the game
    graph on random sets of nodes."""
    from computations import bit_game
    for period in range(1, 10):
        for block in game.necklaces(period):
            for width in (5, 6):
                assert bit_game.criterion(block, width)[0] == (game.bad_pairs(block, width) == 0)
    rng = np.random.default_rng(3)
    for block, width in (("0001", 5), ("00000001", 6), ("0110", 4)):
        tables = bit_game.BitTables(block, width)
        source, target, _, _, _ = game.game_graph(block, width)
        for _ in range(3):
            nodes = rng.random(len(block) << width) < 0.3  # (p 2^K,)
            image = np.zeros_like(nodes)  # (p 2^K,)
            image[target[nodes[source]]] = True
            preimage = np.zeros_like(nodes)  # (p 2^K,)
            preimage[source[nodes[target]]] = True
            table = tables.table(nodes)
            assert (tables.nodes(tables.post(table)) == image).all()
            assert (tables.nodes(tables.pre(table)) == preimage).all()
