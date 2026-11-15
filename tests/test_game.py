"""Tests of computations.game: the finite game, its extensions and its Lean certificates against plain Python, real
right halves and the kit's source."""

from __future__ import annotations

import math
import re
import numpy as np
import pytest

from computations import game
from computations.cyclic_words import least_rotation
from references import ROOT, packed_fields


def column_minus_one(pattern: str, right: np.ndarray, steps: int) -> np.ndarray:
    """Column -1, c_(t+1) xor (c_t or cell 1), for t < steps, of finite right halves driven by a center repeating
    `pattern`, one half a row, all stepped at once."""
    # right: (k, r)
    k = right.shape[0]
    c = np.array([int(pattern[t % len(pattern)]) for t in range(steps + 1)], dtype=bool)  # (steps + 1,)
    row = np.concatenate([right.astype(bool), np.zeros((k, steps + 2), dtype=bool)], axis=1)  # (k, n), cells 1, 2, ..
    out = np.zeros((k, steps), dtype=bool)  # (k, steps)
    for t in range(steps):
        out[:, t] = c[t + 1] ^ (c[t] | row[:, 0])
        left = np.concatenate([np.full((k, 1), c[t]), row[:, :-1]], axis=1)  # (k, n)
        right_cells = np.concatenate([row[:, 1:], np.zeros((k, 1), dtype=bool)], axis=1)  # (k, n)
        row = left ^ (row | right_cells)
    return out  # (k, steps)


def test_game() -> None:
    """The game excludes the constant blocks, 0 1^9 and 0^6 1^2 and leaves 01 open; on real right halves driven by
    0^6 1^2 column -1 is eventually periodic, as the game says; and the certificates in FiniteGame.lean are the ones
    `game_certificate` builds."""
    assert game.bad_pairs("0", 4) == 0 and game.bad_pairs("1", 4) == 0
    assert game.bad_pairs("0111111111", 6) == 0 and game.bad_pairs("00000011", 6) == 0
    assert game.bad_pairs("01", 8) > 0
    assert game.necklaces(4) == ["0001", "0011", "0111"]
    rng = np.random.default_rng(7)
    halves = np.array([rng.integers(0, 2, size=40) for _ in range(20)])  # (20, 40), the draws one half at a time
    for column in column_minus_one("00000011", halves, 800):  # (800,) each
        tail = column[400:].reshape(-1, 8)  # (50, 8), one period a row
        assert (tail == tail[0]).all()
    lean = (ROOT / "Rule30Open" / "Columns" / "FiniteGame.lean").read_text(encoding="utf-8")
    for pattern, width in (("01111111", 5), ("00000011", 6)):
        assert game.lean_certificate(pattern, width) in lean, pattern
    with pytest.raises(ValueError, match="not a function of the phase"):
        game.game_certificate("01", 8)


def jen_open_brute(pattern: str, width: int) -> list[int]:
    """`game.jen_open` by plain Python: components by mutual reachability, then the same three closures."""
    period, n = len(pattern), 1 << width
    moves = {}
    for ph in range(period):
        for r in range(n):
            cells = [(r >> x) & 1 for x in range(width)]
            for free in (0, 1):
                left = [int(pattern[ph])] + cells[:-1]
                right = cells[1:] + [free]
                nxt = sum((l ^ (c | rr)) << x for x, (l, c, rr) in enumerate(zip(left, cells, right, strict=True)))
                moves.setdefault((ph, r), []).append((((ph + 1) % period, nxt), free))
    reach = {}
    for node in moves:
        seen, todo = {node}, [node]
        while todo:
            for target, _ in moves[todo.pop()]:
                if target not in seen:
                    seen.add(target)
                    todo.append(target)
        reach[node] = seen
    components = {frozenset(m for m in reach[node] if node in reach[m]) for node in moves}
    sizes = []
    for component in components:
        inside = [(a, b, free) for a in component for b, free in moves[a] if b in component]
        if not inside:
            continue

        def constant(pairs: list[tuple[int, int]]) -> bool:
            return all(len({v for p, v in pairs if p == ph}) <= 1 for ph in range(period))

        left_column = [(ph, int(pattern[(ph + 1) % period]) ^ (int(pattern[ph]) | (r & 1))) for ph, r in component]
        if constant(left_column):
            continue
        if any(constant([(ph, (r >> x) & 1) for ph, r in component]) for x in range(width)):
            continue
        if constant([(a[0], free) for a, _, free in inside]):
            continue
        if any(all(len({(b[0], b[1] & ((1 << j) - 1)) for a, b, _ in inside if (a[0], a[1] & ((1 << j) - 1)) == key})
                   <= 1 for key in {(a[0], a[1] & ((1 << j) - 1)) for a, _, _ in inside}) for j in range(1, width + 1)):
            continue
        sizes.append(len(component))
    return sorted(sizes, reverse=True)


def test_jen_open() -> None:
    """The extended game against plain Python on six blocks at widths 4 and 5, and up to period 8 at width 6 it
    excludes exactly the blocks the game excludes."""
    for pattern in ("0001", "0011", "0111", "01", "001", "00000011"):
        for width in (4, 5):
            assert game.jen_open(pattern, width) == jen_open_brute(pattern, width), (pattern, width)
    blocks = [pattern for period in range(1, 9) for pattern in game.necklaces(period)]
    assert [p for p in blocks if not game.jen_open(p, 6)] == [p for p in blocks if game.bad_pairs(p, 6) == 0]


def test_component_periods() -> None:
    """`game.component_periods` against closed walks: for 001 at width 4 and 0001 at width 6, the cyclic period of each
    component that can hold a play is the gcd of the lengths up to 60 of the closed walks inside it through its first
    node, from powers of its adjacency matrix; its phase test agrees with `bad_pairs`; and 001 at width 4 has a
    component of period 6 where the left column takes both values at one phase but not in one class."""
    for pattern, width in (("001", 4), ("0001", 6)):
        source, target, label, recurrent, _ = game.game_graph(pattern, width)
        found = game.component_periods(pattern, width)
        assert len(found) == int(recurrent.sum())
        for (size, cycle, _, _), component in zip(found, np.flatnonzero(recurrent).tolist(), strict=True):
            members = np.flatnonzero(label == component)  # (m,)
            index = {node: i for i, node in enumerate(members.tolist())}
            adjacency = np.zeros((members.size, members.size))  # (m, m)
            for a, b in zip(source.tolist(), target.tolist(), strict=True):
                if a in index and b in index:
                    adjacency[index[a], index[b]] = 1.0
            walk, lengths = np.eye(members.size), []  # (m, m)
            for n in range(1, 61):
                walk = np.minimum(walk @ adjacency, 1.0)
                if walk[0, 0] > 0:
                    lengths.append(n)
            assert size == members.size and cycle == math.gcd(*lengths), (pattern, width, component)
        assert any(found_phase for _, _, found_phase, _ in found) == (game.bad_pairs(pattern, width) > 0)
    assert (6, 6, True, False) in game.component_periods("001", 4)


KIT_SOURCE = ROOT / ".lake/packages/rule30prize/lean/Ruliology/CellularAutomata"


def test_kit_blocks() -> None:
    """`KIT_WORDS` is the kit's strip-certificate table, read from its source, and its three single strip certificates;
    and `kit_blocks` agrees on every primitive block up to period 14 with each family read directly: cyclic runs of 1s
    found position by position, and every rotation of each padded word. That makes 43 blocks, 0^9 1 among them and
    0^7 1 not."""
    table = re.findall(r"\((\d+), (\d+), \d+, \d+\)",
                       (KIT_SOURCE / "Rule30StripCertificateTable.lean").read_text(encoding="utf-8"))
    singles = re.findall(r"theorem not_eventually_([01]+) :",
                         (KIT_SOURCE / "Rule30StripCertificates.lean").read_text(encoding="utf-8"))
    assert len(table) == 30 and len(singles) == 3
    words = {least_rotation(format(int(bits), f"0{n}b")) for n, bits in table} | set(singles)
    assert set(game.KIT_WORDS) == words and len(game.KIT_WORDS) == len(words) == 32  # 01111111 is in both
    expected = set(game.KIT_WORDS)
    for period in range(1, 15):
        padded = {("0" * (period - len(tail)) + tail)[i:] + ("0" * (period - len(tail)) + tail)[:i]
                  for tail, white in (("1", 9), ("11", 8), ("10111", 9)) if period - len(tail) >= white
                  for i in range(period)}
        for word in game.necklaces(period):
            runs = []
            for start in range(period):
                if word[start] == "1" and word[start - 1] == "0":
                    length = 0
                    while word[(start + length) % period] == "1":
                        length += 1
                    runs.append(length)
            if all(run >= 9 for run in runs) or word in padded:
                expected.add(word)
    kit = game.kit_blocks(14)
    assert set(kit) == expected and len(kit) == 43
    assert "0000000001" in kit and "00000001" not in kit


def mask_ok(pattern: str, width: int, mask: dict) -> bool:
    """`GameMask.check` in plain Python: cells as lists stepped by the rule, ranks read bit by bit (`packed_fields`)."""
    period, bits = len(pattern), mask["bits"]
    ranks = [packed_fields(mask["ranks"][phase], bits, 1 << width) for phase in range(period)]

    def rank(phase: int, cells: list[bool]) -> int:
        return ranks[phase][sum(1 << i for i, cell in enumerate(cells) if cell)]

    for phase in range(period):
        c, c_next = pattern[phase] == "1", pattern[(phase + 1) % period] == "1"
        for code in range(1 << width):
            cells = [bool(code >> i & 1) for i in range(width)]
            here = rank(phase, cells)
            transient = bool(mask["transient"] >> here & 1)
            for free in (False, True):
                row = [c] + cells + [free]
                after = [row[i] ^ (row[i + 1] | row[i + 2]) for i in range(width)]
                there = rank((phase + 1) % period, after)
                if there < here or (transient and there == here):
                    return False
            if not transient and bool(mask["values"] >> (here * period + phase) & 1) != (c_next ^ (c | cells[0])):
                return False
    return True


def test_game_masks() -> None:
    """The 32 certificates in GameBlocks.lean are for blocks the kit does not exclude and `gameBlocks` lists the same
    blocks; every ninth from the fifth to the last (four, of 448 to 7,168 nodes) is `lean_mask` at the least width and
    passes the check in plain Python and fails it with its values cleared (the kernel checks the rest). The two blocks
    left out need 114,688 and 229,376 nodes. A certificate at one width gives one at every larger width, checked for
    three blocks up to width 11."""
    lean = (ROOT / "Rule30Open" / "Columns" / "GameBlocks.lean").read_text(encoding="utf-8")
    masks = re.findall(r"def mask([01]+) : GameMask where\n  block := wordOf (\d+) 0b\1\n  width := (\d+)", lean)
    listed = re.findall(r"\((\d+), 0b([01]+)\)", lean.split("def gameBlocks", 1)[1].split("\n\n", 1)[0])
    assert len(masks) == 32 and [(n, p) for p, n, _ in masks] == listed
    kit = game.kit_blocks(14)
    for pattern, n, _ in masks:
        assert int(n) == len(pattern) and pattern == least_rotation(pattern) and pattern not in kit
    for pattern, _, width in masks[4::9]:
        width = int(width)
        assert game.least_width(pattern) == width and len(pattern) << width <= 1 << 15
        assert game.lean_mask(pattern, width) in lean, pattern
        mask = game.game_mask(pattern, width)
        assert mask_ok(pattern, width, mask) and not mask_ok(pattern, width, {**mask, "values": 0}), pattern
    for pattern, width in (("00000001001111", 13), ("00000000010001", 14)):
        assert pattern not in kit and game.least_width(pattern) == width
    assert [len(p) << w for p, w in (("00000001001111", 13), ("00000000010001", 14))] == [114688, 229376]
    for pattern in ("00010111111111", "00000000110011", "0000000001101"):
        least = game.least_width(pattern)
        assert all(game.bad_pairs(pattern, width) == 0 for width in range(least, 12))


def test_game_masks_long() -> None:
    """The 97 certificates in GameBlocksLong.lean are `lean_mask` at the least width, at most 9, of blocks of period 15
    or 16 that the kit does not exclude (checked for ten sampled and every eighth), `gameBlocks16` lists the same
    blocks, and sampled certificates pass the check in
    plain Python and fail it with their values cleared."""
    lean = (ROOT / "Rule30Open" / "Columns" / "GameBlocksLong.lean").read_text(encoding="utf-8")
    masks = re.findall(r"def mask([01]+) : GameMask where\n  block := wordOf (\d+) 0b\1\n  width := (\d+)", lean)
    listed = re.findall(r"\((\d+), 0b([01]+)\)", lean.split("def gameBlocks16", 1)[1].split("\n\n", 1)[0])
    assert len(masks) == 97 and [(n, p) for p, n, _ in masks] == listed
    kit = game.kit_blocks(16)
    rng = np.random.default_rng(45)
    sampled = set(rng.choice(len(masks), size=10, replace=False).tolist())
    for i, (pattern, n, width) in enumerate(masks):
        width = int(width)
        assert int(n) == len(pattern) in (15, 16) and pattern == least_rotation(pattern) and pattern not in kit
        if i in sampled or i % 8 == 0:
            assert game.least_width(pattern) == width <= 9
            assert game.lean_mask(pattern, width) in lean, pattern
        if i in sampled:
            mask = game.game_mask(pattern, width)
            assert mask_ok(pattern, width, mask) and not mask_ok(pattern, width, {**mask, "values": 0}), pattern


def test_kit_families() -> None:
    """`PADDING_FAMILIES` and `BLACK_RUN_BLOCKS` are the kit's white-padding certificates and its Theorem B' instances,
    read from its source; at periods 17 and 18 they add 0^13 1011, 0^14 1011 and 0^14 1101 to `kit_blocks`, and up to
    period 16 nothing."""
    padding = (KIT_SOURCE / "Rule30UniformWhitePadding.lean").read_text(encoding="utf-8") + \
        (KIT_SOURCE / "Rule30ShortTail.lean").read_text(encoding="utf-8")
    thresholds = dict(re.findall(r"theorem certificate([A-I]) \(r : Nat\) \(hr : (\d+) ≤ r\)", padding))
    tails = dict(re.findall(r"def tail([A-I]) : List Bool := \[([^\]]*)\]",
                            (KIT_SOURCE / "Rule30Certificates/WhitePaddingFamilies.lean").read_text(encoding="utf-8")))
    assert sorted(thresholds) == sorted(tails) == list("ABCDEFGHI")
    read = {("".join("1" if cell.strip() == "true" else "0" for cell in tails[name].split(",")), int(thresholds[name]))
            for name in thresholds}
    assert read == set(game.PADDING_FAMILIES)
    blocks = re.findall(r"theorem det_[01]+ : Determined \[([^\]]*)\] (\d+) = true",
                        (KIT_SOURCE / "Rule30BlackRunBlocks.lean").read_text(encoding="utf-8"))
    read = {("".join("1" if cell.strip() == "true" else "0" for cell in cells.split(",")), max(9, 9 * int(j0)))
            for cells, j0 in blocks}
    assert read == set(game.BLACK_RUN_BLOCKS)
    assert "padding or black-run family" not in game.kit_blocks(16).values() and len(game.kit_blocks(16)) == 62
    added = {word for word, reason in game.kit_blocks(18).items() if reason == "padding or black-run family"}
    assert added == {"0" * 13 + "1011", "0" * 14 + "1011", "0" * 14 + "1101"}


def test_game_survey() -> None:
    """The survey of `excluded_blocks` over worker processes agrees, at period 8, where it excludes 00000011 and
    01111111 at width 6, with the survey in one process, which agrees with `least_width`, block by block, on every
    primitive block of period 7 and 8 (periods 9 and 10 are the reproduce command of the survey)."""
    one, tried = game.excluded_blocks(8, [6, 10], min_period=7)
    two, tried2 = game.excluded_blocks(8, [6, 10], min_period=8, workers=2)
    assert tried == len(game.necklaces(7)) + len(game.necklaces(8)) and tried2 == len(game.necklaces(8))
    assert two == {block: width for block, width in one.items() if len(block) == 8} == {"00000011": 6, "01111111": 6}
    for period in range(7, 9):
        for block in game.necklaces(period):
            width = game.least_width(block, 10)
            assert (block in one) == (width is not None)
            if width is not None:
                assert one[block] == (6 if width <= 6 else 10)
