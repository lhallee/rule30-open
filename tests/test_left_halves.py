"""Tests of computations.left_halves: the latch and its tree against `held_map`, real orbits and a count of
branches."""

from __future__ import annotations

import numpy as np


def test_left_halves() -> None:
    """`left_halves.tree_failures` against two searches of `held_map`: for 0111 its condition is the kit's C3 and the
    latest failures equal `held_map.tree_failures`; for 01 it is the period-two condition and they equal
    `held_map.first_failures`, which steps every integer of each support directly."""
    from computations import held_map, left_halves
    assert left_halves.pattern("0111") == held_map.PATTERN["0111"] == "*001"
    assert "".join(map(str, left_halves.effective("0111"))) == held_map.EFFECTIVE["0111"]
    for phase in range(4):
        assert left_halves.tree_failures("0111", 24, phase) == held_map.tree_failures("0111", 24, phase, False)
    assert left_halves.pattern("01") == "*1" and left_halves.effective("01") == [0, 0]
    runs = [left_halves.tree_failures("01", 12, phase)[0] for phase in range(2)]
    for support in range(2, 13):
        assert [run[support - 1] for run in runs] == [int(held_map.first_failures(support, phase).max())
                                                      for phase in (0, 1)]
    assert left_halves.pattern("01111") == "*0001" and left_halves.effective("01111") == [0, 1, 1, 1, 0]


def test_left_halves_latch() -> None:
    """The latch along real orbits: from random rows, at any column, it never rejects the readings of the cell left
    of the column and every value it knows is the cell right of it. Then the tree, with and without the latch,
    against stepping every half of up to 9 cells directly, the half held as an integer and driven by the effective
    boundary. For 01 the latch is `period_two_golden`: a white reading at one 0 forces a black one at the next."""
    from computations import left_halves
    from computations.rule30 import step
    rng = np.random.default_rng(30)
    known = 0
    for _ in range(40):
        row = int(rng.integers(0, 1 << 40)) << 200  # 40 random cells, white beyond; bit i is cell 200 + i
        rows = [row]
        for _ in range(120):
            rows.append(step(rows[-1]))
        k = 220 + int(rng.integers(-15, 15))  # a column inside the light cone
        column = "".join(str((r >> k) & 1) for r in rows)  # (121,) as a string
        state = left_halves.UNKNOWN
        for t in range(120):
            state = left_halves.advance(column, t, state, (rows[t] >> (k - 1)) & 1, True)
            assert state is not None
            if state != left_halves.UNKNOWN:
                assert state == (rows[t + 1] >> (k + 1)) & 1
                known += 1
    assert known > 1000

    def direct(block: str, support: int, phase: int, latch: bool) -> int:
        boundary = left_halves.effective(block)
        worst = 0
        for start in range(1 << (support - 1), 1 << support):
            half, state, t = start, left_halves.UNKNOWN, 0  # bit j of `half` is cell -1 - j
            while (state := left_halves.advance(block, t + phase, state, half & 1, latch)) is not None:
                half = (half >> 1) ^ (half | (half << 1) | boundary[(t + phase) % len(block)])
                t += 1
            worst = max(worst, t)
        return worst

    for block in ["01", "001", "011", "0011", "00111", "01011", "000111", "0110111"]:
        for latch in (False, True):
            for phase in range(len(block)):
                tree = left_halves.tree_failures(block, 9, phase, latch)[0]
                assert tree == [direct(block, support, phase, latch) for support in range(1, 10)]
    golden = [left_halves.advance("01", t, s, r, True) for t, s, r in [(0, left_halves.UNKNOWN, 0), (1, 1, 1)]]
    assert golden == [1, 0] and left_halves.advance("01", 2, 0, 0, True) is None


def test_left_halves_entropy() -> None:
    """The automaton of the condition counts the tree's branches: the readings of length m that it allows from a phase,
    the latch state unknown, are as many as the halves the tree keeps through step m - 1. Its entropy is w / P without
    the latch, and for 01 with it the golden condition's log2 of the golden ratio over 2."""
    from computations import left_halves
    for block in ["01", "001", "0011", "00101", "0001011"]:
        for latch in (False, True):
            matrix = left_halves.transfer(block, latch)  # (3P, 3P)
            for phase in range(len(block)):
                counts = np.zeros(3 * len(block))  # (3P,)
                counts[3 * phase + left_halves.UNKNOWN] = 1
                branches = left_halves.tree_failures(block, 14, phase, latch)[1]
                for m in range(1, 15):
                    counts = counts @ matrix  # (3P,)
                    assert counts.sum() == branches[m - 1]
        assert abs(left_halves.entropy(block) - block.count("0") / len(block)) < 1e-9
    assert abs(left_halves.entropy("01", True) - np.log2((1 + 5 ** 0.5) / 2) / 2) < 1e-9
    for block in ["01", "001", "0001", "00111", "0110111"]:  # the window of one cell is the latch, by other code
        rates = [left_halves.window_entropy(block, width) for width in range(1, 6)]
        assert abs(rates[0] - left_halves.entropy(block, True)) < 1e-9
        # consecutive pairs: rates[1:] is one shorter by design; eigenvalues to about 1e-8
        assert all(wide <= narrow + 1e-6 for narrow, wide in zip(rates, rates[1:], strict=False))
