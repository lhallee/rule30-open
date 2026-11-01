"""The survey of the game with cyclic classes against `game.component_periods` and `game.bad_pairs`, which build the
components and the levels by another route, and against the blocks of class-game.md."""

from __future__ import annotations

import numpy as np
import pytest

from computations import class_survey as cs
from computations import game


@pytest.mark.parametrize("period,width", [(3, 8), (5, 7), (6, 6), (7, 8), (8, 6)])
def test_components_match_game(period: int, width: int) -> None:
    for block in cs.blocks_of(range(period, period + 1)):
        row = cs.classify(block, width)
        found = sorted(game.component_periods(block, width), reverse=True)
        assert row.components == found
        assert row.game == (game.bad_pairs(block, width) == 0)
        assert row.classes == (not any(part[3] for part in found))


def test_random_blocks_match_game() -> None:
    rng = np.random.default_rng(5)
    for _ in range(12):
        period = int(rng.integers(9, 14))
        word = "".join(rng.choice(["0", "1"], size=period).tolist())
        block = game.least_rotation(word)
        width = int(rng.integers(6, 11))
        row = cs.classify(block, width)
        assert row.components == sorted(game.component_periods(block, width), reverse=True)


def test_monotone_in_width() -> None:
    for block in ("00000011", "0000000001", "000000001011", "0000000011"):
        flags = [cs.classify(block, width).classes for width in range(4, 14)]
        assert flags == sorted(flags)  # once closed, closed at every larger width
        games = [cs.classify(block, width).game for width in range(4, 14)]
        assert all(c or not g for c, g in zip(flags, games, strict=True))  # the game closes only what classes close


def test_known_blocks() -> None:
    row = cs.classify("000000001011", 16)
    assert row.classes and not row.game
    assert row.components == [(7312, 12, False, False), (532, 36, True, False), (22, 12, False, False)]
    assert not cs.classify("000000001011", 15).classes
    assert cs.least_class_width("0000000001", 12) == 12
    assert cs.elsewhere("0000000001") == ["kit: padded word"]
    assert cs.elsewhere("000000001011") == []


def test_table_counts() -> None:
    rows = [cs.Row("0001", 6, False, False, []), cs.Row("0011", 6, True, True, []),
            cs.Row("00001", 6, False, True, []), cs.Row("00011", 6, False, False, [])]
    assert cs.table(rows) == {4: (2, 1, 0), 5: (2, 0, 1)}


def test_blocks_least_width() -> None:
    """The smallest certified block: the class test closes it at 9 cells and not at 8, the plain game at neither, by
    `game.component_periods`."""
    from computations import class_blocks as cb

    block, width = "0000000001101001", cb.WIDTH["0000000001101001"]
    assert width == 9
    assert not any(part[3] for part in game.component_periods(block, width))
    assert any(part[2] for part in game.component_periods(block, width))
    assert any(part[3] for part in game.component_periods(block, width - 1))
    assert cs.least_class_width(block, 12) == width
    assert sorted(b for blocks in cb.MODULES.values() for b in blocks) == sorted(cb.WIDTH)


def test_compact_certificate() -> None:
    """Renumbering the ranks keeps the node-by-node check, and the check refuses a certificate with a wrong value."""
    from computations import class_blocks as cb
    from computations import class_certificate as cc

    raw = cc.certificate("0000000001101001", 9)
    small = cb.compact(raw)
    assert cc.check(raw) and cc.check(small)
    on = raw.codes >= 0  # (P 2^W,)
    pairs = np.unique(np.stack([raw.codes[on] // raw.base, small.codes[on] // small.base]), axis=1)  # (2, ranks)
    assert (np.diff(pairs[0]) > 0).all() and (np.diff(pairs[1]) > 0).all()  # the ranks keep their order
    assert np.array_equal(raw.codes[on] % raw.base, small.codes[on] % small.base)  # and the labels
    assert int(small.codes.max()) // small.base + 1 == np.unique(raw.codes[on] // raw.base).size
    recurrent = [r for r in range(int(small.codes.max()) // small.base + 1) if not (small.transient >> r) & 1]
    flipped = small.values ^ (1 << (recurrent[0] * small.base))
    assert not cc.check(cc.Certificate(small.block, small.heights, small.codes, small.base, small.transient,
                                       small.mods, flipped))
