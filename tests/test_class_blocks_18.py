"""The blocks of period 18 of `class_blocks_18` against `game.component_periods` and `game.bad_pairs`, which build the
components by another route, on the cheapest block, the node-by-node check of its certificate, and the Lean text."""

from __future__ import annotations

import pytest

from computations import class_blocks as cb
from computations import class_blocks_18 as c18
from computations import class_certificate as cc
from computations import game

CHEAP = "001111111111011101"


def test_blocks_are_least_rotations() -> None:
    kit = game.kit_blocks(18)
    for block, class_width, game_width in c18.BLOCKS:
        assert len(block) == 18 and game.least_rotation(block) == block and "0" in block and "1" in block
        assert all(block != block[i:] + block[:i] for i in range(1, 18))  # primitive
        assert block not in kit
        assert class_width <= 16 and (game_width == 0 or class_width <= game_width <= 16)
        assert game_width == 0 or game_width > 14  # the game at widths up to 14 does not close it
    assert len(c18.WIDTH) == len(c18.BLOCKS) == 15
    in_lean = [b for blocks in c18.MODULES.values() for b in blocks]
    assert len(set(in_lean)) == len(in_lean) and set(in_lean) <= set(c18.WIDTH)


def test_least_width_by_components() -> None:
    """001111111111011101: the class test closes it at 8 cells and not at 7, and the plain game not at 8."""
    width = c18.WIDTH[CHEAP]
    assert width == 8
    here = game.component_periods(CHEAP, width)
    assert not any(part[3] for part in here) and any(part[2] for part in here)
    assert any(part[3] for part in game.component_periods(CHEAP, width - 1))
    assert game.bad_pairs(CHEAP, width) > 0


def test_certificate_checks() -> None:
    """The certificate of the cheapest block passes the node-by-node check, and a flipped value of the left column
    fails it."""
    cert = cb.compact(cc.certificate(CHEAP, c18.WIDTH[CHEAP]))
    assert cc.check(cert)
    keep = cert.codes[cert.codes >= 0]  # (m,)
    code = next(int(v) for v in keep.tolist() if not (cert.transient >> (v // cert.base)) & 1)
    bad = cc.Certificate(cert.block, cert.heights, cert.codes, cert.base, cert.transient, cert.mods,
                         cert.values ^ (1 << code))
    assert not cc.check(bad)


def test_lean_text(monkeypatch: pytest.MonkeyPatch) -> None:
    """The module text for the cheapest block alone: the header, the certificate and the three theorems."""
    monkeypatch.setattr(c18, "MODULES", {"ClassBlocks18": (CHEAP,)})
    text = c18.header("ClassBlocks18", (CHEAP,))
    ((block, width, cert),) = c18.certificates((CHEAP,))
    text += cb.block_section(block, width, cert)
    assert "public import Rule30Open.Columns.ClassGame" in text
    for name in ("column_not_", "center_not_", "not_eventually_"):
        assert f"theorem {name}{CHEAP}" in text
    assert text.count("decide +kernel") == 18 * (width + 1)  # one per width and phase, one per phase of the classes
