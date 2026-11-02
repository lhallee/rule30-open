"""The certificates of `class_blocks_wide` against `game.component_periods` and `game.bad_pairs`, which build the
components by another route, on the cheapest block, and the node-by-node check of its certificate."""

from __future__ import annotations

from computations import class_blocks as cb
from computations import class_blocks_wide as cbw
from computations import class_certificate as cc
from computations import game


def test_modules_cover_blocks() -> None:
    in_lean = sorted(b for blocks in cbw.MODULES.values() for b in blocks)
    assert len(set(in_lean)) == len(in_lean) and set(in_lean) <= set(cbw.WIDTH)
    assert set(cbw.WIDTH) - set(in_lean) == {"00011111111110101", "01111011111111111"}
    assert not set(cbw.WIDTH) & set(cb.WIDTH)  # no block twice


def test_least_width_by_components() -> None:
    """00110011111111: the class test closes it at 13 cells and not at 12, and the plain game at neither."""
    block, width = "00110011111111", cbw.WIDTH["00110011111111"]
    assert width == 13
    here = game.component_periods(block, width)
    assert not any(part[3] for part in here) and any(part[2] for part in here)
    assert any(part[3] for part in game.component_periods(block, width - 1))
    assert game.bad_pairs(block, width) > 0


def test_certificate_checks() -> None:
    """The certificate of 00110011111111 passes the node-by-node check, and a flipped value of the left column fails
    it."""
    block = "00110011111111"
    cert = cb.compact(cc.certificate(block, cbw.WIDTH[block]))
    assert cc.check(cert)
    keep = cert.codes[cert.codes >= 0]  # (m,)
    code = next(int(v) for v in keep.tolist() if not (cert.transient >> (v // cert.base)) & 1)
    bad = cc.Certificate(cert.block, cert.heights, cert.codes, cert.base, cert.transient, cert.mods,
                         cert.values ^ (1 << code))
    assert not cc.check(bad)


def test_report_least_widths() -> None:
    """`report` gives the least widths that `game.bad_pairs` and `game.component_periods` give width by width, and
    reads back the rows that `class_survey --out` writes."""
    import json
    import tempfile
    from dataclasses import asdict

    from computations import class_survey as cs

    rows = [cs.classify(b, 12) for b in ("0000000001", "000000010111", "0011111111", "0101100111")]
    with tempfile.NamedTemporaryFile("w", suffix=".jsonl", delete=False) as handle:
        for row in rows:
            handle.write(json.dumps(asdict(row)) + "\n")
    assert cbw.read_rows(handle.name) == rows
    closed = {item.block: item for item in cbw.report(rows)}
    assert "0101100111" not in closed
    for block, item in closed.items():
        games = [w for w in range(1, 13) if game.bad_pairs(block, w) == 0]
        classes = [w for w in range(1, 13) if not any(part[3] for part in game.component_periods(block, w))]
        assert item.game_width == (games[0] if games else 0)
        assert item.class_width == classes[0]
    assert closed["0000000001"].game_width == 0 and closed["0000000001"].elsewhere == ["kit: padded word"]


def test_period_17_least_width() -> None:
    """00000000011111001: the class test closes it at 12 cells and not at 11, the plain game not at 12, by
    `game.component_periods`, and its certificate passes the node-by-node check."""
    block, width = "00000000011111001", cbw.WIDTH["00000000011111001"]
    assert width == 12 and block in cbw.MODULES["ClassBlocks17"]
    here = game.component_periods(block, width)
    assert not any(part[3] for part in here) and any(part[2] for part in here)
    assert any(part[3] for part in game.component_periods(block, width - 1))
    assert cc.check(cb.compact(cc.certificate(block, width)))
