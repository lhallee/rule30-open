"""The split modules of `class_blocks_split` against the single-module text of `class_blocks.lean_data`, on a small
block split the same way: the parts define exactly the tries of the whole certificate, check every width and phase once
on a certificate whose widths are a prefix of the full ones, and import in an order that defines every table before it
is read."""

from __future__ import annotations

import re

import pytest

from computations import class_blocks as cb
from computations import class_blocks_split as cbs

BLOCK, WIDTH = "0000000001101001", 9  # the class test closes it at 9 cells (`class_blocks.WIDTH`)
RANGES = ((1, 4), (5, 8), (9, 9))


@pytest.fixture
def small(monkeypatch: pytest.MonkeyPatch) -> None:
    """`class_blocks_split` on the small block, split in three modules of heights and one of classes."""
    monkeypatch.setattr(cbs, "WIDTH", WIDTH)
    monkeypatch.setattr(cbs, "SPLITS", {BLOCK: ("SmallSplit", RANGES)})


def definitions(text: str) -> dict[str, str]:
    """The `KeyTrie` definitions of a Lean text, by name."""
    return dict(re.findall(r"def (\S+) : KeyTrie :=\n  (.+)\n", text))


def test_ranges_partition_widths() -> None:
    for prefix, ranges in cbs.SPLITS.values():
        widths = [w for lo, hi in ranges for w in range(lo, hi + 1)]
        assert widths == list(range(1, cbs.WIDTH + 1))
        assert prefix.startswith("ClassBlocks17Split")


def test_parts_match_single_module(small: None) -> None:
    assert cb.WIDTH[BLOCK] == WIDTH
    cert = cbs.certificate(BLOCK)
    whole = definitions(cb.lean_data(cert, f"cls{BLOCK}"))
    assert len(whole) == (WIDTH + 1) * len(BLOCK)  # one trie per width and phase, and per phase of the classes
    parts = cbs.parts(BLOCK)
    texts = [cbs.part_module(p) for p in parts]
    split: dict[str, str] = {}
    for text in texts:
        found = definitions(text)
        assert not set(found) & set(split)  # no table twice
        split.update(found)
    assert split == whole


def test_every_check_once_on_a_prefix(small: None) -> None:
    period = len(BLOCK)
    parts = cbs.parts(BLOCK)
    checked: list[tuple[int, int]] = []
    defined: set[str] = set()
    for part, text in zip(parts, (cbs.part_module(p) for p in parts), strict=True):
        assert (f"public import Rule30Open.Columns.{part.previous}" if part.previous
                else "public import Rule30Open.Columns.ClassGame") in text
        defined |= set(re.findall(r"def (\S+) : List KeyTrie", text))
        levels = re.findall(r"levels := \[(.*)\]", text)
        assert len(levels) == 1
        names = levels[0].split(", ")
        assert names == [f"cls{BLOCK}L{w}" for w in range(1, len(names) + 1)]  # a prefix of the full widths
        assert set(names) <= defined  # every table read is defined here or in a module before
        for name, j, phase in re.findall(r"theorem (\S+)_l(\d+)_(\d+) : \1\.levelOk \2 \3 = true", text):
            assert int(j) < len(names)  # the check reads widths j and j + 1 only
            checked.append((int(j), int(phase)))
        if part.widths is None:
            finals = re.findall(rf"theorem cls{BLOCK}_f(\d+) : cls{BLOCK}\.finalOk \1 = true", text)
            assert sorted(map(int, finals)) == list(range(period))
            assert len(names) == WIDTH and f"final := cls{BLOCK}F" in text
    assert sorted(checked) == [(j, p) for j in range(WIDTH) for p in range(period)]


def test_final_module_gathers_parts(small: None) -> None:
    text = cbs.final_module()
    assert "public import Rule30Open.Columns.SmallSplit4" in text
    for lo, hi in RANGES:
        assert f"cls{BLOCK}W{hi}_levels j (by omega) (by omega) φ hφ" in text
        assert f"by_cases h{RANGES.index((lo, hi))} : j < {hi}" in text or hi == WIDTH
    for name in ("column_not_", "center_not_", "not_eventually_"):
        assert f"theorem {name}{BLOCK}" in text
