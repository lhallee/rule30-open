"""The split modules of `class_blocks_18_split` against the single-module text of `class_blocks.lean_data` and
`class_blocks.block_section`, on the smallest block of period 18 split the same way, and the modules of the repository
against the parts of the generator that do not need a certificate.

On the small block the parts define exactly the tries of the whole certificate, check every width and phase once on a
certificate whose widths are a prefix of the full ones, import in an order that defines every table before it is read,
and the final section states the theorems and the summary that the single-module writer gives."""

from __future__ import annotations

import re
from pathlib import Path

import pytest

from computations import class_blocks as cb
from computations import class_blocks_18 as c18
from computations import class_blocks_18_split as g
from computations import class_blocks_split as cbs

ROOT = Path(__file__).resolve().parent.parent
COLUMNS = ROOT / "Rule30Open" / "Columns"
BLOCK = "001111111111011101"  # the class test closes it at 8 cells (`class_blocks_18.WIDTH`)
RANGES = ((1, 3), (4, 7), (8, 8))


@pytest.fixture
def small(monkeypatch: pytest.MonkeyPatch) -> None:
    """`class_blocks_18_split` on the small block, split in three modules of heights and one of classes."""
    monkeypatch.setattr(g, "SPLITS", {BLOCK: ("SmallSplit", RANGES)})


def definitions(text: str) -> dict[str, str]:
    """The `KeyTrie` definitions of a Lean text, by name."""
    return dict(re.findall(r"def (\S+) : KeyTrie :=\n  (.+)\n", text))


def test_ranges_partition_widths() -> None:
    assert set(g.SPLITS) | {b for blocks in c18.MODULES.values() for b in blocks} == set(c18.WIDTH)
    assert not set(g.SPLITS) & {b for blocks in c18.MODULES.values() for b in blocks}
    for block, (prefix, ranges) in g.SPLITS.items():
        widths = [w for lo, hi in ranges for w in range(lo, hi + 1)]
        assert widths == list(range(1, g.width(block) + 1))
        assert prefix.startswith("ClassBlocks18Split")


def test_parts_match_single_module(small: None) -> None:
    assert g.width(BLOCK) == 8
    cert = g.certificate(BLOCK)
    single = cb.lean_data(cert, f"cls{BLOCK}")
    whole = definitions(single)
    assert len(whole) == (8 + 1) * len(BLOCK)  # one trie per width and phase, and per phase of the classes
    texts = [g.part_module(p) for p in g.parts(BLOCK)]
    split: dict[str, str] = {}
    for text in texts:
        found = definitions(text)
        assert not set(found) & set(split)  # no table twice
        split.update(found)
    assert split == whole
    full = re.search(rf"def cls{BLOCK} : ClassCert where\n(  .*\n)+", single)
    assert full is not None and full.group(0) in texts[-1]  # the full certificate as the single module writes it


def test_every_check_once_on_a_prefix(small: None) -> None:
    period = len(BLOCK)
    parts = g.parts(BLOCK)
    checked: list[tuple[int, int]] = []
    defined: set[str] = set()
    for part, text in zip(parts, (g.part_module(p) for p in parts), strict=True):
        assert (f"public import Rule30Open.Columns.{part.previous}" if part.previous
                else "public import Rule30Open.Columns.ClassGame") in text
        defined |= set(re.findall(r"def (\S+) : List KeyTrie", text))
        levels = re.findall(r"levels := \[(.*)\]", text)
        assert len(levels) == 1
        names = levels[0].split(", ")
        assert names == [f"cls{BLOCK}L{w}" for w in range(1, len(names) + 1)]  # a prefix of the full widths
        assert set(names) <= defined  # every table read is defined here or in a module before
        for _, j, phase in re.findall(r"theorem (\S+)_l(\d+)_(\d+) : \1\.levelOk \2 \3 = true", text):
            assert int(j) < len(names)  # the check reads widths j and j + 1 only
            checked.append((int(j), int(phase)))
        if part.widths is None:
            finals = re.findall(rf"theorem cls{BLOCK}_f(\d+) : cls{BLOCK}\.finalOk \1 = true", text)
            assert sorted(map(int, finals)) == list(range(period))
            assert len(names) == 8 and f"final := cls{BLOCK}F" in text
    assert sorted(checked) == [(j, p) for j in range(8) for p in range(period)]


def test_final_section_matches_single_module(small: None) -> None:
    cert = g.certificate(BLOCK)
    section = g.final_section(BLOCK)
    single = cb.block_section(BLOCK, 8, cert)
    doc = single[:single.index("section\n")]
    assert section.startswith(doc)  # the same summary of the certificate
    for name in ("column_not_", "center_not_", "not_eventually_"):
        start = single.index(f"theorem {name}{BLOCK}")
        stop = single.index("\n\n", start)
        assert single[start:stop] in section
    for lo, hi in RANGES:
        assert f"cls{BLOCK}W{hi}_levels j (by omega) (by omega) φ hφ" in section
        assert f"by_cases h{RANGES.index((lo, hi))} : j < {hi}" in section or hi == 8
    assert "public import Rule30Open.Columns.SmallSplit4\n" in g.final_module()


def test_repository_modules_match_generator() -> None:
    """Each module of the repository holds the parts of the generator's text that need no certificate: its title, its
    import, its checks and, in the final module, the proofs and theorems of every block."""
    for name, part in g.modules().items():
        path = COLUMNS / f"{name}.lean"
        assert path.with_suffix(".md").exists()
        text = path.read_text()
        previous = f"Rule30Open.Columns.{part.previous}" if part.previous else "Rule30Open.Columns.ClassGame"
        assert text.startswith(f"module\n\npublic import {previous}\n\n/-!\n# {g.part_title(part)}\n")
        base = cbs.cert_name(part.block)
        if part.widths is None:
            assert cbs.final_checks(base, len(part.block)) in text
            assert f"def {base} : ClassCert where\n" in text
        else:
            lo, hi = part.widths
            assert cbs.level_checks(cbs.cert_name(part.block, hi), len(part.block), lo, hi) in text
        assert text.endswith("end\n\nend Rule30Open\n")
    final = (COLUMNS / f"{g.FINAL}.lean").read_text()
    for block in g.SPLITS:
        assert f"public import Rule30Open.Columns.{g.parts(block)[-1].module}\n" in final
        assert g.levels_proof(block) + "\n" + g.theorems(block) in final
    assert final.endswith("end\n\nend Rule30Open\n")
