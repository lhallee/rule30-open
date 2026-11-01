"""Certificates of the game with cyclic classes for blocks beyond `class_blocks`: the three blocks the plain game closes
at 15 or 16 cells and nothing else excludes (`Rule30Open.Columns.GameBlocksWide`), and the blocks of period 17 that the
class test closes at 16 or 17 cells and nothing else excludes (`Rule30Open.Columns.ClassBlocks17`, `ClassBlocks17Mid`,
`ClassBlocks17Wide` and `ClassBlocks17Cells`; two blocks at 17 cells are not in Lean).

The plain game asks the column left of the repeating one to be a function of the phase, the class test a function of
the cyclic class; every move advances the phase by one, so every cycle of a component has a length divisible by the
period P, the cyclic period d is a multiple of P, and the phase is a function of the class. So a block the plain game
closes at some width, the class test closes at that width too, and `class_certificate.certificate` at the least width
at which the class test closes it gives a certificate of `Rule30Open.ClassGame`. For `00110011111111` that width is 13,
three cells fewer than the plain game needs.

Each certificate is renumbered by `class_blocks.compact` and checked node by node by `class_certificate.check` before it
is written; the Lean text is `class_blocks.block_section` under this module's own header.

    python -m computations.class_blocks_wide                                       # sizes and checks, about 40 s
    python -m computations.class_blocks_wide --lean GameBlocksWide > GameBlocksWide.lean
    python -m computations.class_survey --periods 17 17 --width 16 --workers 2 --out rows17.jsonl   # about 45 min
    python -m computations.class_blocks_wide --report rows17.jsonl   # the blocks closed beyond the game at 14 cells
"""

from __future__ import annotations

import argparse
import json
import sys
import textwrap
from dataclasses import dataclass

from tqdm.auto import tqdm

from computations import class_blocks as cb
from computations import class_certificate as cc
from computations import class_survey as cs

# Each block with the least width at which the class test closes it (`class_survey.least_class_width`). The plain game
# closes the first at 16 cells and the other two at 15 (`game.bad_pairs`), and at no width up to 14.
GAME_BLOCKS = (("00110011111111", 13), ("0000000000111011", 15), ("0000101111111001", 15))
# The blocks of period 17 that the class test closes at 16 cells and nothing else excludes, each with its least width:
# four the plain game does not close at 16 cells, and 00011011111111001, which it closes at 15 and not at 14.
CLASS_BLOCKS_17 = (("00000000001000001", 16), ("00000000010010001", 14), ("00000000011111001", 12),
                   ("00000011011111011", 14), ("00011011111111001", 13))
# The blocks of period 17 that the class test closes at 17 cells and not at 16, and nothing else excludes; the plain game
# closes the last at 17 cells as well.
CELLS_17 = (("01010111111111111", 17), ("00011111111110101", 17), ("01111011111111111", 17))
WIDTH = dict(GAME_BLOCKS + CLASS_BLOCKS_17 + CELLS_17)

# The Lean modules and their blocks, split so that no Lean process holds more than about 180,000 nodes of tables (one
# of 176,000 nodes peaks near 4.8 GB). The other two blocks of `CELLS_17`, with certificates of 205,288 and 227,810
# nodes, are not in Lean.
MODULES = {
    "GameBlocksWide": tuple(b for b, _ in GAME_BLOCKS),
    "ClassBlocks17": ("00000000011111001", "00011011111111001", "00000000010010001"),
    "ClassBlocks17Mid": ("00000011011111011",),
    "ClassBlocks17Wide": ("00000000001000001",),
    "ClassBlocks17Cells": ("01010111111111111",),
}

INTRO = {
    "GameBlocksWide": (
        "The finite game at 15 or 16 cells closes three blocks of period 14 and 16 that its surveys at widths up to 14 "
        "miss and that nothing else in this repository or the kit excludes. The plain game's test is the class test's "
        "case in which the left column is a function of the phase, and the phase is a function of the cyclic class, so "
        "[ClassGame](ClassGame.md)'s certificates prove them: `class_column` holds for any block with a valid "
        "`ClassCert`. Each certificate is at the least width at which the class test closes the block, 13 cells for "
        "`00110011111111` and 15 for the other two, made by `computations/class_blocks_wide.py`."),
    "ClassBlocks17": (
        "[ClassGame](ClassGame.md) proves, for any block with a valid `ClassCert`, that no column of the orbit of a row "
        "with a leftmost 1 repeats it (`class_column`). The class-test survey at period 17 finds five blocks that the "
        "class test closes at 16 cells and that nothing else in this repository or the kit excludes: four that the "
        "plain game does not close at 16 cells, and one that it closes at 15 cells and not at 14. This module proves "
        "the exclusion of {listed}, {each} at the least width at which the class test closes it, made by "
        "`computations/class_blocks_wide.py`. The other blocks are in {others}."),
}
for _module in MODULES:
    if _module.startswith("ClassBlocks17"):
        INTRO[_module] = INTRO["ClassBlocks17"]
INTRO["ClassBlocks17Cells"] = (
    "[ClassGame](ClassGame.md) proves, for any block with a valid `ClassCert`, that no column of the orbit of a row with "
    "a leftmost 1 repeats it (`class_column`). The class-test survey at period 17 and 17 cells finds three blocks that "
    "the class test closes at 17 cells and not at 16 and that nothing else in this repository or the kit excludes. "
    "This module proves the exclusion of {listed}, {each} at 17 cells, made by `computations/class_blocks_wide.py`; "
    "the other two, `00011111111110101` and `01111011111111111`, are not in Lean. The blocks of period 17 that the "
    "class test closes at 16 cells are in {others}.")


def header(module: str, blocks: tuple[str, ...]) -> str:
    """The head of the module `module`: imports, docstring and namespace, as `class_blocks.header` writes them."""
    listed = " and ".join(", ".join(f"`{b}`" for b in blocks).rsplit(", ", 1))
    trio = ("ClassBlocks17", "ClassBlocks17Mid", "ClassBlocks17Wide")
    cells = module.startswith("ClassBlocks17Cells")  # the modules at 17 cells name every other module of period 17
    others = ", ".join(f"[{m}]({m}.md)" for m in MODULES if m != module
                       and (m in trio or cells and m.startswith("ClassBlocks17")))
    each = "from a certificate" if len(blocks) == 1 else "each from a certificate"
    intro = textwrap.fill(INTRO[module].format(listed=listed, each=each, others=others), width=120,
                          break_on_hyphens=False)
    return f"""module

public import Rule30Open.Columns.ClassGame

/-!
# The game with cyclic classes excludes {listed}

{intro}

For each block `b` there is one section with the certificate `cls<b>`, one kernel check per width and phase and one per
phase of the classes, and the theorems `column_not_<b>` (every column of every row with a leftmost 1),
`center_not_<b>` (the center column) and `not_eventually_<b>` (the kit's form).

The natural-language argument is `{module}.md`, beside this file.
-/

@[expose] public section

-- Sequential elaboration: the kernel checks would otherwise run in parallel and stack their memory.
set_option Elab.async false

namespace Rule30Open

open Ruliology.CellularAutomata
open Rule30StripCertificateTable (wordOf)
"""


def certificates(blocks: tuple[str, ...]) -> list[tuple[str, int, cc.Certificate]]:
    """The compacted certificate of every block at its width in `WIDTH`, each checked node by node."""
    out = []
    for block in tqdm(blocks, desc="certificates", file=sys.stderr):
        cert = cb.compact(cc.certificate(block, WIDTH[block]))
        if not cc.check(cert):
            raise ValueError(f"{block} at width {WIDTH[block]}: the certificate fails its check")
        out.append((block, WIDTH[block], cert))
    return out


@dataclass
class Closed:
    """One block that the game or the class test closes at the survey's width: the least width of the class test, the
    least width of the plain game up to the survey's width (0 when it does not close it), and the other exclusions
    that reach it (`class_survey.elsewhere`)."""

    block: str
    class_width: int
    game_width: int
    elsewhere: list[str]


def least_game_width(block: str, width: int) -> int:
    """The least width at which the plain game closes `block`, given that it closes it at `width` (passing at a width
    implies passing at every larger one)."""
    while width > 1 and cs.classify(block, width - 1).game:
        width -= 1
    return width


def report(rows: list[cs.Row]) -> list[Closed]:
    """Every block that the class test closes in `rows` (one survey at one width, as `class_survey.survey` gives them),
    with its least widths and the other exclusions that reach it."""
    out = []
    for row in tqdm([r for r in rows if r.classes], desc="closed blocks", file=sys.stderr):
        game_width = least_game_width(row.block, row.width) if row.game else 0
        out.append(Closed(row.block, cs.least_class_width(row.block, row.width), game_width, cs.elsewhere(row.block)))
    return out


def read_rows(path: str) -> list[cs.Row]:
    """The rows that `class_survey --out` wrote."""
    with open(path) as handle:
        return [cs.Row(**{**d, "components": [tuple(c) for c in d["components"]]}) for d in map(json.loads, handle)]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--lean", choices=list(MODULES), help="print this module of MODULES")
    parser.add_argument("--report", metavar="ROWS", help="the closed blocks of a survey written by class_survey --out")
    parser.add_argument("--settled", type=int, default=14,
                        help="the width up to which the game surveys ran: blocks the game closes within it are known")
    args = parser.parse_args()
    if args.report:
        rows = read_rows(args.report)
        closed = report(rows)
        width = rows[0].width
        print(f"{len(rows)} blocks at width {width}: the game closes {sum(r.game for r in rows)}, the class test "
              f"{len(closed)}")
        for item in closed:
            if item.game_width and item.game_width <= args.settled:
                continue
            kind = f"game at {item.game_width}" if item.game_width else "classes only"
            print(f"{item.block}: {kind}, classes at {item.class_width}; elsewhere: {item.elsewhere or 'none'}")
        return
    if args.lean:
        blocks = MODULES[args.lean]
        print(header(args.lean, blocks))
        for block, width, cert in certificates(blocks):
            print(cb.block_section(block, width, cert).replace(" with 1 ranks and", " with one rank and"))
        print("end Rule30Open")
        return
    for block, width, cert in certificates(tuple(WIDTH)):
        codes = cert.codes[cert.codes >= 0]  # (m,)
        print(f"{block} at {width}: {sum(int((h >= 0).sum()) for h in cert.heights):,} nodes checked, "
              f"{codes.size:,} classed, {int(codes.max()) // cert.base + 1} ranks, base {cert.base}, heights up to "
              f"{max(int(h.max()) for h in cert.heights)}")


if __name__ == "__main__":
    main()
