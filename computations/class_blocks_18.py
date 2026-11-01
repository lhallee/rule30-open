"""The blocks of period 18 that the game or the class test closes at 16 cells and nothing else excludes, and the
certificates of `Rule30Open.Columns.ClassBlocks18` for the cheapest of them.

`class_survey --periods 18 18 --width 16` classifies the 14,532 primitive blocks of period 18 with both colors. The
plain game at 16 cells closes 147 of them, the 142 of the game blocks of period 17 and 18
(`findings/columns/game-blocks-18.md`) at widths up to 14 and five more, and the class test closes those 147 and ten
more. `class_blocks_wide.report` finds the least
widths and the other exclusions (`class_survey.elsewhere`): none of the fifteen is excluded by the kit, the wall sets or
the limit windows of 14 cells. `BLOCKS` lists them with the least width at which the class test closes each and the
least width at which the plain game does (0 when it does not at 16 cells).

The certificate of each block in Lean is `class_certificate.certificate` at its least class width, renumbered by
`class_blocks.compact` and checked node by node by `class_certificate.check`; the Lean text of each block is
`class_blocks.block_section` under this module's header.

    python -m computations.class_blocks_18                                 # certificate sizes, each checked, 45 s
    python -m computations.class_blocks_18 --lean ClassBlocks18 > Rule30Open/Columns/ClassBlocks18.lean
    python -m computations.class_survey --periods 18 18 --width 16 --workers 2 --out rows18.jsonl   # about 40 min
    python -m computations.class_blocks_wide --report rows18.jsonl   # the fifteen blocks and their least widths
"""

from __future__ import annotations

import argparse
import sys
import textwrap

from tqdm.auto import tqdm

from computations import class_blocks as cb
from computations import class_certificate as cc

# Each block with the least width of the class test and of the plain game (0: not closed by the game at 16 cells), from
# `class_blocks_wide --report` on the survey at 16 cells.
BLOCKS: tuple[tuple[str, int, int], ...] = (
    ("000000000000111011", 15, 0), ("000000000010010011", 15, 0), ("000000000011111001", 16, 0),
    ("000010111111111001", 16, 0), ("000011111111111101", 15, 0), ("001001101111111111", 11, 0),
    ("001010100111111111", 14, 0), ("001011111111110111", 16, 0), ("001111111111011101", 8, 0),
    ("011110111111111111", 15, 0), ("000000000001000001", 16, 16), ("000000000011000101", 15, 16),
    ("000000000100000001", 13, 16), ("000000011011111001", 16, 16), ("001111001111111111", 15, 15),
)
WIDTH = {block: width for block, width, _ in BLOCKS}

# The Lean modules and their blocks: the five with the smallest certificates, 70,573 nodes in the first module and
# 71,447 and 85,421 in the others.
MODULES = {
    "ClassBlocks18": ("001111111111011101", "001001101111111111", "000000000100000001"),
    "ClassBlocks18Mid": ("000000000010010011",),
    "ClassBlocks18Wide": ("000000000000111011",),
}


def header(module: str, blocks: tuple[str, ...]) -> str:
    """The head of the module `module`: imports, docstring and namespace, as `class_blocks.header` writes them."""
    listed = " and ".join(", ".join(f"`{b}`" for b in blocks).rsplit(", ", 1))
    others = ", ".join(f"[{m}]({m}.md)" for m in MODULES if m != module)
    each = "from a certificate" if len(blocks) == 1 else "each from a certificate"
    intro = textwrap.fill(
        "[ClassGame](ClassGame.md) proves, for any block with a valid `ClassCert`, that no column of the orbit of a "
        "row with a leftmost 1 repeats it (`class_column`). The class-test survey at period 18 and 16 cells finds "
        "fifteen blocks that the game or the class test closes and that nothing else in this repository or the kit "
        f"excludes. This module proves the exclusion of {listed}, {each} at the least width at which the class test "
        f"closes it, made by `computations/class_blocks_18.py`. The other blocks of period 18 in Lean are in "
        f"{others}.", width=120, break_on_hyphens=False)
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


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--lean", choices=list(MODULES), help="print this module of MODULES")
    args = parser.parse_args()
    if args.lean:
        blocks = MODULES[args.lean]
        print(header(args.lean, blocks))
        for block, width, cert in certificates(blocks):
            print(cb.block_section(block, width, cert))
        print("end Rule30Open")
        return
    for block, width, cert in certificates(tuple(WIDTH)):
        codes = cert.codes[cert.codes >= 0]  # (m,)
        print(f"{block} at {width}: {sum(int((h >= 0).sum()) for h in cert.heights):,} nodes checked, "
              f"{codes.size:,} classed, {int(codes.max()) // cert.base + 1} ranks, base {cert.base}, heights up to "
              f"{max(int(h.max()) for h in cert.heights)}")


if __name__ == "__main__":
    main()
