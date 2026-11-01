"""The certificates of `Rule30Open.Columns.ClassBlocks`: the game with cyclic classes for the ten blocks of period 13
to 16 that `class_survey` finds closed by the classes at 16 cells and by nothing else in the repository or the kit.

Each certificate is `class_certificate.certificate` at the block's least width, with its ranks renumbered 0, 1, 2, ...
in their order (`compact`): the conditions of `ClassCert` compare ranks only by their order, so the renumbered
certificate passes exactly when the original does, and its numbers `transient`, `mods` and `values` are shorter. The
blocks are split over modules (`MODULES`) so that no Lean process holds more than a few of the tables.

    python -m computations.class_blocks                                   # sizes and node-by-node check, about 20 s
    python -m computations.class_blocks --lean ClassBlocks > ClassBlocks.lean   # one module of `MODULES`
"""

from __future__ import annotations

import argparse
import sys
import textwrap

import numpy as np
from tqdm.auto import tqdm

from computations import class_certificate as cc

# The blocks the class test closes at width 16 and nothing else does, each with the least width at which the class test
# closes it (`class_survey.least_class_width`).
BLOCKS = (
    ("0000001011011", 15), ("0001011111011", 15), ("00100101111111", 15), ("000000001101001", 11),
    ("0000000001101001", 9), ("0000000011011001", 14), ("0000001101111011", 14), ("0001101111111001", 16),
    ("0011110011111111", 13), ("0110110111111111", 16),
)
WIDTH = dict(BLOCKS)

# The Lean modules and their blocks, a few per module so that one Lean process holds a few tables at a time.
MODULES = {
    "ClassBlocks": ("000000001101001", "0000000001101001", "0011110011111111", "0000000011011001"),
    "ClassBlocks13": ("0000001011011", "0001011111011"),
    "ClassBlocks14": ("00100101111111",),
    "ClassBlocks16": ("0000001101111011", "0110110111111111"),
    "ClassBlocks16Wide": ("0001101111111001",),
}


def compact(cert: cc.Certificate) -> cc.Certificate:
    """The certificate with its ranks renumbered 0, 1, 2, ... in their order."""
    base = cert.base
    on = cert.codes >= 0  # (P 2^W,)
    rank, label = cert.codes[on] // base, cert.codes[on] % base  # (m,), (m,)
    old = np.unique(rank)  # (k,), the ranks in use, increasing
    new_rank = np.searchsorted(old, rank)  # (m,)
    codes = cert.codes.copy()  # (P 2^W,)
    codes[on] = new_rank * base + label
    transient = sum(1 << i for i, r in enumerate(old.tolist()) if (cert.transient >> r) & 1)
    mods = sum(((cert.mods >> (8 * r)) & 255) << (8 * i) for i, r in enumerate(old.tolist()))
    values = 0
    for i, r in enumerate(old.tolist()):
        values |= ((cert.values >> (r * base)) & ((1 << base) - 1)) << (i * base)
    return cc.Certificate(cert.block, cert.heights, codes, base, transient, mods, values)


def lean_data(cert: cc.Certificate, name: str) -> str:
    """The certificate as Lean definitions, as `class_certificate.lean_data` writes them but with each phase's trie in a
    definition of its own, `<table>_<phase>`: a list literal of sixteen large tries exceeds the elaborator's recursion
    depth."""
    period, width = len(cert.block), len(cert.heights)
    out = []
    tables = [(f"{name}L{w}", cert.heights[w - 1], w) for w in range(1, width + 1)] + [(f"{name}F", cert.codes, width)]
    for ident, table, w in tqdm(tables, desc="tries", file=sys.stderr):
        for phase, trie in enumerate(cc.phase_tries(table, period, w)):
            out.append(f"open KeyTrie in\ndef {ident}_{phase} : KeyTrie :=\n  {trie}\n")
        names = ", ".join(f"{ident}_{phase}" for phase in range(period))
        out.append(f"def {ident} : List KeyTrie := [{names}]\n")
    names = ", ".join(f"{name}L{w}" for w in range(1, width + 1))
    out.append(f"def {name} : ClassCert where\n  block := wordOf {period} 0b{cert.block}\n  levels := [{names}]\n"
               f"  final := {name}F\n  base := {cert.base}\n  transient := 0x{cert.transient:x}\n"
               f"  mods := 0x{cert.mods:x}\n  values := 0x{cert.values:x}\n")
    return "\n".join(out)


def block_section(block: str, width: int, cert: cc.Certificate) -> str:
    """The Lean section of one block: the certificate, its checks and the headline theorems."""
    period, name = len(block), f"cls{block}"
    word = f"wordOf {period} 0b{block}"
    checked = sum(int((h >= 0).sum()) for h in cert.heights)
    final = int((cert.codes >= 0).sum())
    ranks = int(cert.codes.max()) // cert.base + 1
    mods = sorted({(cert.mods >> (8 * r)) & 255 for r in range(ranks)} - {0})
    moduli = " and ".join(", ".join(map(str, mods)).rsplit(", ", 1))
    out = [f"/-! ### The block {block} at {width} cells\n\nWidths 1 to {width} check {checked:,} nodes, with heights "
           f"up to {max(int(h.max()) for h in cert.heights)}; the classes cover\nthe {final:,} nodes of height 0 at "
           f"{width} cells, with {ranks} ranks and labels modulo {moduli}. -/\n",
           "section", lean_data(cert, name), cc.lean_checks(name, period, width)]
    out.append(
        f"/-- **No column repeats {block}.** In the orbit of a row with a leftmost 1, no column repeats the block\n"
        f"`{block}`, from any time `T` on and read from any phase. -/\n"
        f"theorem column_not_{block} (init : Int → Bool) (m : Int) (hm : init m = true)\n"
        f"    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T shift : Nat)\n"
        f"    (h : ∀ t : Nat, T ≤ t → evolve init t k = ({word}).getD ((t + shift) % {period}) false) : False :=\n"
        f"  class_column init m hm hz {name} {name}_valid k T shift fun t ht => by\n"
        f"    rw [h t ht]\n"
        f"    show _ = bit ({word}) ((t + shift) % ({word}).length)\n"
        f"    rw [bit_eq_getD, Rule30StripCertificateTable.wordOf_length]\n")
    out.append(
        f"/-- **The center column does not repeat {block}**, from any time `T` on and read from any phase. -/\n"
        f"theorem center_not_{block} (T shift : Nat)\n"
        f"    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = ({word}).getD ((t + shift) % {period}) false) :\n"
        f"    False :=\n"
        f"  column_not_{block} single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T shift fun t ht => by\n"
        f"    rw [evolve_single_center, h t ht]\n")
    out.append(
        f"/-- The same in the kit's form: `{block}` is not an `EventuallyWord` of the center column. -/\n"
        f"theorem not_eventually_{block} : ¬ Rule30StripCertificates.EventuallyWord ({word}) :=\n"
        f"  class_not_eventuallyWord {name} {name}_valid\n")
    out.append("end\n")
    return "\n".join(out)


def header(module: str, blocks: tuple[str, ...]) -> str:
    """The head of the module `module`: imports, docstring and namespace."""
    listed = " and ".join(", ".join(f"`{b}`" for b in blocks).rsplit(", ", 1))
    others = ", ".join(f"[{m}]({m}.md)" for m in MODULES if m != module)
    each = "from a certificate" if len(blocks) == 1 else "each from a certificate"
    intro = textwrap.fill(
        "[ClassGame](ClassGame.md) proves, for any block with a valid `ClassCert`, that no column of the orbit of a "
        "row with a leftmost 1 repeats it (`class_column`). The class-test survey at periods 13 to 16 finds ten "
        "blocks that the class test closes at 16 cells and that nothing else in this repository or the kit excludes. "
        "This module "
        f"proves the exclusion of {listed}, {each} at the least width that closes it, made by "
        f"`computations/class_blocks.py`. The other blocks are in {others}.", width=120, break_on_hyphens=False)
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
    """The compacted certificate of every block at its width in `BLOCKS`, each checked node by node."""
    out = []
    for block in tqdm(blocks, desc="certificates", file=sys.stderr):
        cert = compact(cc.certificate(block, WIDTH[block]))
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
            print(block_section(block, width, cert))
        print("end Rule30Open")
        return
    for block, width, cert in certificates(tuple(WIDTH)):
        codes = cert.codes[cert.codes >= 0]  # (m,)
        print(f"{block} at {width}: {sum(int((h >= 0).sum()) for h in cert.heights):,} nodes checked, "
              f"{codes.size:,} classed, {int(codes.max()) // cert.base + 1} ranks, base {cert.base}, heights up to "
              f"{max(int(h.max()) for h in cert.heights)}")


if __name__ == "__main__":
    main()
