"""Certificates of the game with cyclic classes that are too large for one Lean module, checked over several.

The two blocks of period 17 that the class test closes at 17 cells, `00011111111110101` and `01111011111111111`, have
certificates of 205,288 and 227,810 nodes over the widths and 58,385 and 65,607 nodes for the classes
(`class_blocks_wide`). One module of 175,714 + 51,430 nodes peaks near 4.8 GB, so each certificate is split over three
modules: widths 1 to 15, widths 16 and 17, and the classes. The check of width `j + 1`, `ClassCert.levelOk j`, reads
only the block and the heights of widths `j` and `j + 1`, so each module defines its own heights and checks them on a
certificate whose widths are a prefix of the full ones, importing the heights of the width before from the module
before. The module of the classes defines the full certificate and checks `ClassCert.finalOk`. The final module,
`ClassBlocks17Split`, carries the checks of the widths to the full certificate with `ClassCert.levelOk_append`
(`Rule30Open.Columns.ClassSplit`) and applies `class_column`.

Each certificate is `class_certificate.certificate` at 17 cells, renumbered by `class_blocks.compact` and checked
node by node by `class_certificate.check` before it is written.

    python -m computations.class_blocks_split                                  # sizes of every part, checked, 20 s
    python -m computations.class_blocks_split --lean ClassBlocks17SplitA1 > Rule30Open/Columns/ClassBlocks17SplitA1.lean
    python -m computations.class_blocks_split --lean ClassBlocks17Split > Rule30Open/Columns/ClassBlocks17Split.lean
"""

from __future__ import annotations

import argparse
import functools
import sys
import textwrap
from dataclasses import dataclass

from tqdm.auto import tqdm

from computations import class_blocks as cb
from computations import class_certificate as cc

WIDTH = 17
# Each block with the prefix of its modules and the widths of each module of heights; the module after them holds the
# classes. The parts hold 58,385 to 140,650 nodes of tables each and peak at 2.1 to 4.1 GB in Lean.
SPLITS: dict[str, tuple[str, tuple[tuple[int, int], ...]]] = {
    "00011111111110101": ("ClassBlocks17SplitA", ((1, 15), (16, 17))),
    "01111011111111111": ("ClassBlocks17SplitB", ((1, 15), (16, 17))),
}
FINAL = "ClassBlocks17Split"
NUMBERS = {2: "two", 3: "three", 4: "four", 5: "five", 6: "six"}


@dataclass
class Part:
    """One module of one block: `widths` is (lo, hi) for a module of heights and None for the module of the classes."""

    block: str
    module: str
    index: int
    widths: tuple[int, int] | None
    previous: str | None


def parts(block: str) -> list[Part]:
    """The modules of `block`, in import order."""
    prefix, ranges = SPLITS[block]
    out: list[Part] = []
    for i, widths in enumerate(list(ranges) + [None], start=1):
        out.append(Part(block, f"{prefix}{i}", i, widths, out[-1].module if out else None))
    return out


def modules() -> dict[str, Part]:
    """Every module of a part, by name."""
    return {p.module: p for block in SPLITS for p in parts(block)}


def certificate(block: str) -> cc.Certificate:
    """The compacted certificate of `block` at `WIDTH` cells, checked node by node."""
    return _certificate(block, WIDTH)


@functools.cache
def _certificate(block: str, width: int) -> cc.Certificate:
    """The compacted certificate of `block` at `width` cells, checked node by node."""
    cert = cb.compact(cc.certificate(block, width))
    if not cc.check(cert):
        raise ValueError(f"{block} at width {width}: the certificate fails its check")
    return cert


def cert_name(block: str, hi: int | None = None) -> str:
    """The Lean name of the certificate of `block` with widths 1 .. `hi` (the full certificate when `hi` is None)."""
    return f"cls{block}" if hi is None else f"cls{block}W{hi}"


def tries(cert: cc.Certificate, ident: str, table_width: int) -> str:
    """One table of the certificate as per-phase `KeyTrie` definitions `<ident>_<phase>` and the list `<ident>`, as
    `class_blocks.lean_data` writes them; `table_width` 0 is the table of the classes."""
    period = len(cert.block)
    array = cert.codes if table_width == 0 else cert.heights[table_width - 1]  # (P 2^w,)
    w = len(cert.heights) if table_width == 0 else table_width
    out = [f"open KeyTrie in\ndef {ident}_{phase} : KeyTrie :=\n  {trie}\n"
           for phase, trie in enumerate(cc.phase_tries(array, period, w))]
    names = ", ".join(f"{ident}_{phase}" for phase in range(period))
    out.append(f"def {ident} : List KeyTrie := [{names}]\n")
    return "\n".join(out)


def cert_def(cert: cc.Certificate, name: str, hi: int, final: str) -> str:
    """The `ClassCert` with the heights of widths 1 .. `hi` and the classes `final`."""
    base = cert_name(cert.block)
    period = len(cert.block)
    levels = ", ".join(f"{base}L{w}" for w in range(1, hi + 1))
    return (f"def {name} : ClassCert where\n  block := wordOf {period} 0b{cert.block}\n  levels := [{levels}]\n"
            f"  final := {final}\n  base := {cert.base}\n  transient := 0x{cert.transient:x}\n"
            f"  mods := 0x{cert.mods:x}\n  values := 0x{cert.values:x}\n")


def level_checks(name: str, period: int, lo: int, hi: int) -> str:
    """One kernel check per width `lo .. hi` and phase on the certificate `name`, and `<name>_levels`, which gathers
    them for `lo - 1 <= j < hi`."""
    out = []
    for j in range(lo - 1, hi):
        for phase in range(period):
            out.append(f"set_option maxHeartbeats 0 in\ntheorem {name}_l{j}_{phase} : {name}.levelOk {j} {phase} = "
                       f"true := by\n  decide +kernel\n")
        cases = "".join(f"  | {phase}, _ => {name}_l{j}_{phase}\n" for phase in range(period))
        out.append(f"theorem {name}_l{j} : ∀ φ, φ < {period} → {name}.levelOk {j} φ = true\n{cases}"
                   f"  | _ + {period}, h => absurd h (by omega)\n")
    below = "".join(f"  | {j}, h, _ => absurd h (by omega)\n" for j in range(lo - 1))
    cases = "".join(f"  | {j}, _, _ => {name}_l{j}\n" for j in range(lo - 1, hi))
    span = f"W{widths_phrase(lo, hi)[1:]} pass" + ("es" if lo == hi else "")
    out.append(f"/-- {span} at every phase. -/\n"
               f"theorem {name}_levels :\n"
               f"    ∀ j, {lo - 1} ≤ j → j < {hi} → ∀ φ, φ < {period} → {name}.levelOk j φ = true\n"
               f"{below}{cases}  | _ + {hi}, _, h => absurd h (by omega)\n")
    return "\n".join(out)


def final_checks(name: str, period: int) -> str:
    """One kernel check per phase of the classes, and `<name>_f`, which gathers them."""
    out = [f"set_option maxHeartbeats 0 in\ntheorem {name}_f{phase} : {name}.finalOk {phase} = true := by\n"
           f"  decide +kernel\n" for phase in range(period)]
    cases = "".join(f"  | {phase}, _ => {name}_f{phase}\n" for phase in range(period))
    out.append(f"/-- The classes pass at every phase. -/\ntheorem {name}_f : ∀ φ, φ < {period} → {name}.finalOk φ = "
               f"true\n{cases}  | _ + {period}, h => absurd h (by omega)\n")
    return "\n".join(out)


HEAD = """module

public import {imports}

/-!
# {title}

{intro}

The natural-language argument is `{module}.md`, beside this file.
-/

@[expose] public section

-- Sequential elaboration: the kernel checks would otherwise run in parallel and stack their memory.
set_option Elab.async false

namespace Rule30Open

open Ruliology.CellularAutomata
open Rule30StripCertificateTable (wordOf)
"""


def nodes(cert: cc.Certificate, widths: tuple[int, int] | None) -> int:
    """The entries of the tables of one part."""
    if widths is None:
        return int((cert.codes >= 0).sum())
    return sum(int((cert.heights[w - 1] >= 0).sum()) for w in range(widths[0], widths[1] + 1))


def widths_phrase(lo: int, hi: int) -> str:
    """The widths lo .. hi in words."""
    if lo == hi:
        return f"width {lo}"
    return f"widths {lo} and {hi}" if hi == lo + 1 else f"widths {lo} to {hi}"


def part_title(part: Part) -> str:
    """The heading of one part's module."""
    if part.widths is None:
        return f"The classes of the certificate of {part.block} at {WIDTH} cells"
    lo, hi = part.widths
    span = widths_phrase(lo, hi)
    return f"The heights of the certificate of {part.block} at {span}"


def part_module(part: Part) -> str:
    """The Lean text of one part."""
    cert = certificate(part.block)
    period, base = len(part.block), cert_name(part.block)
    imports = f"Rule30Open.Columns.{part.previous}" if part.previous else "Rule30Open.Columns.ClassGame"
    if part.widths is None:
        body = (f"the classes on the {nodes(cert, None):,} nodes of height 0 at {WIDTH} cells and the full "
                f"certificate `{base}`, whose widths come from the modules before, and checks `ClassCert.finalOk` at "
                f"every phase (`{base}_f`)")
    else:
        lo, hi = part.widths
        span = widths_phrase(lo, hi)
        body = (f"the heights of {span}, {nodes(cert, part.widths):,} nodes, and checks "
                f"`ClassCert.levelOk` there at every phase on the certificate `{cert_name(part.block, hi)}`, "
                f"whose widths are the first {hi} of the full certificate (`{cert_name(part.block, hi)}_levels`)")
    intro = textwrap.fill(
        f"The certificate of [ClassGame](ClassGame.md) for `{part.block}` at {WIDTH} cells has "
        f"{nodes(cert, (1, WIDTH)):,} nodes over the widths and {nodes(cert, None):,} for the classes, too many for "
        f"one module, so it is checked over {NUMBERS[len(parts(part.block))]} modules. This one, part {part.index}, "
        f"defines {body}. "
        f"[{FINAL}]({FINAL}.md) gathers the parts and proves the exclusion of the block.",
        width=120, break_on_hyphens=False)
    out = [HEAD.format(imports=imports, title=part_title(part), intro=intro, module=part.module), "section"]
    if part.widths is None:
        out.append(tries(cert, f"{base}F", 0))
        out.append(cert_def(cert, base, WIDTH, f"{base}F"))
        out.append(final_checks(base, period))
    else:
        lo, hi = part.widths
        for w in tqdm(range(lo, hi + 1), desc="tries", file=sys.stderr):
            out.append(tries(cert, f"{base}L{w}", w))
        name = cert_name(part.block, hi)
        out.append(cert_def(cert, name, hi, "[]"))
        out.append(level_checks(name, period, lo, hi))
    out.append("end\n\nend Rule30Open")
    return "\n".join(out)


def final_section(block: str) -> str:
    """The section of the final module for one block: the widths carried to the full certificate, its validity and
    the headline theorems."""
    cert = certificate(block)
    period, name = len(block), cert_name(block)
    word = f"wordOf {period} 0b{block}"
    level_parts = [p for p in parts(block) if p.widths is not None]
    lines = [f"/-- Every width passes at every phase on the full certificate of `{block}`. -/",
             f"theorem {name}_levels :\n    ∀ j, j < {WIDTH} → ∀ φ, φ < {period} → {name}.levelOk j φ = true := by",
             "  intro j hj φ hφ"]
    for k, part in enumerate(level_parts):
        hi = part.widths[1]
        sub = cert_name(block, hi)
        rest = ", ".join(f"{name}L{w}" for w in range(hi + 1, WIDTH + 1))
        step = [f"have hl : {sub}.levels.length = {hi} := rfl",
                f"rw [ClassCert.levelOk_append {sub} {name}\n      [{rest}] rfl rfl (by omega) φ]",
                f"exact {sub}_levels j (by omega) (by omega) φ hφ"]
        if k < len(level_parts) - 1:
            lines.append(f"  by_cases h{k} : j < {hi}")
            lines.append("  · " + "\n    ".join(step))
        else:
            lines.append("  " + "\n  ".join(step))
    levels = "\n".join(lines) + "\n"
    valid = (f"/-- The certificate of `{block}` passes at every width and phase. -/\n"
             f"theorem {name}_valid : {name}.Valid := by\n"
             f"  have hP : {name}.block.length = {period} := Rule30StripCertificateTable.wordOf_length _ _\n"
             f"  have hW : {name}.levels.length = {WIDTH} := rfl\n"
             f"  exact ⟨by omega, by omega, fun j φ hj hφ => {name}_levels j (by omega) φ (by omega),\n"
             f"    fun φ hφ => {name}_f φ (by omega)⟩\n")
    column = (
        f"/-- **No column repeats {block}.** In the orbit of a row with a leftmost 1, no column repeats the block\n"
        f"`{block}`, from any time `T` on and read from any phase. -/\n"
        f"theorem column_not_{block} (init : Int → Bool) (m : Int) (hm : init m = true)\n"
        f"    (hz : ∀ x : Int, x < m → init x = false) (k : Int) (T shift : Nat)\n"
        f"    (h : ∀ t : Nat, T ≤ t → evolve init t k = ({word}).getD ((t + shift) % {period}) false) : False :=\n"
        f"  class_column init m hm hz {name} {name}_valid k T shift fun t ht => by\n"
        f"    rw [h t ht]\n"
        f"    show _ = bit ({word}) ((t + shift) % ({word}).length)\n"
        f"    rw [bit_eq_getD, Rule30StripCertificateTable.wordOf_length]\n")
    center = (
        f"/-- **The center column does not repeat {block}**, from any time `T` on and read from any phase. -/\n"
        f"theorem center_not_{block} (T shift : Nat)\n"
        f"    (h : ∀ t : Nat, T ≤ t → Rule30Prize.center t = ({word}).getD ((t + shift) % {period}) false) :\n"
        f"    False :=\n"
        f"  column_not_{block} single 0 rfl (fun x hx => decide_eq_false (by omega)) 0 T shift fun t ht => by\n"
        f"    rw [evolve_single_center, h t ht]\n")
    kit = (f"/-- The same in the kit's form: `{block}` is not an `EventuallyWord` of the center column. -/\n"
           f"theorem not_eventually_{block} : ¬ Rule30StripCertificates.EventuallyWord ({word}) :=\n"
           f"  class_not_eventuallyWord {name} {name}_valid\n")
    heights = max(int(h.max()) for h in cert.heights)
    ranks = int(cert.codes.max()) // cert.base + 1
    mods = sorted({(cert.mods >> (8 * r)) & 255 for r in range(ranks)} - {0})
    moduli = " and ".join(", ".join(map(str, mods)).rsplit(", ", 1))
    doc = (f"/-! ### The block {block} at {WIDTH} cells\n\nWidths 1 to {WIDTH} check {nodes(cert, (1, WIDTH)):,} "
           f"nodes, "
           f"with heights up to {heights}; the classes cover\nthe {nodes(cert, None):,} nodes of height 0 at {WIDTH} "
           f"cells, with {ranks} ranks and labels modulo {moduli}. -/\n")
    return f"{doc}\nsection\n{levels}\n{valid}\n{column}\n{center}\n{kit}\nend\n"


def final_module() -> str:
    """The Lean text of the module that gathers the parts."""
    blocks = list(SPLITS)
    last = [parts(b)[-1].module for b in blocks]
    imports = "\n".join(["Rule30Open.Columns.ClassSplit"] + [f"public import Rule30Open.Columns.{m}" for m in last])
    listed = " and ".join(f"`{b}`" for b in blocks)
    links = ", ".join(f"[{p.module}]({p.module}.md)" for b in blocks for p in parts(b))
    intro = textwrap.fill(
        f"[ClassGame](ClassGame.md) proves, for any block with a valid `ClassCert`, that no column of the orbit of a "
        f"row with a leftmost 1 repeats it (`class_column`). The class-test survey at period 17 and 17 cells finds "
        f"three blocks that the class test closes at 17 cells and not at 16 and that nothing else in this repository "
        f"or the kit excludes. This module proves the exclusion of {listed}, whose certificates at 17 cells are "
        f"checked over the modules {links}, made by `computations/class_blocks_split.py`. "
        f"`ClassCert.levelOk_append` ([ClassSplit](ClassSplit.md)) carries the checks of the widths to the full "
        f"certificates. The third block, `01010111111111111`, is in [ClassBlocks17Cells](ClassBlocks17Cells.md).",
        width=120, break_on_hyphens=False)
    intro += ("\n\nFor each block `b` there is one section with `cls<b>_levels`, `cls<b>_valid` and the theorems "
              "`column_not_<b>`\n(every column of every row with a leftmost 1), `center_not_<b>` (the center column) "
              "and\n`not_eventually_<b>` (the kit's form).")
    out = [HEAD.format(imports=imports, title=f"The game with cyclic classes excludes {listed}", intro=intro,
                       module=FINAL)]
    out += [final_section(b) for b in blocks]
    out.append("end Rule30Open")
    return "\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--lean", choices=list(modules()) + [FINAL], help="print this module")
    args = parser.parse_args()
    if args.lean == FINAL:
        print(final_module())
        return
    if args.lean:
        print(part_module(modules()[args.lean]))
        return
    for block in tqdm(SPLITS, desc="certificates", file=sys.stderr):
        cert = certificate(block)
        for part in parts(block):
            print(f"{part.module}: {part_title(part)}, {nodes(cert, part.widths):,} nodes")


if __name__ == "__main__":
    main()
