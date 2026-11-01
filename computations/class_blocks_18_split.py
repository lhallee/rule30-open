"""The ten blocks of period 18 with the largest certificates among those that the game or the class test closes at 16
cells and nothing else excludes, each certificate checked over several Lean modules.

`class_blocks_18` lists fifteen blocks of period 18 that the game or the class test closes at 16 cells and nothing else
excludes; `Rule30Open.Columns.ClassBlocks18`, `ClassBlocks18Mid` and `ClassBlocks18Wide` prove the five with the
smallest certificates. The other ten have certificates of 87,205 to 194,697 nodes, at the least width at which the
class test closes each (14 to 16 cells). Each is checked as `class_blocks_split` checks the two blocks of period 17 at
17 cells: one or two modules of heights, each checking `ClassCert.levelOk` on a certificate whose widths are a prefix of
the full ones, then a module of the classes, which defines the full certificate and checks `ClassCert.finalOk`. The
final module, `ClassBlocks18Split`, carries the checks of the widths to the full certificates with
`ClassCert.levelOk_append` (`Rule30Open.Columns.ClassSplit`) and applies `class_column`.

A block whose heights hold at most 88,328 nodes has one module of heights (widths 1 to the last); the five larger ones,
all at 16 cells, have two (widths 1 to 15, and width 16). So no module holds more than 98,060 nodes of tables.

Each certificate is `class_certificate.certificate` at the width of `class_blocks_18.WIDTH`, renumbered by
`class_blocks.compact` and checked node by node by `class_certificate.check` before it is written. The tables, the
checks and the certificates are written by the functions of `class_blocks_split`.

    python -m computations.class_blocks_18_split                        # sizes of every part, checked, 45 s
    python -m computations.class_blocks_18_split --lean ClassBlocks18SplitA1 > Rule30Open/Columns/ClassBlocks18SplitA1.lean
    python -m computations.class_blocks_18_split --lean ClassBlocks18Split > Rule30Open/Columns/ClassBlocks18Split.lean
"""

from __future__ import annotations

import argparse
import functools
import sys
import textwrap

from tqdm.auto import tqdm

from computations import class_blocks as cb
from computations import class_blocks_18 as c18
from computations import class_blocks_split as cbs
from computations import class_certificate as cc

# Each block, in increasing size of its certificate, with the prefix of its modules and the widths of each module of
# heights; the module after them holds the classes. The widths end at the block's width in `class_blocks_18.WIDTH`.
SPLITS: dict[str, tuple[str, tuple[tuple[int, int], ...]]] = {
    "001010100111111111": ("ClassBlocks18SplitA", ((1, 14),)),
    "001111001111111111": ("ClassBlocks18SplitB", ((1, 15),)),
    "011110111111111111": ("ClassBlocks18SplitC", ((1, 15),)),
    "000000000011000101": ("ClassBlocks18SplitD", ((1, 15),)),
    "000011111111111101": ("ClassBlocks18SplitE", ((1, 15),)),
    "000000000011111001": ("ClassBlocks18SplitF", ((1, 15), (16, 16))),
    "000000000001000001": ("ClassBlocks18SplitG", ((1, 15), (16, 16))),
    "000010111111111001": ("ClassBlocks18SplitH", ((1, 15), (16, 16))),
    "001011111111110111": ("ClassBlocks18SplitI", ((1, 15), (16, 16))),
    "000000011011111001": ("ClassBlocks18SplitJ", ((1, 15), (16, 16))),
}
FINAL = "ClassBlocks18Split"
# The modules that prove the other five blocks of period 18.
SINGLE = ("ClassBlocks18", "ClassBlocks18Mid", "ClassBlocks18Wide")


def width(block: str) -> int:
    """The number of cells of the certificate of `block`: the least width at which the class test closes it."""
    return c18.WIDTH[block]


def parts(block: str) -> list[cbs.Part]:
    """The modules of `block`, in import order."""
    prefix, ranges = SPLITS[block]
    out: list[cbs.Part] = []
    for i, widths in enumerate(list(ranges) + [None], start=1):
        out.append(cbs.Part(block, f"{prefix}{i}", i, widths, out[-1].module if out else None))
    return out


def modules() -> dict[str, cbs.Part]:
    """Every module of a part, by name."""
    return {p.module: p for block in SPLITS for p in parts(block)}


@functools.cache
def certificate(block: str) -> cc.Certificate:
    """The compacted certificate of `block` at `width(block)` cells, checked node by node."""
    cert = cb.compact(cc.certificate(block, width(block)))
    if not cc.check(cert):
        raise ValueError(f"{block} at width {width(block)}: the certificate fails its check")
    return cert


def part_title(part: cbs.Part) -> str:
    """The heading of one part's module."""
    if part.widths is None:
        return f"The classes of the certificate of {part.block} at {width(part.block)} cells"
    return f"The heights of the certificate of {part.block} at {cbs.widths_phrase(*part.widths)}"


def part_module(part: cbs.Part) -> str:
    """The Lean text of one part."""
    cert = certificate(part.block)
    period, base, cells = len(part.block), cbs.cert_name(part.block), width(part.block)
    imports = f"Rule30Open.Columns.{part.previous}" if part.previous else "Rule30Open.Columns.ClassGame"
    if part.widths is None:
        before = "the module before" if part.index == 2 else "the modules before"
        body = (f"the classes on the {cbs.nodes(cert, None):,} nodes of height 0 at {cells} cells and the full "
                f"certificate `{base}`, whose widths come from {before}, and checks `ClassCert.finalOk` at "
                f"every phase (`{base}_f`)")
    else:
        lo, hi = part.widths
        name = cbs.cert_name(part.block, hi)
        body = (f"the heights of {cbs.widths_phrase(lo, hi)}, {cbs.nodes(cert, part.widths):,} nodes, and checks "
                f"`ClassCert.levelOk` there at every phase on the certificate `{name}`, "
                f"whose widths are the first {hi} of the full certificate (`{name}_levels`)")
    intro = textwrap.fill(
        f"The certificate of [ClassGame](ClassGame.md) for `{part.block}` at {cells} cells has "
        f"{cbs.nodes(cert, (1, cells)):,} nodes over the widths and {cbs.nodes(cert, None):,} for the classes. It is "
        f"checked over {cbs.NUMBERS[len(parts(part.block))]} modules, so that none holds more than 100,000 nodes of "
        f"tables. This one, part "
        f"{part.index}, defines {body}. [{FINAL}]({FINAL}.md) gathers the parts and proves the exclusion of the block.",
        width=120, break_on_hyphens=False)
    out = [cbs.HEAD.format(imports=imports, title=part_title(part), intro=intro, module=part.module), "section"]
    if part.widths is None:
        out.append(cbs.tries(cert, f"{base}F", 0))
        out.append(cbs.cert_def(cert, base, cells, f"{base}F"))
        out.append(cbs.final_checks(base, period))
    else:
        lo, hi = part.widths
        for w in tqdm(range(lo, hi + 1), desc="tries", file=sys.stderr):
            out.append(cbs.tries(cert, f"{base}L{w}", w))
        name = cbs.cert_name(part.block, hi)
        out.append(cbs.cert_def(cert, name, hi, "[]"))
        out.append(cbs.level_checks(name, period, lo, hi))
    out.append("end\n\nend Rule30Open")
    return "\n".join(out)


def levels_proof(block: str) -> str:
    """`cls<b>_levels`: every width at every phase on the full certificate, carried from the parts' prefixes. It reads
    only the names of the parts, not the certificate."""
    period, name, cells = len(block), cbs.cert_name(block), width(block)
    level_parts = [p for p in parts(block) if p.widths is not None]
    lines = [f"/-- Every width passes at every phase on the full certificate of `{block}`. -/",
             f"theorem {name}_levels :\n    ∀ j, j < {cells} → ∀ φ, φ < {period} → {name}.levelOk j φ = true := by",
             "  intro j hj φ hφ"]
    for k, part in enumerate(level_parts):
        hi = part.widths[1]
        sub = cbs.cert_name(block, hi)
        rest = ", ".join(f"{name}L{w}" for w in range(hi + 1, cells + 1))
        step = [f"have hl : {sub}.levels.length = {hi} := rfl",
                f"rw [ClassCert.levelOk_append {sub} {name}\n      [{rest}] rfl rfl (by omega) φ]",
                f"exact {sub}_levels j (by omega) (by omega) φ hφ"]
        if k < len(level_parts) - 1:
            lines.append(f"  by_cases h{k} : j < {hi}")
            lines.append("  · " + "\n    ".join(step))
        else:
            lines.append("  " + "\n  ".join(step))
    return "\n".join(lines) + "\n"


def theorems(block: str) -> str:
    """`cls<b>_valid` and the three headline theorems of `block`. They read only the block and its width."""
    period, name, cells = len(block), cbs.cert_name(block), width(block)
    word = f"wordOf {period} 0b{block}"
    valid = (f"/-- The certificate of `{block}` passes at every width and phase. -/\n"
             f"theorem {name}_valid : {name}.Valid := by\n"
             f"  have hP : {name}.block.length = {period} := Rule30StripCertificateTable.wordOf_length _ _\n"
             f"  have hW : {name}.levels.length = {cells} := rfl\n"
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
    return f"{valid}\n{column}\n{center}\n{kit}"


def final_section(block: str) -> str:
    """The section of the final module for one block: the widths carried to the full certificate, its validity and
    the headline theorems."""
    cert, cells = certificate(block), width(block)
    heights = max(int(h.max()) for h in cert.heights)
    ranks = int(cert.codes.max()) // cert.base + 1
    mods = sorted({(cert.mods >> (8 * r)) & 255 for r in range(ranks)} - {0})
    moduli = " and ".join(", ".join(map(str, mods)).rsplit(", ", 1))
    doc = (f"/-! ### The block {block} at {cells} cells\n\nWidths 1 to {cells} check "
           f"{cbs.nodes(cert, (1, cells)):,} nodes, with heights up to {heights}; the classes cover\nthe "
           f"{cbs.nodes(cert, None):,} nodes of height 0 at {cells} cells, with {ranks} ranks and labels modulo "
           f"{moduli}. -/\n")
    return f"{doc}\nsection\n{levels_proof(block)}\n{theorems(block)}\nend\n"


def final_module() -> str:
    """The Lean text of the module that gathers the parts."""
    blocks = list(SPLITS)
    last = [parts(b)[-1].module for b in blocks]
    imports = "\n".join(["Rule30Open.Columns.ClassSplit"] + [f"public import Rule30Open.Columns.{m}" for m in last])
    listed = " and ".join(", ".join(f"`{b}`" for b in blocks).rsplit(", ", 1))
    links = ", ".join(f"[{p.module}]({p.module}.md)" for b in blocks for p in parts(b))
    others = " and ".join(", ".join(f"[{m}]({m}.md)" for m in SINGLE).rsplit(", ", 1))
    intro = textwrap.fill(
        f"[ClassGame](ClassGame.md) proves, for any block with a valid `ClassCert`, that no column of the orbit of a "
        f"row with a leftmost 1 repeats it (`class_column`). The class-test survey at period 18 and 16 cells finds "
        f"fifteen blocks that the game or the class test closes and that nothing else in this repository or the kit "
        f"excludes. This module proves the exclusion of {listed}, each from a certificate at the least width at which "
        f"the class test closes it, checked over the modules {links}, made by "
        f"`computations/class_blocks_18_split.py`. `ClassCert.levelOk_append` ([ClassSplit](ClassSplit.md)) carries "
        f"the checks of the widths to the full certificates. The other five blocks are in {others}.",
        width=120, break_on_hyphens=False)
    intro += ("\n\nFor each block `b` there is one section with `cls<b>_levels`, `cls<b>_valid` and the theorems "
              "`column_not_<b>`\n(every column of every row with a leftmost 1), `center_not_<b>` (the center column) "
              "and\n`not_eventually_<b>` (the kit's form).")
    title = "The game with cyclic classes excludes ten blocks of period 18"
    out = [cbs.HEAD.format(imports=imports, title=title, intro=intro, module=FINAL)]
    out += [final_section(b) for b in tqdm(blocks, desc="certificates", file=sys.stderr)]
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
            print(f"{part.module}: {part_title(part)}, {cbs.nodes(cert, part.widths):,} nodes")


if __name__ == "__main__":
    main()
