---
title: The heights of the certificate of 00011111111110101 at widths 16 and 17, checked in Lean
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ClassBlocks17SplitA2
headline: [cls00011111111110101W17_levels]
kit: new
kit_modules: [Rule30StripCertificateTable]
evidence: [computations/class_blocks_split.py, computations/class_blocks.py, computations/class_certificate.py]
---

# The heights of the certificate of 00011111111110101 at widths 16 and 17, checked in Lean

The certificate of [the game with cyclic classes](../../findings/columns/class-game.md) that excludes
$00011111111110101$ at 17 cells has 205,288 nodes over the widths and 58,385 for the classes, too many for one Lean
module ([ClassBlocks17Cells](ClassBlocks17Cells.md), with 175,714 and 51,430, peaks near 4.8 GB), so it is checked over
three modules. This is part 2. [ClassBlocks17Split](ClassBlocks17Split.md) gathers the parts and proves that no column
of a row with a leftmost 1 eventually repeats $00011111111110101$.

## Statement

- `cls00011111111110101W17_levels`: `cls00011111111110101W17.levelOk j φ = true` for every `j` with `15 ≤ j < 17` and
  every phase `φ < 17`, where `cls00011111111110101W17` is the certificate with the block, the heights of widths 1 to 17
  and no classes.

## Argument

This module holds the heights of widths 16 and 17, 119,726 nodes, reading those of width 15 from the module before. One
`decide +kernel` per width and phase checks `ClassCert.levelOk`: at width $w$, both extensions of every node whose first
$w - 1$ cells have height 0 at width $w - 1$ have a height, a move from height 0 stays at height 0, and a move from a
positive height lowers it. The check of width $j + 1$ reads only the block and the heights of widths $j$ and $j + 1$, so
it holds on the full certificate too (`ClassCert.levelOk_append`, [ClassSplit](ClassSplit.md)). The module builds in
about 13 minutes with a peak of about 3.5 GB.

## In Lean

`Rule30Open.Columns.ClassBlocks17SplitA2` is written by `computations/class_blocks_split.py`, which builds the
certificate with `class_certificate.certificate`, renumbers its ranks with `class_blocks.compact`, checks every
condition node by node in plain Python (`class_certificate.check`), and writes each phase's table in a definition of its
own.

## Reproduce

```bash
python -m computations.class_blocks_split --lean ClassBlocks17SplitA2 > Rule30Open/Columns/ClassBlocks17SplitA2.lean
lake build Rule30Open.Columns.ClassBlocks17SplitA2
```
