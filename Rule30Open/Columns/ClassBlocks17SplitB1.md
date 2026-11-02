---
title: The heights of the certificate of 01111011111111111 at widths 1 to 15, checked in Lean
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ClassBlocks17SplitB1
headline: [cls01111011111111111W15_levels]
kit: new
kit_modules: [Rule30StripCertificateTable]
evidence: [computations/class_blocks_split.py, computations/class_blocks.py, computations/class_certificate.py]
---

# The heights of the certificate of 01111011111111111 at widths 1 to 15, checked in Lean

The certificate of [the game with cyclic classes](../../findings/columns/class-game.md) that excludes
$01111011111111111$ at 17 cells has 227,810 nodes over the widths and 65,607 for the classes, too many for one Lean
module ([ClassBlocks17Cells](ClassBlocks17Cells.md), with 175,714 and 51,430, peaks near 4.8 GB), so it is checked over
three modules. This is part 1. [ClassBlocks17Split](ClassBlocks17Split.md) gathers the parts and proves that no column
of a row with a leftmost 1 eventually repeats $01111011111111111$.

## Statement

- `cls01111011111111111W15_levels`: `cls01111011111111111W15.levelOk j φ = true` for every `j` with `0 ≤ j < 15` and
  every phase `φ < 17`, where `cls01111011111111111W15` is the certificate with the block, the heights of widths 1 to 15
  and no classes.

## Argument

This module holds the heights of widths 1 to 15, 87,160 nodes. One `decide +kernel` per width and phase checks
`ClassCert.levelOk`: at width $w$, both extensions of every node whose first $w - 1$ cells have height 0 at width $w -
1$ have a height, a move from height 0 stays at height 0, and a move from a positive height lowers it. The check of
width $j + 1$ reads only the block and the heights of widths $j$ and $j + 1$, so it holds on the full certificate too
(`ClassCert.levelOk_append`, [ClassSplit](ClassSplit.md)). The module builds in about 6 minutes with a peak of about 2.1
GB.

## In Lean

`Rule30Open.Columns.ClassBlocks17SplitB1` is written by `computations/class_blocks_split.py`, which builds the
certificate with `class_certificate.certificate`, renumbers its ranks with `class_blocks.compact`, checks every
condition node by node in plain Python (`class_certificate.check`), and writes each phase's table in a definition of its
own.

## Reproduce

```bash
python -m computations.class_blocks_split --lean ClassBlocks17SplitB1 > Rule30Open/Columns/ClassBlocks17SplitB1.lean
lake build Rule30Open.Columns.ClassBlocks17SplitB1
```
