---
title: The heights of the certificate of 000000000011111001 at width 16, checked in Lean
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ClassBlocks18SplitF2
headline: [cls000000000011111001W16_levels]
kit: new
kit_modules: [Rule30StripCertificateTable]
evidence: [computations/class_blocks_18_split.py, computations/class_blocks_split.py, computations/class_blocks.py, computations/class_certificate.py]
---

# The heights of the certificate of 000000000011111001 at width 16, checked in Lean

The certificate of [the game with cyclic classes](../../findings/columns/class-game.md) that excludes
$000000000011111001$ at 16 cells has 105,158 nodes over the widths and 30,320 for the classes. It is checked over three
modules, so that none holds more than 100,000 nodes of tables. This is part 2.
[ClassBlocks18Split](ClassBlocks18Split.md) gathers the parts and proves that no column of a row with a leftmost 1
eventually repeats $000000000011111001$.

## Statement

- `cls000000000011111001W16_levels`: `cls000000000011111001W16.levelOk j φ = true` for every `j` with `15 ≤ j < 16` and
  every phase `φ < 18`, where `cls000000000011111001W16` is the certificate with the block, the heights of widths 1 to
  16 and no classes.

## Argument

This module holds the heights of width 16, 39,670 nodes, reading those of width 15 from the module before. One
`decide +kernel` per width and phase checks `ClassCert.levelOk`: at width $w$, both extensions of every node whose first
$w - 1$ cells have height 0 at width $w - 1$ have a height, a move from height 0 stays at height 0, and a move from a
positive height lowers it. The check of width $j + 1$ reads only the block and the heights of widths $j$ and $j + 1$, so
it holds on the full certificate too (`ClassCert.levelOk_append`, [ClassSplit](ClassSplit.md)). The module builds in
about 4 minutes with a peak of about 1.7 GB.

## In Lean

`Rule30Open.Columns.ClassBlocks18SplitF2` is written by `computations/class_blocks_18_split.py`, which builds the
certificate with `class_certificate.certificate`, renumbers its ranks with `class_blocks.compact`, checks every
condition node by node in plain Python (`class_certificate.check`), and writes each phase's table in a definition of its
own with the functions of `computations/class_blocks_split.py`.

## Reproduce

```bash
python -m computations.class_blocks_18_split --lean ClassBlocks18SplitF2 > Rule30Open/Columns/ClassBlocks18SplitF2.lean
lake build Rule30Open.Columns.ClassBlocks18SplitF2
```
