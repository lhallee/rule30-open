---
title: The heights of the certificate of 011110111111111111 at widths 1 to 15, checked in Lean
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ClassBlocks18SplitC1
headline: [cls011110111111111111W15_levels]
kit: new
kit_modules: [Rule30StripCertificateTable]
evidence: [computations/class_blocks_18_split.py, computations/class_blocks_split.py, computations/class_blocks.py, computations/class_certificate.py]
---

# The heights of the certificate of 011110111111111111 at widths 1 to 15, checked in Lean

The certificate of [the game with cyclic classes](../../findings/columns/class-game.md) that excludes
$011110111111111111$ at 15 cells has 80,736 nodes over the widths and 20,080 for the classes. It is checked over two
modules, so that none holds more than 100,000 nodes of tables. This is part 1.
[ClassBlocks18Split](ClassBlocks18Split.md) gathers the parts and proves that no column of a row with a leftmost 1
eventually repeats $011110111111111111$.

## Statement

- `cls011110111111111111W15_levels`: `cls011110111111111111W15.levelOk j φ = true` for every `j` with `0 ≤ j < 15` and
  every phase `φ < 18`, where `cls011110111111111111W15` is the certificate with the block, the heights of widths 1 to
  15 and no classes.

## Argument

This module holds the heights of widths 1 to 15, 80,736 nodes. One `decide +kernel` per width and phase checks
`ClassCert.levelOk`: at width $w$, both extensions of every node whose first $w - 1$ cells have height 0 at width
$w - 1$ have a height, a move from height 0 stays at height 0, and a move from a positive height lowers it. The check of
width $j + 1$ reads only the block and the heights of widths $j$ and $j + 1$, so it holds on the full certificate too
(`ClassCert.levelOk_append`, [ClassSplit](ClassSplit.md)). The module builds in about 5 minutes with a peak of about
2.0 GB.

## In Lean

`Rule30Open.Columns.ClassBlocks18SplitC1` is written by `computations/class_blocks_18_split.py`, which builds the
certificate with `class_certificate.certificate`, renumbers its ranks with `class_blocks.compact`, checks every
condition node by node in plain Python (`class_certificate.check`), and writes each phase's table in a definition of its
own with the functions of `computations/class_blocks_split.py`.

## Reproduce

```bash
python -m computations.class_blocks_18_split --lean ClassBlocks18SplitC1 > Rule30Open/Columns/ClassBlocks18SplitC1.lean
lake build Rule30Open.Columns.ClassBlocks18SplitC1
```
