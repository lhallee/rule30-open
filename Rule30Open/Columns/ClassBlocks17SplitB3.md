---
title: The classes of the certificate of 01111011111111111 at 17 cells, checked in Lean
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ClassBlocks17SplitB3
headline: [cls01111011111111111_f]
kit: new
kit_modules: [Rule30StripCertificateTable]
evidence: [computations/class_blocks_split.py, computations/class_blocks.py, computations/class_certificate.py]
---

# The classes of the certificate of 01111011111111111 at 17 cells, checked in Lean

The certificate of [the game with cyclic classes](../../findings/columns/class-game.md) that excludes
$01111011111111111$ at 17 cells has 227,810 nodes over the widths and 65,607 for the classes, too many for one Lean
module ([ClassBlocks17Cells](ClassBlocks17Cells.md), with 175,714 and 51,430, peaks near 4.8 GB), so it is checked over
three modules. This is part 3. [ClassBlocks17Split](ClassBlocks17Split.md) gathers the parts and proves that no column
of a row with a leftmost 1 eventually repeats $01111011111111111$.

## Statement

- `cls01111011111111111_f`: `cls01111011111111111.finalOk φ = true` for every phase `φ < 17`, where
  `cls01111011111111111` is the full certificate of [ClassGame](ClassGame.md)'s `ClassCert` for `01111011111111111` at
  17 cells.

## Argument

This module holds the 65,607 nodes of height 0 at 17 cells, each with its code rank times base plus label, and the full
certificate `cls01111011111111111`, whose tables of heights come from the two modules before. One `decide +kernel` per
phase checks `ClassCert.finalOk`: both moves of every node of height 0 at 17 cells keep or raise the rank, raise the
label by one modulo the rank's cyclic period when they keep a rank that is not transient, and at such a rank the column
left of the repeating one is the value the certificate gives for the rank and the label. The module builds in about 10
minutes with a peak of about 3.2 GB.

## In Lean

`Rule30Open.Columns.ClassBlocks17SplitB3` is written by `computations/class_blocks_split.py`, which builds the
certificate with `class_certificate.certificate`, renumbers its ranks with `class_blocks.compact`, checks every
condition node by node in plain Python (`class_certificate.check`), and writes each phase's table in a definition of its
own.

## Reproduce

```bash
python -m computations.class_blocks_split --lean ClassBlocks17SplitB3 > Rule30Open/Columns/ClassBlocks17SplitB3.lean
lake build Rule30Open.Columns.ClassBlocks17SplitB3
```
