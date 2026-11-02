---
title: The classes of the certificate of 000000000011111001 at 16 cells, checked in Lean
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ClassBlocks18SplitF3
headline: [cls000000000011111001_f]
kit: new
kit_modules: [Rule30StripCertificateTable]
evidence: [computations/class_blocks_18_split.py, computations/class_blocks_split.py, computations/class_blocks.py, computations/class_certificate.py]
---

# The classes of the certificate of 000000000011111001 at 16 cells, checked in Lean

The certificate of [the game with cyclic classes](../../findings/columns/class-game.md) that excludes
$000000000011111001$ at 16 cells has 105,158 nodes over the widths and 30,320 for the classes. It is checked over three
modules, so that none holds more than 100,000 nodes of tables. This is part 3.
[ClassBlocks18Split](ClassBlocks18Split.md) gathers the parts and proves that no column of a row with a leftmost 1
eventually repeats $000000000011111001$.

## Statement

- `cls000000000011111001_f`: `cls000000000011111001.finalOk φ = true` for every phase `φ < 18`, where
  `cls000000000011111001` is the full certificate of [ClassGame](ClassGame.md)'s `ClassCert` for `000000000011111001` at
  16 cells.

## Argument

This module holds the 30,320 nodes of height 0 at 16 cells, each with its code rank times base plus label, and the full
certificate `cls000000000011111001`, whose tables of heights come from the modules before. One `decide +kernel` per
phase checks `ClassCert.finalOk`: both moves of every node of height 0 at 16 cells keep or raise the rank, raise the
label by one modulo the rank's cyclic period when they keep a rank that is not transient, and at such a rank the column
left of the repeating one is the value the certificate gives for the rank and the label. The module builds in about 3
minutes with a peak of about 1.6 GB.

## In Lean

`Rule30Open.Columns.ClassBlocks18SplitF3` is written by `computations/class_blocks_18_split.py`, which builds the
certificate with `class_certificate.certificate`, renumbers its ranks with `class_blocks.compact`, checks every
condition node by node in plain Python (`class_certificate.check`), and writes each phase's table in a definition of its
own with the functions of `computations/class_blocks_split.py`.

## Reproduce

```bash
python -m computations.class_blocks_18_split --lean ClassBlocks18SplitF3 > Rule30Open/Columns/ClassBlocks18SplitF3.lean
lake build Rule30Open.Columns.ClassBlocks18SplitF3
```
