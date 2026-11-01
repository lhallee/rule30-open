---
title: The classes of the certificate of 000011111111111101 at 15 cells, checked in Lean
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ClassBlocks18SplitE2
headline: [cls000011111111111101_f]
kit: new
kit_modules: [Rule30StripCertificateTable]
evidence: [computations/class_blocks_18_split.py, computations/class_blocks_split.py, computations/class_blocks.py, computations/class_certificate.py]
---

# The classes of the certificate of 000011111111111101 at 15 cells, checked in Lean

The certificate of [the game with cyclic classes](../../findings/columns/class-game.md) that excludes
$000011111111111101$ at 15 cells has 88,328 nodes over the widths and 25,091 for the classes. It is checked over two
modules, so that none holds more than 100,000 nodes of tables. This is part 2.
[ClassBlocks18Split](ClassBlocks18Split.md) gathers the parts and proves that no column of a row with a leftmost 1
eventually repeats $000011111111111101$.

## Statement

- `cls000011111111111101_f`: `cls000011111111111101.finalOk φ = true` for every phase `φ < 18`, where
  `cls000011111111111101` is the full certificate of [ClassGame](ClassGame.md)'s `ClassCert` for `000011111111111101` at
  15 cells.

## Argument

This module holds the 25,091 nodes of height 0 at 15 cells, each with its code rank times base plus label, and the full
certificate `cls000011111111111101`, whose tables of heights come from the module before. One `decide +kernel` per phase
checks `ClassCert.finalOk`: both moves of every node of height 0 at 15 cells keep or raise the rank, raise the label by
one modulo the rank's cyclic period when they keep a rank that is not transient, and at such a rank the column left of
the repeating one is the value the certificate gives for the rank and the label. The module builds in about 2 minutes
with a peak of about 1.4 GB.

## In Lean

`Rule30Open.Columns.ClassBlocks18SplitE2` is written by `computations/class_blocks_18_split.py`, which builds the
certificate with `class_certificate.certificate`, renumbers its ranks with `class_blocks.compact`, checks every
condition node by node in plain Python (`class_certificate.check`), and writes each phase's table in a definition of its
own with the functions of `computations/class_blocks_split.py`.

## Reproduce

```bash
python -m computations.class_blocks_18_split --lean ClassBlocks18SplitE2 > Rule30Open/Columns/ClassBlocks18SplitE2.lean
lake build Rule30Open.Columns.ClassBlocks18SplitE2
```
