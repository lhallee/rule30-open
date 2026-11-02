---
title: A certificate of the game with cyclic classes can be checked over several modules
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ClassSplit
headline: [ClassCert.tri_append, ClassCert.levelOk_append]
kit: new
kit_modules: [Rule30StripCertificateTable]
evidence: [computations/class_blocks_split.py]
---

# A certificate of the game with cyclic classes can be checked over several modules

The kernel check of a certificate of [ClassGame](ClassGame.md) at width $j + 1$, `ClassCert.levelOk j φ`, reads only
the block and the tables of heights of widths $j$ and $j + 1$. So the widths of a certificate too large for one module
can be checked in several, each on a certificate whose list of widths is a prefix of the full one, and carried to the
full certificate.

## Statement

- `ClassCert.tri_append`: if `d.levels = c.levels ++ t`, then `d.tri i φ = c.tri i φ` for every `i ≤ c.levels.length`
  and every phase `φ`.
- `ClassCert.levelOk_append`: if moreover `d.block = c.block`, then `d.levelOk j φ = c.levelOk j φ` for every
  `j < c.levels.length` and every phase `φ`.

## Argument

`ClassCert.tri 0 φ` is the one-entry table `ts 0 0` for every certificate, and `tri (i + 1) φ` is entry `φ` of entry
`i` of `levels`, which is the same in `c.levels` and in `c.levels ++ t` when `i < c.levels.length`. `levelOk j φ` is a
function of `tri j φ`, `tri (j + 1) φ`, `tri (j + 1) (next φ)` and `center φ`, and `next` and `center` read only the
block. Both proofs are rewriting.

## In Lean

[ClassBlocks17Split](ClassBlocks17Split.md) applies `levelOk_append` to the certificates of $00011111111110101$ and
$01111011111111111$ at 17 cells, whose widths are checked over [ClassBlocks17SplitA1](ClassBlocks17SplitA1.md) to
[ClassBlocks17SplitA3](ClassBlocks17SplitA3.md) and [ClassBlocks17SplitB1](ClassBlocks17SplitB1.md) to
[ClassBlocks17SplitB3](ClassBlocks17SplitB3.md). The module builds in a few seconds.

## Reproduce

```bash
lake build Rule30Open.Columns.ClassSplit
```
