---
title: The game with cyclic classes excludes ten more blocks of period 18, which nothing else excludes
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ClassBlocks18Split
headline: [column_not_001010100111111111, center_not_001010100111111111, not_eventually_001010100111111111, column_not_001111001111111111, center_not_001111001111111111, not_eventually_001111001111111111, column_not_011110111111111111, center_not_011110111111111111, not_eventually_011110111111111111, column_not_000000000011000101, center_not_000000000011000101, not_eventually_000000000011000101, column_not_000011111111111101, center_not_000011111111111101, not_eventually_000011111111111101, column_not_000000000011111001, center_not_000000000011111001, not_eventually_000000000011111001, column_not_000000000001000001, center_not_000000000001000001, not_eventually_000000000001000001, column_not_000010111111111001, center_not_000010111111111001, not_eventually_000010111111111001, column_not_001011111111110111, center_not_001011111111110111, not_eventually_001011111111110111, column_not_000000011011111001, center_not_000000011011111001, not_eventually_000000011011111001]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/class_blocks_18_split.py, computations/class_blocks_split.py, computations/class_blocks_18.py, computations/class_blocks.py, computations/class_certificate.py, computations/class_survey.py, computations/class_blocks_wide.py, computations/game.py]
---

# The game with cyclic classes excludes ten more blocks of period 18, which nothing else excludes

No column of the orbit of a row with a leftmost 1, the center column of the single cell among them, eventually repeats
any of the ten blocks of period 18 in the table below, from any time on and in any rotation. Neither the kit nor any
other module of this repository excludes them. The class-test survey of period 18 at 16 cells ([the class-test
survey](../../findings/columns/class-blocks.md)) finds fifteen blocks that the game or the class test closes there and
that nothing else excludes; [ClassBlocks18](ClassBlocks18.md), [ClassBlocks18Mid](ClassBlocks18Mid.md) and
[ClassBlocks18Wide](ClassBlocks18Wide.md) prove the five with the smallest certificates, and this module proves the
other ten, each certificate checked over two or three modules.

## Statement

For each block $b$ of the table, with `w` the word `wordOf 18 0b<b>`:

- `column_not_<b>`: for a row `init` with a leftmost 1 and any column $k$, there are no $T$ and shift $s$ with
  `evolve init t k = w.getD ((t + s) % 18) false` for every $t \ge T$.
- `center_not_<b>`: the same for `Rule30Prize.center`.
- `not_eventually_<b>`: `¬ Rule30StripCertificates.EventuallyWord w`.

## Argument

The general soundness is [ClassGame](ClassGame.md)'s `class_column`: let column $k$ repeat a block $b$ of period $P$.
The game at width $w$ follows the phase and the cells $k + 1, \dots, k + w$ with cell $k + w + 1$ free, and every real
row is one play at every width. The certificate gives, width by width, heights under which every play enters a set
closed under moves and stays there, and on that set at the last width a rank, which no move lowers, and a label modulo
the cyclic period $d$ of each component that can hold a play, which a move inside it raises by one; at such a rank the
column $k - 1$, which is $b_{\varphi + 1} \oplus (b_\varphi \lor \text{cell } k + 1)$, is a function of the label. So
the play settles in one component, column $k - 1$ repeats with period $d$, and two adjacent columns would be eventually
periodic, which [the adjacent-column theorem](AdjacentColumns.md) excludes.

Each certificate is at the least width at which the class test closes the block (`class_blocks_18.WIDTH`), built by
`class_certificate.certificate`, renumbered by `class_blocks.compact` and checked node by node in plain Python by
`class_certificate.check` before it is written.

| block | closed by | cells | nodes checked over the widths | height 0 at the last width | largest height | ranks | components that can hold a play at that width: nodes (cyclic period) |
|---|---|---:|---:|---:|---:|---:|---|
| $001010100111111111$ | classes only | 14 | 66,196 | 21,009 | 45 | 107 | 8,745 (18); 542 (36, mixed by phase) |
| $001111001111111111$ | the game at 15 cells | 15 | 70,070 | 19,812 | 37 | 138 | 12,331 (18); 52 (18); 26 (18) |
| $011110111111111111$ | classes only | 15 | 80,736 | 20,080 | 80 | 137 | 4,864 (18); 219 (18); 166 (54, mixed by phase) |
| $000000000011000101$ | the game at 16 cells | 15 | 80,020 | 21,670 | 55 | 208 | 8,227 (18); 57 (36, mixed by phase); 53 (18); 30 (18); 27 (18); 24 (18) |
| $000011111111111101$ | classes only | 15 | 88,328 | 25,091 | 51 | 232 | 7,701 (18); 292 (18); 214 (18); 161 (36, mixed by phase); 63 (18); 59 (18) |
| $000000000011111001$ | classes only | 16 | 105,158 | 30,320 | 53 | 197 | 13,724 (18); 1,505 (18); 119 (36, mixed by phase) |
| $000000000001000001$ | the game at 16 cells | 16 | 118,106 | 23,267 | 98 | 102 | 12,331 (18); 52 (18); 26 (18) |
| $000010111111111001$ | classes only | 16 | 119,668 | 32,054 | 85 | 102 | 14,726 (18); 470 (36, mixed by phase); 222 (36, mixed by phase) |
| $001011111111110111$ | classes only | 16 | 150,174 | 43,557 | 52 | 189 | 14,228 (18); 576 (36, mixed by phase); 145 (36); 55 (18); 53 (18) |
| $000000011011111001$ | the game at 16 cells | 16 | 152,538 | 42,159 | 68 | 173 | 6,774 (18); 105 (18); 24 (18) |

"Classes only" means the plain game does not close the block at 16 cells; "the game at 15 cells" and "at 16 cells" give
the least width at which it does. "Mixed by phase" marks a component where the left column takes both values at one
phase, which is where the plain game fails; on each cyclic class of such a component the left column has one value, so
the class test holds. The components of $001111001111111111$ at 15 cells and of $000000000001000001$ at 16 cells have
the same sizes (`class_survey.classify`).

## In Lean

The checks are split by `computations/class_blocks_18_split.py`, with the functions of
`computations/class_blocks_split.py`. The five blocks whose heights hold at most 88,328 nodes have two modules: the
first ([ClassBlocks18SplitA1](ClassBlocks18SplitA1.md), [ClassBlocks18SplitB1](ClassBlocks18SplitB1.md),
[ClassBlocks18SplitC1](ClassBlocks18SplitC1.md), [ClassBlocks18SplitD1](ClassBlocks18SplitD1.md),
[ClassBlocks18SplitE1](ClassBlocks18SplitE1.md)) holds the heights of every width and checks them on a certificate with
no classes, and the second ([ClassBlocks18SplitA2](ClassBlocks18SplitA2.md),
[ClassBlocks18SplitB2](ClassBlocks18SplitB2.md), [ClassBlocks18SplitC2](ClassBlocks18SplitC2.md),
[ClassBlocks18SplitD2](ClassBlocks18SplitD2.md), [ClassBlocks18SplitE2](ClassBlocks18SplitE2.md)) holds the classes,
defines the full certificate `cls<b>` and checks `ClassCert.finalOk` at every phase. The five blocks at 16 cells with
more nodes have three: widths 1 to 15 ([ClassBlocks18SplitF1](ClassBlocks18SplitF1.md),
[ClassBlocks18SplitG1](ClassBlocks18SplitG1.md), [ClassBlocks18SplitH1](ClassBlocks18SplitH1.md),
[ClassBlocks18SplitI1](ClassBlocks18SplitI1.md), [ClassBlocks18SplitJ1](ClassBlocks18SplitJ1.md)), width 16
([ClassBlocks18SplitF2](ClassBlocks18SplitF2.md), [ClassBlocks18SplitG2](ClassBlocks18SplitG2.md),
[ClassBlocks18SplitH2](ClassBlocks18SplitH2.md), [ClassBlocks18SplitI2](ClassBlocks18SplitI2.md),
[ClassBlocks18SplitJ2](ClassBlocks18SplitJ2.md)) and the classes ([ClassBlocks18SplitF3](ClassBlocks18SplitF3.md),
[ClassBlocks18SplitG3](ClassBlocks18SplitG3.md), [ClassBlocks18SplitH3](ClassBlocks18SplitH3.md),
[ClassBlocks18SplitI3](ClassBlocks18SplitI3.md), [ClassBlocks18SplitJ3](ClassBlocks18SplitJ3.md)). No module holds
more than 98,060 nodes of tables.

This module proves `cls<b>_levels`, every width at every phase on the full certificate, from the parts with
`ClassCert.levelOk_append` ([ClassSplit](ClassSplit.md)): the check of width $j + 1$ reads only the block and the
heights of widths $j$ and $j + 1$, which agree on a certificate and its prefix. Then `cls<b>_valid` and the three
theorems, which apply `class_column`, `center_not_class` and `class_not_eventuallyWord`. This module itself builds in
seconds; the 25 parts build in 2 to 7 minutes each, about 104 minutes in all, with peaks of 1.1 to 2.2 GB.

## Relation to the kit and to the other game modules

The kit does not exclude these blocks: its strip-certificate table, its padded words, its long runs of 1s and its
padding and black-run families do not include them (`game.kit_blocks`), and no rotation of any of them appears in the
Lean sources of the pinned kit or of the kit's main branch, whose four-category grammars, white runs of at least 17 and
black runs $1^r u$ with $u$ of at most five cells do not contain them. The kit has no cyclic-class argument. The finite
game does not close them at 14 cells (`game.bad_pairs`), so [BitBlocks18](BitBlocks18.md) and
[BitPhases](BitPhases.md) do not reach them; neither [WallSets](WallSets.md) nor
[limit windows](../../findings/columns/limit-windows.md) of 14 cells reach them (`class_survey.elsewhere`).

## Reproduce

```bash
python -m computations.class_blocks_18_split                    # every part's size, certificates checked, 45 s
python -m computations.class_blocks_18_split --lean ClassBlocks18Split > Rule30Open/Columns/ClassBlocks18Split.lean
lake build Rule30Open.Columns.ClassBlocks18Split                # the 25 parts first, about 104 minutes in all
```
