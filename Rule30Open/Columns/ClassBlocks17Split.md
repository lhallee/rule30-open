---
title: The game with cyclic classes at 17 cells excludes 00011111111110101 and 01111011111111111, which nothing else excludes
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ClassBlocks17Split
headline: [column_not_00011111111110101, center_not_00011111111110101, not_eventually_00011111111110101, column_not_01111011111111111, center_not_01111011111111111, not_eventually_01111011111111111]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/class_blocks_split.py, computations/class_blocks_wide.py, computations/class_blocks.py, computations/class_certificate.py, computations/class_survey.py, computations/game.py]
---

# The game with cyclic classes at 17 cells excludes 00011111111110101 and 01111011111111111, which nothing else excludes

No column of the orbit of a row with a leftmost 1, the center column of the single cell among them, eventually repeats
$00011111111110101$ or $01111011111111111$, from any time on and in any rotation. Neither the kit nor any other module
of this repository excludes them. The class-test survey of period 17 at 17 cells ([the class-test
survey](../../findings/columns/class-blocks.md)) finds three blocks that the class test closes at 17 cells and not at
16 and that nothing else excludes; the third, $01010111111111111$, is in [ClassBlocks17Cells](ClassBlocks17Cells.md).
The certificates of these two are too large for one Lean module, so each is checked over three.

## Statement

With `w` the word `wordOf 17 0b<b>` for each of the two blocks `b`:

- `column_not_<b>`: for a row `init` with a leftmost 1 and any column $k$, there are no $T$ and shift $s$ with
  `evolve init t k = w.getD ((t + s) % 17) false` for every $t \ge T$.
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

| block | cells | nodes checked over the widths | height 0 at 17 cells | largest height | ranks | components that can hold a play at 17 cells: nodes (cyclic period) |
|---|---:|---:|---:|---:|---:|---|
| $00011111111110101$ | 17 | 205,288 | 58,385 | 87 | 216 | 8,043 (17); 1,355 (17); 1,143 (17); 451 (17); 142 (51, mixed by phase); 124 (17); 61 (17); 52 (17); 29 (17); 17 (17) |
| $01111011111111111$ | 17 | 227,810 | 65,607 | 79 | 268 | 12,860 (17); 589 (17); 185 (17); 20 (17) |

"Mixed by phase" marks a component where the left column takes both values at one phase, which is where the plain game
fails for $00011111111110101$. For $01111011111111111$ every component has cyclic period 17, and the plain game closes
it at 17 cells as well (`game.bad_pairs` is 0); at 16 cells both tests fail for both blocks (`class_survey.classify`).

## In Lean

The checks are split by `computations/class_blocks_split.py`. For each block, the first module
([ClassBlocks17SplitA1](ClassBlocks17SplitA1.md), [ClassBlocks17SplitB1](ClassBlocks17SplitB1.md)) holds the heights of
widths 1 to 15 and checks them on a certificate with those widths only; the second
([ClassBlocks17SplitA2](ClassBlocks17SplitA2.md), [ClassBlocks17SplitB2](ClassBlocks17SplitB2.md)) holds widths 16 and
17 and checks them on a certificate with widths 1 to 17 and no classes; the third
([ClassBlocks17SplitA3](ClassBlocks17SplitA3.md), [ClassBlocks17SplitB3](ClassBlocks17SplitB3.md)) holds the classes,
defines the full certificate `cls<b>` and checks `ClassCert.finalOk` at every phase. This module proves
`cls<b>_levels`, every width at every phase on the full certificate, from the parts with `ClassCert.levelOk_append`
([ClassSplit](ClassSplit.md)): the check of width $j + 1$ reads only the block and the heights of widths $j$ and
$j + 1$, which agree on a certificate and its prefix. Then `cls<b>_valid` and the three theorems, which apply
`class_column`, `center_not_class` and `class_not_eventuallyWord`. This module itself builds in seconds; the six
parts build in 6 to 16 minutes each, with peaks of 2.1 to 4.1 GB.

## Relation to the kit and to the other game modules

The kit does not exclude these blocks: its strip-certificate table, its padded words, its long runs of 1s and its
padding and black-run families do not include them (`game.kit_blocks`), no rotation of either appears in the kit's Lean
sources, and the kit has no cyclic-class argument. The finite game does not close them at 14 cells (`game.bad_pairs`),
so [BitBlocks17](BitBlocks17.md) and [BitPhases](BitPhases.md) do not reach them; neither [WallSets](WallSets.md) nor
[limit windows](../../findings/columns/limit-windows.md) of 14 cells reach them (`class_survey.elsewhere`).

## Reproduce

```bash
python -m computations.class_blocks_split                       # every part's size, certificates checked, 20 s
python -m computations.class_blocks_split --lean ClassBlocks17Split > Rule30Open/Columns/ClassBlocks17Split.lean
lake build Rule30Open.Columns.ClassBlocks17Split                # the six parts first, about an hour in all
```
