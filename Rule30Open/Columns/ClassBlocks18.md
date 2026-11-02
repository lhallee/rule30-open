---
title: The game with cyclic classes excludes 001111111111011101, 001001101111111111 and 000000000100000001, of period 18, which nothing else excludes
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ClassBlocks18
headline: [column_not_001111111111011101, center_not_001111111111011101, not_eventually_001111111111011101, column_not_001001101111111111, center_not_001001101111111111, not_eventually_001001101111111111, column_not_000000000100000001, center_not_000000000100000001, not_eventually_000000000100000001]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/class_blocks_18.py, computations/class_blocks.py, computations/class_certificate.py, computations/class_survey.py, computations/class_blocks_wide.py, computations/game.py]
---

# The game with cyclic classes excludes 001111111111011101, 001001101111111111 and 000000000100000001, of period 18, which nothing else excludes

No column of the orbit of a row with a leftmost 1, the center column of the single cell among them, eventually repeats
$001111111111011101$, $001001101111111111$ or $000000000100000001$, from any time on and in any rotation. Neither the
kit nor any other module of this repository excludes them. The class-test survey of period 18 at 16 cells ([the
class-test survey](../../findings/columns/class-blocks.md)) finds fifteen blocks that the game or the class test closes
there and that nothing else excludes; these are the three with the smallest certificates, the next two are in
[ClassBlocks18Mid](ClassBlocks18Mid.md) and [ClassBlocks18Wide](ClassBlocks18Wide.md), and the other ten are in
[ClassBlocks18Split](ClassBlocks18Split.md), each certificate checked over two or three modules. The plain game does not
close the first two at any width up to 16, and closes $000000000100000001$ at 16 cells and not at 15; the class test
closes them at 8, 11 and 13 cells. The proof is [the game with cyclic classes](../../findings/columns/class-game.md),
checked by the kernel through the certificates of [ClassGame](ClassGame.md).

## Statement

For each block $b$ here, with `w` the word `wordOf 18 0b<b>`:

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
periodic, which [the adjacent-column theorem](AdjacentColumns.md) excludes. At the width of each certificate some
component of cyclic period $2P$ or $3P$ shows both values of the left column at one phase but one value on each of its
classes, so the plain game's test fails there and the class test holds.

`computations/class_blocks_18.py` builds each certificate with `class_certificate.certificate` at the least width at
which the class test closes the block, renumbers its ranks with `class_blocks.compact`, and checks every condition node
by node in plain Python (`class_certificate.check`) before writing it.

| block | period | cells | nodes checked | height 0 at the last width | largest height | ranks | components that can hold a play at that width: nodes (cyclic period) |
|---|---:|---:|---:|---:|---:|---:|---|
| $001111111111011101$ | 18 | 8 | 3,696 | 998 | 23 | 44 | 369 (18); 129 (36, mixed by phase); 64 (18); 22 (18) |
| $001001101111111111$ | 18 | 11 | 13,312 | 4,216 | 21 | 127 | 393 (18); 333 (36, mixed by phase); 149 (18); 41 (18) |
| $000000000100000001$ | 18 | 13 | 38,154 | 10,197 | 46 | 115 | 3,083 (18); 90 (54, mixed by phase); 29 (18) |

"Mixed by phase" marks a component where the left column takes both values at one phase. At one cell fewer the class
test fails for each block (`class_survey.classify`), so the widths are the least.

## In Lean

`Rule30Open.Columns.ClassBlocks18` has one section per block, written by `class_blocks.block_section`: the tries
`cls<b>L<w>_<phase>` and `cls<b>F_<phase>`, each phase in a definition of its own, the certificate `cls<b>`, one
`decide +kernel` per width and phase and one per phase of the classes, `cls<b>_valid`, and the three theorems, which
apply `class_column`, `center_not_class` and `class_not_eventuallyWord`. The module builds in about 4 minutes
with a peak of about 1.6 GB.

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
python -m computations.class_blocks_18                                  # all fifteen certificates, checked, 45 s
python -m computations.class_blocks_18 --lean ClassBlocks18 > Rule30Open/Columns/ClassBlocks18.lean
lake build Rule30Open.Columns.ClassBlocks18
```
