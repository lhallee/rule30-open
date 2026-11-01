---
title: The game with cyclic classes excludes 000000000010010011, of period 18, which nothing else excludes
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ClassBlocks18Mid
headline: [column_not_000000000010010011, center_not_000000000010010011, not_eventually_000000000010010011]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/class_blocks_18.py, computations/class_blocks.py, computations/class_certificate.py, computations/class_survey.py, computations/class_blocks_wide.py, computations/game.py]
---

# The game with cyclic classes excludes 000000000010010011, of period 18, which nothing else excludes

No column of the orbit of a row with a leftmost 1, the center column of the single cell among them, eventually repeats
$000000000010010011$, from any time on and in any rotation. Neither the kit nor any other module of this repository
excludes it. The class-test survey of period 18 at 16 cells ([the class-test
survey](../../findings/columns/class-blocks.md)) finds fifteen blocks that the game or the class test closes there and
that nothing else excludes; the class test closes this one at 15 cells, and the plain game does not close it at any
width up to 16. The other blocks of period 18 in Lean are in [ClassBlocks18](ClassBlocks18.md) and
[ClassBlocks18Wide](ClassBlocks18Wide.md). The proof is [the game with cyclic
classes](../../findings/columns/class-game.md), checked by the kernel through the certificate of
[ClassGame](ClassGame.md).

## Statement

With `w` the word `wordOf 18 0b000000000010010011`:

- `column_not_000000000010010011`: for a row `init` with a leftmost 1 and any column $k$, there are no $T$ and shift $s$
  with `evolve init t k = w.getD ((t + s) % 18) false` for every $t \ge T$.
- `center_not_000000000010010011`: the same for `Rule30Prize.center`.
- `not_eventually_000000000010010011`: `¬ Rule30StripCertificates.EventuallyWord w`.

## Argument

The general soundness is [ClassGame](ClassGame.md)'s `class_column`: let column $k$ repeat a block $b$ of period $P$.
The game at width $w$ follows the phase and the cells $k + 1, \dots, k + w$ with cell $k + w + 1$ free, and every real
row is one play at every width. The certificate gives, width by width, heights under which every play enters a set
closed under moves and stays there, and on that set at the last width a rank, which no move lowers, and a label modulo
the cyclic period $d$ of each component that can hold a play, which a move inside it raises by one; at such a rank the
column $k - 1$, which is $b_{\varphi + 1} \oplus (b_\varphi \lor \text{cell } k + 1)$, is a function of the label. So
the play settles in one component, column $k - 1$ repeats with period $d$, and two adjacent columns would be eventually
periodic, which [the adjacent-column theorem](AdjacentColumns.md) excludes. At the width of the certificate a
component of cyclic period $2P$ shows both values of the left column at one phase but one value on each of its
classes, so the plain game's test fails there and the class test holds.

`computations/class_blocks_18.py` builds the certificate with `class_certificate.certificate` at the least width at
which the class test closes the block, renumbers its ranks with `class_blocks.compact`, and checks every condition node
by node in plain Python (`class_certificate.check`) before writing it.

| block | period | cells | nodes checked | height 0 at the last width | largest height | ranks | components that can hold a play at that width: nodes (cyclic period) |
|---|---:|---:|---:|---:|---:|---:|---|
| $000000000010010011$ | 18 | 15 | 55,744 | 15,703 | 80 | 160 | 2,538 (18); 1,292 (36, mixed by phase); 88 (18); 73 (18); 42 (18) |

"Mixed by phase" marks a component where the left column takes both values at one phase. At one cell fewer the class
test fails (`class_survey.classify`), so the width is the least.

## In Lean

`Rule30Open.Columns.ClassBlocks18Mid` has one section, written by `class_blocks.block_section`: the tries
`cls<b>L<w>_<phase>` and `cls<b>F_<phase>`, each phase in a definition of its own, the certificate `cls<b>`, one
`decide +kernel` per width and phase and one per phase of the classes, `cls<b>_valid`, and the three theorems, which
apply `class_column`, `center_not_class` and `class_not_eventuallyWord`. The module builds in about 5 minutes
with a peak of about 1.8 GB.

## Relation to the kit and to the other game modules

The kit does not exclude this block: its strip-certificate table, its padded words, its long runs of 1s and its
padding and black-run families do not include it (`game.kit_blocks`), and no rotation of it appears in the
Lean sources of the pinned kit or of the kit's main branch, whose four-category grammars, white runs of at least 17 and
black runs $1^r u$ with $u$ of at most five cells do not contain it. The kit has no cyclic-class argument. The finite
game does not close it at 14 cells (`game.bad_pairs`), so [BitBlocks18](BitBlocks18.md) and
[BitPhases](BitPhases.md) do not reach it; neither [WallSets](WallSets.md) nor
[limit windows](../../findings/columns/limit-windows.md) of 14 cells reach it (`class_survey.elsewhere`).

## Reproduce

```bash
python -m computations.class_blocks_18                                  # all fifteen certificates, checked, 45 s
python -m computations.class_blocks_18 --lean ClassBlocks18Mid > Rule30Open/Columns/ClassBlocks18Mid.lean
lake build Rule30Open.Columns.ClassBlocks18Mid
```
