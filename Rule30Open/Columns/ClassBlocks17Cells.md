---
title: The game with cyclic classes at 17 cells excludes 01010111111111111, which nothing else excludes
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ClassBlocks17Cells
headline: [column_not_01010111111111111, center_not_01010111111111111, not_eventually_01010111111111111]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/class_blocks_wide.py, computations/class_blocks.py, computations/class_certificate.py, computations/class_survey.py, computations/game.py]
---

# The game with cyclic classes at 17 cells excludes 01010111111111111, which nothing else excludes

No column of the orbit of a row with a leftmost 1, the center column of the single cell among them, eventually repeats
$01010111111111111$, from any time on and in any rotation. Neither the kit nor any other module of this repository
excludes it. The class test closes it at 17 cells and not at 16, and the plain game does not close it at 17 cells: at 17
cells one component of cyclic period $2P$ shows both values of the left column at one phase but one value on each of its
classes. The proof is [the game with cyclic classes](../../findings/columns/class-game.md), checked by the kernel
through the certificate of [ClassGame](ClassGame.md). The class-test survey at period 17 ([the class-test
survey](../../findings/columns/class-blocks.md)) finds eight such blocks: five at 16 cells, in
[ClassBlocks17](ClassBlocks17.md), [ClassBlocks17Mid](ClassBlocks17Mid.md) and
[ClassBlocks17Wide](ClassBlocks17Wide.md), and three at 17 cells, this one and $00011111111110101$ and
$01111011111111111$, whose certificates of 205,288 and 227,810 nodes over the widths are checked over three modules
each in [ClassBlocks17Split](ClassBlocks17Split.md).

## Statement

With `w` the word `wordOf 17 0b01010111111111111`:

- `column_not_01010111111111111`: for a row `init` with a leftmost 1 and any column $k$, there are no $T$ and shift $s$
  with `evolve init t k = w.getD ((t + s) % 17) false` for every $t \ge T$.
- `center_not_01010111111111111`: the same for `Rule30Prize.center`.
- `not_eventually_01010111111111111`: `¬ Rule30StripCertificates.EventuallyWord w`.

## Argument

The general soundness is [ClassGame](ClassGame.md)'s `class_column`: let column $k$ repeat a block $b$ of period $P$.
The game at width $w$ follows the phase and the cells $k + 1, \dots, k + w$ with cell $k + w + 1$ free, and every real
row is one play at every width. The certificate gives, width by width, heights under which every play enters a set
closed under moves and stays there, and on that set at the last width a rank, which no move lowers, and a label modulo
the cyclic period $d$ of each component that can hold a play, which a move inside it raises by one; at such a rank the
column $k - 1$, which is $b_{\varphi + 1} \oplus (b_\varphi \lor \text{cell } k + 1)$, is a function of the label. So
the play settles in one component, column $k - 1$ repeats with period $d$, and two adjacent columns would be eventually
periodic, which [the adjacent-column theorem](AdjacentColumns.md) excludes.

`computations/class_blocks_wide.py` builds the certificate with `class_certificate.certificate` at 17 cells, renumbers
its ranks with `class_blocks.compact`, and checks every condition node by node in plain Python
(`class_certificate.check`) before writing it.

| block | period | cells | nodes checked | height 0 at the last width | largest height | ranks | components that can hold a play at 17 cells: nodes (cyclic period) |
|---|---:|---:|---:|---:|---:|---:|---|
| $01010111111111111$ | 17 | 17 | 175,714 | 51,430 | 82 | 183 | 19,265 (17); 151 (34, mixed by phase); 149 (17); 98 (17); 70 (17) |

"Mixed by phase" marks a component where the left column takes both values at one phase. At 16 cells the class test
fails (`class_survey.classify`), so 17 is the least width.

## In Lean

`Rule30Open.Columns.ClassBlocks17Cells` has one section, written by `class_blocks.block_section`: the tries `cls<b>L<w>_<phase>` and
`cls<b>F_<phase>`, each phase in a definition of its own, the certificate `cls<b>`, one `decide +kernel` per width and
phase and one per phase of the classes, `cls<b>_valid`, and the three theorems, which apply `class_column`,
`center_not_class` and `class_not_eventuallyWord`. The module builds in about 21 minutes with a peak of about 4.8 GB.

## Relation to the kit and to the other game modules

The kit does not exclude this block: its strip-certificate table, its padded words $0^q 1$, $0^r 11$ and $0^q 10111$,
its long runs of 1s, its white-padding family $0^r 1011$ and its other padding and black-run families do not include it
(`game.kit_blocks`), and the kit has no cyclic-class argument. The finite game does not close it at 14 cells
(`game.bad_pairs`), so [BitBlocks17](BitBlocks17.md) and [BitPhases](BitPhases.md) do not reach it; neither
[WallSets](WallSets.md) nor [limit windows](../../findings/columns/limit-windows.md) of 14 cells reach it
(`class_survey.elsewhere`).

## Reproduce

```bash
python -m computations.class_blocks_wide                                     # every certificate, checked, about 40 s
python -m computations.class_blocks_wide --lean ClassBlocks17Cells > Rule30Open/Columns/ClassBlocks17Cells.lean
lake build Rule30Open.Columns.ClassBlocks17Cells
```
