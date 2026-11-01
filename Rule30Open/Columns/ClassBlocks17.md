---
title: The game with cyclic classes excludes 00000000011111001, 00011011111111001 and 00000000010010001, of period 17, which nothing else excludes
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ClassBlocks17
headline: [column_not_00000000011111001, center_not_00000000011111001, not_eventually_00000000011111001, column_not_00011011111111001, center_not_00011011111111001, not_eventually_00011011111111001, column_not_00000000010010001, center_not_00000000010010001, not_eventually_00000000010010001]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/class_blocks_wide.py, computations/class_blocks.py, computations/class_certificate.py, computations/class_survey.py, computations/game.py]
---

# The game with cyclic classes excludes 00000000011111001, 00011011111111001 and 00000000010010001, of period 17, which nothing else excludes

No column of the orbit of a row with a leftmost 1, the center column of the single cell among them, eventually repeats
$00000000011111001$, $00011011111111001$ or $00000000010010001$, from any time on and in any rotation. Neither the kit
nor any other module of this repository excludes them. The plain game closes $00011011111111001$ at 15 cells and not at
14, so [the game blocks of period 17 and 18](../../findings/columns/game-blocks-18.md), which ran the game at widths up
to 14, miss it; the class test closes it at 13. The plain game does not close the others at any width up to 16. The
proof is [the game with cyclic classes](../../findings/columns/class-game.md), checked by the kernel through the
certificates of [ClassGame](ClassGame.md). The class-test survey at period 17 ([the class-test
survey](../../findings/columns/class-blocks.md)) finds five such blocks at 16 cells; the others are in
[ClassBlocks17Mid](ClassBlocks17Mid.md), [ClassBlocks17Wide](ClassBlocks17Wide.md). Of the three it finds at 17 cells,
[ClassBlocks17Cells](ClassBlocks17Cells.md) proves one.

## Statement

For each block $b$ here, with `w` the word `wordOf 17 0b<b>`:

- `column_not_<b>`: for a row `init` with a leftmost 1 and any column $k$, there are no $T$ and shift $s$ with `evolve
  init t k = w.getD ((t + s) % 17) false` for every $t \ge T$.
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
component of cyclic period $2P$ or $3P$ shows both values of the left column at one phase but one value on each
of its classes, so the plain game's test fails there and the class test holds.

`computations/class_blocks_wide.py` builds each certificate with `class_certificate.certificate` at the least width at
which the class test closes the block, renumbers its ranks with `class_blocks.compact`, and checks every condition node
by node in plain Python (`class_certificate.check`) before writing it.

| block | period | cells | nodes checked | height 0 at the last width | largest height | ranks | components that can hold a play at that width: nodes (cyclic period) |
|---|---:|---:|---:|---:|---:|---:|---|
| $00000000011111001$ | 17 | 12 | 16,040 | 4,820 | 33 | 90 | 1,894 (17); 100 (34, mixed by phase); 45 (34, mixed by phase); 32 (17) |
| $00011011111111001$ | 17 | 13 | 34,154 | 9,348 | 57 | 181 | 1,077 (17); 432 (17); 122 (17); 61 (51, mixed by phase); 28 (17); 25 (17) |
| $00000000010010001$ | 17 | 14 | 64,950 | 13,371 | 65 | 201 | 1,212 (17); 603 (17); 394 (17); 105 (51, mixed by phase); 39 (17); 27 (17); 18 (17) |

"Mixed by phase" marks a component where the left column takes both values at one phase. At one cell fewer the class
test fails for each block (`class_survey.classify`), so the widths are the least.

## In Lean

`Rule30Open.Columns.ClassBlocks17` has one section per block, written by `class_blocks.block_section`: the tries
`cls<b>L<w>_<phase>` and `cls<b>F_<phase>`, each phase in a definition of its own, the certificate `cls<b>`, one
`decide +kernel` per width and phase and one per phase of the classes, `cls<b>_valid`, and the three theorems, which
apply `class_column`, `center_not_class` and `class_not_eventuallyWord`. The module builds in
about 8 minutes with a peak of about 2.9 GB.

## Relation to the kit and to the other game modules

The kit does not exclude these blocks: its strip-certificate table, its padded words $0^q 1$, $0^r 11$ and $0^q 10111$,
its long runs of 1s, its white-padding family $0^r 1011$ and its other padding and black-run families do not include
them (`game.kit_blocks`), and the kit has no cyclic-class argument. The finite game does not close them at 14 cells
(`game.bad_pairs`), so [BitBlocks17](BitBlocks17.md) and [BitPhases](BitPhases.md) do not reach them; neither
[WallSets](WallSets.md) nor [limit windows](../../findings/columns/limit-windows.md) of 14 cells reach them
(`class_survey.elsewhere`).

## Reproduce

```bash
python -m computations.class_blocks_wide                                     # every certificate, checked, about 40 s
python -m computations.class_blocks_wide --lean ClassBlocks17 > Rule30Open/Columns/ClassBlocks17.lean
lake build Rule30Open.Columns.ClassBlocks17
```
