---
title: The game with cyclic classes excludes two blocks of period 13 that nothing else excludes
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ClassBlocks13
headline: [column_not_0000001011011, center_not_0000001011011, not_eventually_0000001011011, column_not_0001011111011, center_not_0001011111011, not_eventually_0001011111011]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/class_blocks.py, computations/class_certificate.py, computations/class_survey.py, computations/game.py]
---

# The game with cyclic classes excludes two blocks of period 13 that nothing else excludes

No column of the orbit of a row with a leftmost 1, the center column of the single cell among them, eventually repeats
$0000001011011$ or $0001011111011$, from any time on and in any rotation. The finite game does not exclude them at any
width up to 16, and neither the kit nor any other module of this repository does. The proof is [the game with cyclic
classes](../../findings/columns/class-game.md), checked by the kernel through the certificates of
[ClassGame](ClassGame.md). They are two of the ten blocks of period 13 to 16 that [the class-test
survey](../../findings/columns/class-blocks.md) finds; the others are in [ClassBlocks](ClassBlocks.md),
[ClassBlocks14](ClassBlocks14.md), [ClassBlocks16](ClassBlocks16.md), [ClassBlocks16Wide](ClassBlocks16Wide.md).

## Statement

For each block $b$ here, with `w` the word `wordOf P 0b<b>`:

- `column_not_<b>`: for a row `init` with a leftmost 1 and any column $k$, there are no $T$ and shift $s$ with `evolve
  init t k = w.getD ((t + s) % P) false` for every $t \ge T$.
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
periodic, which [the adjacent-column theorem](AdjacentColumns.md) excludes. The plain game asks the left column to be a
function of the phase; for each block here some component of cyclic period $2P or 3P$ shows both values at one phase but
one value on each of its classes, so only the classes close it.

`computations/class_blocks.py` builds each certificate with `class_certificate.certificate` at the least width at which
the class test closes the block, renumbers its ranks $0, 1, 2, \dots$ in order (the conditions compare ranks only by
their order), and checks every condition node by node in plain Python (`class_certificate.check`) before writing it.

| block | period | cells | nodes checked | height 0 at the last width | largest height | ranks | components that can hold a play: nodes (cyclic period) |
|---|---:|---:|---:|---:|---:|---:|---|
| $0000001011011$ | 13 | 15 | 61,826 | 17,617 | 56 | 119 | 10,957 (13); 183 (39, mixed by phase); 16 (13) |
| $0001011111011$ | 13 | 15 | 102,344 | 21,932 | 100 | 165 | 7,140 (13); 1,518 (26, mixed by phase); 1,277 (13); 617 (13); 57 (13) |

"Mixed by phase" marks the components where the plain game fails: the left column takes both values at one phase. At one
cell fewer the class test fails for each block (`game.component_periods`), so the widths are the least.

## In Lean

`Rule30Open.Columns.ClassBlocks13` has one section per block: the tries `cls<b>L<w>_<phase>` and `cls<b>F_<phase>`, each
phase in a definition of its own (a list literal of sixteen large tries exceeds the elaborator's recursion depth), the
certificate `cls<b>`, one `decide +kernel` per width and phase and one per phase of the classes, `cls<b>_valid`, and the
three theorems, which apply `class_column`, `center_not_class` and `class_not_eventuallyWord`. The module builds in
about 14 minutes with a peak of about 4.0 GB.

## Relation to the kit and to the other game modules

The kit does not exclude these blocks: its strip-certificate table, its padded words $0^q 1$, $0^r 11$ and $0^q 10111$,
its long runs of 1s and its padding and black-run families do not include them (`game.kit_blocks`), and the kit has no
cyclic-class argument. The finite game does not exclude them at widths 6, 10, 14, 15 or 16 (`game.bad_pairs`), so
[GameBlocks](GameBlocks.md), [GameBlocksLong](GameBlocksLong.md) and [BitGame](BitGame.md) do not reach them; neither
[WallSets](WallSets.md) nor [limit windows](../../findings/columns/limit-windows.md) reach them
(`class_survey.elsewhere`). This repository has kernel-checked traps, conditional on the column entering them, in
[NaturalTrapsLongLarge](NaturalTrapsLongLarge.md) for $0000001011011$ and [NaturalTrapsLong](NaturalTrapsLong.md) for
$0001011111011$; the exclusion here is unconditional.

## Reproduce

```bash
python -m computations.class_blocks                                   # every certificate, checked node by node, 20 s
python -m computations.class_blocks --lean ClassBlocks13 > ClassBlocks13.lean
lake build Rule30Open.Columns.ClassBlocks13
```
