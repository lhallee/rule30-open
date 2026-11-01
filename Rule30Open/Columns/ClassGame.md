---
title: The game with cyclic classes, checked width by width, excludes 000000001011 in Lean
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ClassGame
headline: [class_column, center_not_class, class_not_eventuallyWord, column_not_000000001011,
  center_not_000000001011, not_eventually_000000001011]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/class_certificate.py, computations/game.py, computations/bit_game.py]
---

# The game with cyclic classes, checked width by width, excludes 000000001011 in Lean

No column of the orbit of a row with a leftmost 1 repeats $000000001011$ ($0^8 1011$), from any time on and in any
rotation; in particular the center column of the single cell does not. The argument is [the game with cyclic
classes](../../findings/columns/class-game.md) at 16 cells. The kernel checks it with a certificate whose conditions are
local: one node and its two moves at a time, over 52,046 nodes for the widths and 14,476 for the classes.

## Statement

- `class_column`: in the orbit of a row with a leftmost 1, no column repeats, from some time on and in any rotation, a
  block that has a valid `ClassCert`.
- `center_not_class`, `class_not_eventuallyWord`: the same for the center column of the single cell, and in the kit's
  form `Rule30StripCertificates.EventuallyWord`.
- `column_not_000000001011`, `center_not_000000001011`, `not_eventually_000000001011`: the block `wordOf 12
  0b000000001011` is not repeated by any column of a row with a leftmost 1, nor by the center column, read from any
  phase, and it is not an `EventuallyWord` of the center column.

## Argument

Let column $k$ repeat a block $b$ of period $P$ from time $T$ on. For a width $w$, the node of the game at time $t$ is
the phase and the cells $k + 1, \dots, k + w$, coded as a number with cell $k + 1 + i$ at bit $i$; one step is the kit's
bit-mask step with the column value on the left and the real cell $k + w + 1$ on the right, so every real row is one
play of the game at every width (`codeFrom_succ`). Dropping cell $k + w$ maps a play at width $w$ to a play at width
$w - 1$ (`codeFrom_succ_top`).

1. **Widths in turn.** The certificate gives, for $w = 1, \dots, W$, a height for every node of width $w$ whose first
   $w - 1$ cells have height 0 at width $w - 1$ (at width 0 every node has height 0). The check (`levelOk`) reads the
   nodes of height 0 at width $w - 1$ off its table, extends each by both values of cell $k + w$, and verifies at each
   that both moves stay at height 0 from height 0 and lower a positive height. By induction on $w$: once the first
   $w - 1$ cells of the real play stay at height 0, its node at width $w$ is one the check covers, so its height stays
   at 0 once it is 0 and falls while it is positive; it reaches 0 and stays there (`descends`).
2. **Classes.** On the nodes of height 0 at width $W$ the certificate gives a rank and a label. The check (`finalOk`)
   verifies that no move lowers the rank, that a move from a transient rank raises it, that a move that keeps a rank
   that is not transient raises the label by one modulo that rank's modulus $d > 0$, and that at such a rank column
   $k - 1$, which is $b_{\varphi + 1} \oplus (b_\varphi \lor \text{cell } k + 1)$ (`left_cell`), equals a value the
   certificate stores for the rank and the label.
3. **The play settles.** The ranks of the real play never fall and are bounded, so from some time $t_1$ on the rank is
   constant (`settles`); it is not transient, since a move from a transient rank raises it. From then on the label
   runs $l, l + 1, \dots$ modulo $d$, so column $k - 1$ repeats with period $d$ from $t_1 + 1$ on, column $k$ with
   period $P$, and both with period $dP$, against [the adjacent-column theorem](AdjacentColumns.md).

The maps are binary tries (`KeyTrie`) read from the key's bit 0 at the root, so a lookup takes at most $w$ steps of
small numbers; the check never shifts a large number.

## The certificate for $000000001011$

`computations/class_certificate.py` builds it: at each width the set $Q_w$ of nodes whose first $w - 1$ cells have
height 0, the set its images settle into (height 0), and on the rest the longest walk into that set (the height); then
on the 14,476 nodes of height 0 at width 16 the strongly connected components, ranked by their layer in the
condensation with the components that can hold a play kept apart, and in each of those the distance from a root
modulo its cyclic period.

| width | nodes checked | height 0 | largest height |
|---:|---:|---:|---:|
| 1 to 4 | 24, 48, 96, 168 | 24, 48, 84, 135 | 2 |
| 5 to 8 | 270, 360, 318, 538 | 180, 159, 269, 458 | 29 |
| 9 to 12 | 916, 1,124, 1,724, 2,884 | 562, 862, 1,442, 2,388 | 34 |
| 13 to 16 | 4,776, 7,884, 13,130, 17,786 | 3,942, 6,565, 8,893, 14,476 | 65 |

The classes have ranks up to 283; the three components that can hold a play have 7,312, 532 and 22 nodes and cyclic
periods 12, 36 and 12, as `game.component_periods` and [the finding](../../findings/columns/class-game.md) give, and
the labels run modulo those periods. The 14,476 nodes are the set that the images of every node of the game at 16
cells settle into, which `bit_game.criterion` reaches after 106 images (the two sets are equal: a walk longer than the
sum of the largest heights ends at height 0, and every node of height 0 ends walks of every length).

## In Lean

The certificate is `cls000000001011`, and the kernel checks it with one `decide +kernel` per width and phase and one
per phase of the classes, 204 declarations, so that the kernel's cache holds one at a time; the module builds in about
5 minutes with a peak of about 1.8 GB. The general soundness,
`class_column`, is proved once for any block and any certificate. The node coding and the move are those of
[GameBlocks](GameBlocks.md) (`codeFrom`, `GameMask.move`), and the rank argument is that of
[FiniteGame](FiniteGame.md) (`settles`).

## Relation to the kit and to the other game modules

The kit does not exclude $000000001011$: its strip-certificate table has $0^9 1011$, of period 13, and its padded
words and families do not include this block (`game.kit_blocks`). The kit has no cyclic-class argument. The finite game
of [FiniteGame](FiniteGame.md), [GameBlocks](GameBlocks.md), [BitGame](BitGame.md) and [BitPhases](BitPhases.md) asks
the left column to be a function of the phase and does not exclude this block at any width up to 18; on the block read
three times it does, but the bit tables of `BitPhases.phaseCheck` on `wordOf 36` at 16 cells ran out of 13 GB. The
certificate here is the same argument, made local by checking the widths in turn and labelling the classes.

## Reproduce

```bash
python -m computations.class_certificate --check            # the sizes and the node-by-node check, a few seconds
python -m computations.class_certificate --lean > data.lean # the tables and checks of ClassGame.lean
lake build Rule30Open.Columns.ClassGame                    # about 5 minutes, peak about 1.8 GB
```
