---
title: The finite game, checked in bit masks, excludes 32 more blocks of period at most 14
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.GameBlocks
headline: [mask_column, center_not_gameBlocks, not_eventually_gameBlocks]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable, Rule30PaddedWords, Rule30BlackRuns, Rule30BlackRunBlocks, Rule30UniformWhitePadding]
evidence: [computations/game.py]
---

# The finite game, checked in bit masks, excludes 32 more blocks of period at most 14

The center column of the single cell does not eventually repeat any of the 32 blocks below, from any time on and in any
rotation (`center_not_gameBlocks`). More generally, no column of the orbit of a row with a leftmost 1 does
(`mask_column`). The kit excludes none of these blocks. They are 32 of the 34 blocks of period at most 14 that [the
finite game](FiniteGame.md) excludes beyond the kit; the other two need certificates too large for the build, and
[BitGame](BitGame.md) excludes them without one.
[GameBlocksLong](GameBlocksLong.md) adds 97 blocks of period 15 and 16.

## Statement

Each block is written as its least rotation.

| Period | Blocks |
|---|---|
| 8 | $00000001$ |
| 11 | $00000001011$, $00000001111$ |
| 12 | $000000001111$, $000000010111$ |
| 13 | $0000000001101$, $0000000001111$, $0000000011101$, $0000000011111$, $0000000101011$, $0000101111111$ |
| 14 | $00000000000101$, $00000000001011$, $00000000001101$, $00000000001111$, $00000000010011$, $00000000011011$, $00000000011101$, $00000000011111$, $00000000101011$, $00000000110011$, $00000001011011$, $00000001011111$, $00001011111111$, $00010111111111$, $00101011111111$, $00101111111111$, $00111111111011$, $00111111111101$, $01011111111111$, $01101111111111$, $01110111111111$ |

- `mask_column`: in the orbit of a row with a leftmost 1, no column repeats, from any time and in any rotation, a block
  whose certificate passes `GameMask.check`.
- `center_not_gameBlocks`: for each entry $(n, b)$ of `gameBlocks`, the center column is not, from any time $T$ on,
  the block spelled by the $n$ binary digits of $b$ (`wordOf n b`), read from any phase.
- `not_eventually_gameBlocks`: the same in the kit's form, `¬ Rule30StripCertificates.EventuallyWord`, which composes
  with the kit's `problem1_iff_no_word`.

## Argument

The game is the one in [FiniteGame.md](FiniteGame.md): column $k$ repeats the block, cells $k + 1$ to $k + K$ evolve
exactly, cell $k + K + 1$ is free at each step, and a certificate ranks the nodes (phase, cells) so that no move lowers
the rank, a move from a transient rank raises it, and at every other rank column $k - 1$ is a function of the phase.
Along the real row the rank then settles at a rank that is not transient, column $k - 1$ repeats with the block, and
[the adjacent-column theorem](AdjacentColumns.md) rules out two adjacent eventually periodic columns. Only the
encoding changes.

1. **Cells as a number.** The cells $k + 1, \dots, k + K$ at time $t$ are the number with cell $k + 1 + i$ at bit $i$
   (`codeFrom`). One step of the real cells is the kit's bit-mask step `Rule30StripCertificates.stripStep`, fed the
   column's cell on the left and the real cell $k + K + 1$ on the right (`codeFrom_succ`, from the kit's
   `testBit_stripStep` bit by bit).
2. **Ranks in as many bits as they need.** Each certificate stores its ranks in the fewest bits that hold the largest
   (5 to 10 bits here), in one number for each phase, so the kernel shifts numbers of at most $2^K$ ranks. The check is
   written with the `Nat` functions themselves (`GameMask.move`, `entry`, `bitOf`), which the kernel evaluates with
   big-number arithmetic in fewer steps; `move_eq` says `move` is the kit's `stripStep`.
3. **The same proof.** `mask_column` follows `game_column` step for step: the rank of the real play never falls and
   stays below $2^{\text{bits}}$, so it settles (`settles`) at a rank that is not transient; from then on column
   $k - 1$ is the certificate's value at that rank and the phase, which repeats with the block, as column $k$ does.

## The certificates

`game_mask` in [computations/game.py](../../computations/game.py) builds each certificate at the least width at which
the game excludes the block (`least_width`), and `lean_mask` prints it. The 32 certificates have widths 5 to 12 and
448 to 32,768 nodes, 112,896 nodes in all. The kernel checks them in about a tenth of a millisecond a node, and the
module builds in about 11 s.

The other two blocks the game excludes beyond the kit are $00000001001111$, at width 13 with 114,688 nodes, and
$00000000010001$, at width 14 with 229,376 nodes. Their certificates would add about 0.9 MB of hexadecimal to this file,
and checked on their own in the same form they take about 16 s and 163 s, against about 11 s for this whole module.
So they are left out of this module; [BitGame](BitGame.md) excludes both with a check that the kernel runs on the
block alone, without a certificate.

## Relation to the kit

`kit_blocks` in [computations/game.py](../../computations/game.py) lists the 43 primitive blocks of period at most 14
that the pinned kit excludes for the center column: the 30 words of its strip-certificate table
(`Rule30StripCertificateTable.not_eventually_certTable`) and three single strip certificates, the blocks whose runs of 1s
all last at least nine steps (`Rule30BlackRuns.not_eventuallyPeriodic_of_long_one_runs`, the constant blocks
included), and the padded words $0^q1$ for $q \ge 9$, $0^r11$ for $r \ge 8$ and $0^q10111$ for $q \ge 9$
(`Rule30PaddedWords`). Of the game's 76 blocks, 42 are among these and 34 are not; the kit's $0^91$ is one the game
does not exclude at any width up to 14. The kit's other families, a black run followed by a short block
(`Rule30BlackRunBlocks`) and a white run followed by a tail (`Rule30UniformWhitePadding`, `Rule30ShortTail` and their
relatives), need runs long enough that every block they exclude has period above 14. So the 32 blocks here are new.
The block $00000001 = 0^71$ extends the kit's $0^q1$ from $q \ge 9$ to $q = 7$; $q = 8$ stays open, since the game
excludes no block of period 9 at any width up to 14.

A certificate at width $K$ gives one at every larger width, since a play of the larger game, read on its first $K$
cells, is a play of the smaller one; so the survey's widths 6, 10 and 14 find every block the game excludes at a width
up to 14.

The method is independent of the kit's strip certificates, which read column 1 at the white times of the center and
apply masked Jen; the game reads column $k - 1$ at every time and applies the adjacent-column theorem, and it reaches
every column of every row with a leftmost 1.

## Lean

`Rule30Open.Columns.GameBlocks`: `codeFrom` with `codeFrom_lt`, `testBit_codeFrom` and `codeFrom_succ`; the structure
`GameMask` with `center`, `move`, `entry`, `bitOf`, `nodeOk`, `phaseOk` and `check`, and the lemmas `phaseOk_spec`,
`nodeOk_move` and `nodeOk_value`; `mask_column` and `mask_not_eventuallyWord`; the 32 certificates `mask00000001` to
`mask01110111111111`, each with its `_check` by `decide +kernel`; and `gameMasks`, `gameBlocks`, `gameMasks_blocks`,
`gameMasks_check` and `mem_gameMasks` for the list.
