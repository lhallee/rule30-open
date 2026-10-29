---
title: The finite game, checked in bit masks, excludes 97 more blocks of period 15 and 16
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.GameBlocksLong
headline: [center_not_gameBlocks16, not_eventually_gameBlocks16]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable, Rule30PaddedWords, Rule30BlackRuns, Rule30BlackRunBlocks, Rule30UniformWhitePadding]
evidence: [computations/game.py]
---

# The finite game, checked in bit masks, excludes 97 more blocks of period 15 and 16

The center column of the single cell does not eventually repeat any of the 97 blocks of `gameBlocks16`, from any time on
and in any rotation (`center_not_gameBlocks16`); `not_eventually_gameBlocks16` says the same in the kit's form
`Rule30StripCertificates.EventuallyWord`. They are 42 blocks of period 15 and 55 of period 16, and the kit excludes none
of them.

## Statement

Run on every primitive block of period at most 16, [the finite game](FiniteGame.md) excludes 197, and 136 of them are
beyond the kit ([the game blocks finding](../../findings/columns/game-blocks.md)). Of these, 102 have period 15 or 16,
and 97 need a game of at most 9 cells: 38 at width 5, 41 at width 6, 6 at width 7, 8 at width 8 and 4 at width 9. This
module checks those 97 in the kernel. The other five need 12 to 14 cells and are left to the computation.

All but one have a run of at least six 0s or at least seven 1s; $000010111111011$ has at most four 0s and six 1s in a
row. Most are a long black run with a short pattern, such as $000010111111111$ and $0101111111111111$, or a long white
run with one, such as $000000000011101$.

## Argument

The same as [GameBlocks](GameBlocks.md): a certificate ranks the nodes (phase, cells) of the game on the cells right
of the repeating column, so that no move lowers the rank, a move from a transient rank raises it, and at every other
rank the column on the left is a function of the phase (`GameMask.check`). Along the real row the rank settles at a
rank that is not transient, the column on the left repeats with the block, and Jen's theorem on adjacent columns
rules this out (`mask_column`, `mask_not_eventuallyWord`).

## The certificates

`game_mask` in [computations/game.py](../../computations/game.py) builds each certificate at the least width at which
the game excludes the block (`least_width`), and `lean_mask` prints it. The 97 certificates have 134,720 nodes in all,
and the module builds in about 30 seconds with a peak below 500 MB.

## Relation to the kit

`kit_blocks` in [computations/game.py](../../computations/game.py) lists the blocks of period at most 16 that the
pinned kit excludes: its strip certificates, the blocks whose runs of 1s all last at least nine steps, and three padded
families. Its other families (white padding, black-run blocks, suffix families) need periods above 16. None of the 97
is among them.

## Lean

`Rule30Open.Columns.GameBlocksLong`: the 97 certificates `mask<block>` with their kernel checks `mask<block>_check`,
`gameMasks16`, `gameBlocks16`, `gameMasks16_blocks`, `gameMasks16_check`, `mem_gameMasks16`, and the two headline
theorems. `GameMask` and `mask_column` are those of `GameBlocks`.
