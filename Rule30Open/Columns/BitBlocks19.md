---
title: The game decided in the kernel and the window-set check exclude 133 more blocks of period 19
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.BitBlocks19
headline: [center_not_blocks19, not_eventually_blocks19, center_not_wallBlocks19]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/game.py, computations/bit_game.py]
---

# The game decided in the kernel and the window-set check exclude 133 more blocks of period 19

The center column of the single cell does not eventually repeat any of the 66 blocks of `blocks19`, from any time on and
in any rotation (`center_not_blocks19`); `not_eventually_blocks19` says the same in the kit's form
`Rule30StripCertificates.EventuallyWord`. The center column also does not repeat any of the 67 blocks of `wallBlocks19`
(`center_not_wallBlocks19`), for which the kernel evaluates the check of [WallSets](WallSets.md). The kit excludes none
of the 133.

## Statement

Of the 27,594 primitive blocks of period 19, [the finite game](FiniteGame.md) excludes 217 ([the game blocks of period
19 and 20](../../findings/columns/game-blocks-20.md)). The kit excludes 16 of them, WallSets 67 more, and 134 are new.
Of the new ones, 123 need a width of at most 12 and 11 need 13 or 14 cells, which [BitPhases19](BitPhases19.md) checks
one phase at a time. This module checks the 66 that need 5 or 6 cells: 1 at width 5, 65 at 6;
[BitBlocks19Wide](BitBlocks19Wide.md) holds the others of width at most 12.

## Argument

The same as [BitGame](BitGame.md): for each block the kernel runs `gameCheck`, the game's criterion on bit tables, from
the block alone, and `center_not_bitGame` turns a passing check into the exclusion. The parameters, the width, the
number of images `D` after which the set reached stops changing (at most 53), the rounds of refinement (21 blocks need
at least one) and the search fuel, come from `criterion` in [computations/bit_game.py](../../computations/bit_game.py).
The module builds in about 110 seconds with a peak near 1.0 GB.

## Relation to the kit

`kit_blocks` in [computations/game.py](../../computations/game.py) lists the kit's exclusions at this period: its blocks
whose runs of 1s all last at least nine steps, its padded words, and its white-padding and black-run families that reach
period 19. The game excludes all of them, and none of the blocks here is among them.

## Lean

`Rule30Open.Columns.BitBlocks19`: `blocks19`, one kernel check `check_<block>` per block, `blocks19_check`,
`center_not_blocks19` and `not_eventually_blocks19`, and `wallBlocks19`, `wallBlocks19_all` and `center_not_wallBlocks19`.
