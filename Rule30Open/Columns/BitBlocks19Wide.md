---
title: The game decided in the kernel excludes 57 more blocks of period 19 that need 7 to 12 cells
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.BitBlocks19Wide
headline: [center_not_blocks19Wide, not_eventually_blocks19Wide]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/game.py, computations/bit_game.py]
---

# The game decided in the kernel excludes 57 more blocks of period 19 that need 7 to 12 cells

The center column of the single cell does not eventually repeat any of the 57 blocks of `blocks19Wide`, from any time on
and in any rotation (`center_not_blocks19Wide`); `not_eventually_blocks19Wide` says the same in the kit's form
`Rule30StripCertificates.EventuallyWord`. The kit excludes none of them.

## Statement

Of the 27,594 primitive blocks of period 19, [the finite game](FiniteGame.md) excludes 217 ([the game blocks of period
19 and 20](../../findings/columns/game-blocks-20.md)). The kit excludes 16 of them, WallSets 67 more, and 134 are new.
Of the new ones, 123 need a width of at most 12 and 11 need 13 or 14 cells, which [BitPhases19](BitPhases19.md) checks
one phase at a time. This module checks the 57 that need 7 to 12 cells: 11 at width 7, 21 at 8, 9 at 9, 7 at 10, 3 at
11, 6 at 12; [BitBlocks19](BitBlocks19.md) holds the others of width at most 12.

## Argument

The same as [BitGame](BitGame.md): for each block the kernel runs `gameCheck`, the game's criterion on bit tables, from
the block alone, and `center_not_bitGame` turns a passing check into the exclusion. The parameters, the width, the
number of images `D` after which the set reached stops changing (at most 133), the rounds of refinement (51 blocks need
at least one) and the search fuel, come from `criterion` in [computations/bit_game.py](../../computations/bit_game.py).
The module builds in about 285 seconds with a peak near 2.7 GB.

## Relation to the kit

`kit_blocks` in [computations/game.py](../../computations/game.py) lists the kit's exclusions at this period: its blocks
whose runs of 1s all last at least nine steps, its padded words, and its white-padding and black-run families that reach
period 19. The game excludes all of them, and none of the blocks here is among them.

## Lean

`Rule30Open.Columns.BitBlocks19Wide`: `blocks19Wide`, one kernel check `check_<block>` per block, `blocks19Wide_check`,
`center_not_blocks19Wide` and `not_eventually_blocks19Wide`.
