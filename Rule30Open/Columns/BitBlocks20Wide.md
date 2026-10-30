---
title: The game decided in the kernel excludes 44 more blocks of period 20 that need 9 to 12 cells
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.BitBlocks20Wide
headline: [center_not_blocks20Wide, not_eventually_blocks20Wide]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/game.py, computations/bit_game.py]
---

# The game decided in the kernel excludes 44 more blocks of period 20 that need 9 to 12 cells

The center column of the single cell does not eventually repeat any of the 44 blocks of `blocks20Wide`, from any time on
and in any rotation (`center_not_blocks20Wide`); `not_eventually_blocks20Wide` says the same in the kit's form
`Rule30StripCertificates.EventuallyWord`. The kit excludes none of them.

## Statement

Of the 52,377 primitive blocks of period 20, [the finite game](FiniteGame.md) excludes 291 ([the game blocks of period
19 and 20](../../findings/columns/game-blocks-20.md)). The kit excludes 17 of them, WallSets 81 more, and 193 are new.
Of the new ones, 178 need a width of at most 12 and 15 need 13 or 14 cells, which are left to the computation. This
module checks the 44 that need 9 to 12 cells: 16 at width 9, 12 at 10, 14 at 11, 2 at 12; [BitBlocks20](BitBlocks20.md)
and [BitBlocks20Mid](BitBlocks20Mid.md) hold the others of width at most 12.

## Argument

The same as [BitGame](BitGame.md): for each block the kernel runs `gameCheck`, the game's criterion on bit tables, from
the block alone, and `center_not_bitGame` turns a passing check into the exclusion. The parameters, the width, the
number of images `D` after which the set reached stops changing (at most 133), the rounds of refinement (29 blocks need
at least one) and the search fuel, come from `criterion` in [computations/bit_game.py](../../computations/bit_game.py).
The module builds in about 195 seconds with a peak near 2.7 GB.

## Relation to the kit

`kit_blocks` in [computations/game.py](../../computations/game.py) lists the kit's exclusions at this period: its blocks
whose runs of 1s all last at least nine steps, its padded words, and its white-padding and black-run families that reach
period 20. The game excludes all of them, and none of the blocks here is among them.

## Lean

`Rule30Open.Columns.BitBlocks20Wide`: `blocks20Wide`, one kernel check `check_<block>` per block, `blocks20Wide_check`,
`center_not_blocks20Wide` and `not_eventually_blocks20Wide`.
