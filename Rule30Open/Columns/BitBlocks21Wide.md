---
title: The game decided in the kernel excludes 62 more blocks of period 21 that need 9 to 12 cells
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.BitBlocks21Wide
headline: [center_not_blocks21Wide, not_eventually_blocks21Wide]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/game.py, computations/bit_game.py]
---

# The game decided in the kernel excludes 62 more blocks of period 21 that need 9 to 12 cells

The center column of the single cell does not eventually repeat any of the 62 blocks of `blocks21Wide`, from any time on
and in any rotation (`center_not_blocks21Wide`); `not_eventually_blocks21Wide` says the same in the kit's form
`Rule30StripCertificates.EventuallyWord`. The kit excludes none of them.

## Statement

Of the 99,858 primitive blocks of period 21, [the finite game](FiniteGame.md) excludes 434 ([the game blocks of period
21](../../findings/columns/game-blocks-21.md)). The kit excludes 20 of them, WallSets 111 more, and 303 are new. Of the
new ones, 268 need a width of at most 12 and 35 need 13 or 14 cells, which [BitPhases21](BitPhases21.md) checks one
phase at a time. This module checks the 62 that need 9 to 12 cells: 14 at width 9, 14 at 10, 20 at 11, 14 at 12;
[BitBlocks21](BitBlocks21.md) and [BitBlocks21Mid](BitBlocks21Mid.md) hold the others of width at most 12.

## Argument

The same as [BitGame](BitGame.md): for each block the kernel runs `gameCheck`, the game's criterion on bit tables, from
the block alone, and `center_not_bitGame` turns a passing check into the exclusion. The parameters, the width, the
number of images `D` after which the set reached stops changing (at most 132), the rounds of refinement (50 blocks need
at least one) and the search fuel, come from `criterion` in [computations/bit_game.py](../../computations/bit_game.py).
The module builds in about 265 seconds with a peak near 3.9 GB.

## Relation to the kit

`kit_blocks` in [computations/game.py](../../computations/game.py) lists the kit's exclusions at this period: its blocks
whose runs of 1s all last at least nine steps, its padded words, and its white-padding and black-run families that reach
period 21. The game excludes all of them, and none of the blocks here is among them.

## Lean

`Rule30Open.Columns.BitBlocks21Wide`: `blocks21Wide`, one kernel check `check_<block>` per block, `blocks21Wide_check`,
`center_not_blocks21Wide` and `not_eventually_blocks21Wide`.
