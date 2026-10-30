---
title: The game decided in the kernel excludes 97 more blocks of period 21 that need 7 to 8 cells
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.BitBlocks21Mid
headline: [center_not_blocks21Mid, not_eventually_blocks21Mid]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/game.py, computations/bit_game.py]
---

# The game decided in the kernel excludes 97 more blocks of period 21 that need 7 to 8 cells

The center column of the single cell does not eventually repeat any of the 97 blocks of `blocks21Mid`, from any time on
and in any rotation (`center_not_blocks21Mid`); `not_eventually_blocks21Mid` says the same in the kit's form
`Rule30StripCertificates.EventuallyWord`. The kit excludes none of them.

## Statement

Of the 99,858 primitive blocks of period 21, [the finite game](FiniteGame.md) excludes 434 ([the game blocks of period
21](../../findings/columns/game-blocks-21.md)). The kit excludes 20 of them, WallSets 111 more, and 303 are new. Of the
new ones, 268 need a width of at most 12 and 35 need 13 or 14 cells, which [BitPhases21](BitPhases21.md) checks one
phase at a time. This module checks the 97 that need 7 or 8 cells: 44 at width 7 and 53 at 8;
[BitBlocks21](BitBlocks21.md) and [BitBlocks21Wide](BitBlocks21Wide.md) hold the others of width at most 12.

## Argument

The same as [BitGame](BitGame.md): for each block the kernel runs `gameCheck`, the game's criterion on bit tables, from
the block alone, and `center_not_bitGame` turns a passing check into the exclusion. The parameters, the width, the
number of images `D` after which the set reached stops changing (at most 92), the rounds of refinement (70 blocks need
at least one) and the search fuel, come from `criterion` in [computations/bit_game.py](../../computations/bit_game.py).
The module builds in about 240 seconds with a peak near 1.5 GB.

## Relation to the kit

`kit_blocks` in [computations/game.py](../../computations/game.py) lists the kit's exclusions at this period: its blocks
whose runs of 1s all last at least nine steps, its padded words, and its white-padding and black-run families that reach
period 21. The game excludes all of them, and none of the blocks here is among them.

## Lean

`Rule30Open.Columns.BitBlocks21Mid`: `blocks21Mid`, one kernel check `check_<block>` per block, `blocks21Mid_check`,
`center_not_blocks21Mid` and `not_eventually_blocks21Mid`.
