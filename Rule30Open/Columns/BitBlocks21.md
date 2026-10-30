---
title: The game decided in the kernel and the window-set check exclude 220 more blocks of period 21
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.BitBlocks21
headline: [center_not_blocks21, not_eventually_blocks21, center_not_wallBlocks21]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/game.py, computations/bit_game.py]
---

# The game decided in the kernel and the window-set check exclude 220 more blocks of period 21

The center column of the single cell does not eventually repeat any of the 109 blocks of `blocks21`, from any time on
and in any rotation (`center_not_blocks21`); `not_eventually_blocks21` says the same in the kit's form
`Rule30StripCertificates.EventuallyWord`. The center column also does not repeat any of the 111 blocks of `wallBlocks21`
(`center_not_wallBlocks21`), for which the kernel evaluates the check of [WallSets](WallSets.md). The kit excludes none
of the 220.

## Statement

Of the 99,858 primitive blocks of period 21, [the finite game](FiniteGame.md) excludes 434 ([the game blocks of period
21](../../findings/columns/game-blocks-21.md)). The kit excludes 20 of them, WallSets 111 more, and 303 are new. Of the
new ones, 268 need a width of at most 12 and 35 need 13 or 14 cells, which [BitPhases21](BitPhases21.md) checks one
phase at a time. This module checks the 109 that need 5 or 6 cells: 1 at width 5 and 108 at 6;
[BitBlocks21Mid](BitBlocks21Mid.md) and [BitBlocks21Wide](BitBlocks21Wide.md) hold the others of width at most 12.

## Argument

The same as [BitGame](BitGame.md): for each block the kernel runs `gameCheck`, the game's criterion on bit tables, from
the block alone, and `center_not_bitGame` turns a passing check into the exclusion. The parameters, the width, the
number of images `D` after which the set reached stops changing (at most 56), the rounds of refinement (25 blocks need
at least one) and the search fuel, come from `criterion` in [computations/bit_game.py](../../computations/bit_game.py).
The module builds in about 120 seconds with a peak near 1.1 GB.

## Relation to the kit

`kit_blocks` in [computations/game.py](../../computations/game.py) lists the kit's exclusions at this period: its blocks
whose runs of 1s all last at least nine steps, its padded words, and its white-padding and black-run families that reach
period 21. The game excludes all of them, and none of the blocks here is among them.

## Lean

`Rule30Open.Columns.BitBlocks21`: `blocks21`, one kernel check `check_<block>` per block, `blocks21_check`,
`center_not_blocks21` and `not_eventually_blocks21`, and `wallBlocks21`, `wallBlocks21_all` and
`center_not_wallBlocks21`.
