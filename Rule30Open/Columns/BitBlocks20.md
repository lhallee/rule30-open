---
title: The game decided in the kernel and the window-set check exclude 160 more blocks of period 20
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.BitBlocks20
headline: [center_not_blocks20, not_eventually_blocks20, center_not_wallBlocks20]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/game.py, computations/bit_game.py]
---

# The game decided in the kernel and the window-set check exclude 160 more blocks of period 20

The center column of the single cell does not eventually repeat any of the 79 blocks of `blocks20`, from any time on and
in any rotation (`center_not_blocks20`); `not_eventually_blocks20` says the same in the kit's form
`Rule30StripCertificates.EventuallyWord`. The center column also does not repeat any of the 81 blocks of `wallBlocks20`
(`center_not_wallBlocks20`), for which the kernel evaluates the check of [WallSets](WallSets.md). The kit excludes none
of the 160.

## Statement

Of the 52,377 primitive blocks of period 20, [the finite game](FiniteGame.md) excludes 291 ([the game blocks of period
19 and 20](../../findings/columns/game-blocks-20.md)). The kit excludes 17 of them, WallSets 81 more, and 193 are new.
Of the new ones, 178 need a width of at most 12 and 15 need 13 or 14 cells, which [BitPhases20](BitPhases20.md) checks
one phase at a time. This module checks the 79 that need 5 or 6 cells: 2 at width 5, 77 at 6;
[BitBlocks20Mid](BitBlocks20Mid.md) and [BitBlocks20Wide](BitBlocks20Wide.md) hold the others of width at most 12.

## Argument

The same as [BitGame](BitGame.md): for each block the kernel runs `gameCheck`, the game's criterion on bit tables, from
the block alone, and `center_not_bitGame` turns a passing check into the exclusion. The parameters, the width, the
number of images `D` after which the set reached stops changing (at most 58), the rounds of refinement (16 blocks need
at least one) and the search fuel, come from `criterion` in [computations/bit_game.py](../../computations/bit_game.py).
The module builds in about 125 seconds with a peak near 1.0 GB.

## Relation to the kit

`kit_blocks` in [computations/game.py](../../computations/game.py) lists the kit's exclusions at this period: its blocks
whose runs of 1s all last at least nine steps, its padded words, and its white-padding and black-run families that reach
period 20. The game excludes all of them, and none of the blocks here is among them.

## Lean

`Rule30Open.Columns.BitBlocks20`: `blocks20`, one kernel check `check_<block>` per block, `blocks20_check`,
`center_not_blocks20` and `not_eventually_blocks20`, and `wallBlocks20`, `wallBlocks20_all` and `center_not_wallBlocks20`.
