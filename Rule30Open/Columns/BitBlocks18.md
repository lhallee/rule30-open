---
title: The game decided in the kernel and the window-set check exclude 122 more blocks of period 18
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.BitBlocks18
headline: [center_not_blocks18, not_eventually_blocks18, center_not_wallBlocks18]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/game.py, computations/bit_game.py]
---

# The game decided in the kernel and the window-set check exclude 122 more blocks of period 18

The center column of the single cell does not eventually repeat any of the 77 blocks of `blocks18`, from any time on
and in any rotation (`center_not_blocks18`); `not_eventually_blocks18` says the same in the kit's form
`Rule30StripCertificates.EventuallyWord`. The center column also does not repeat any of the 45 blocks of
`wallBlocks18` (`center_not_wallBlocks18`), for which the kernel evaluates the check of [WallSets](WallSets.md). The kit
excludes none of the 122.

## Statement

Of the 14,532 primitive blocks of period 18, [the finite game](FiniteGame.md) excludes 142 ([the game blocks of period
17 and 18](../../findings/columns/game-blocks-18.md)). The kit excludes 14 of them, WallSets 45 more, and 83 are new.
This module checks the 77 of those that the game excludes at a width of at most 12: 2 at width 5, 44 at 6, 7 at 7, 10 at
8, 3 at 9, 8 at 10, 1 at 11 and 2 at 12. The other 6 need 13 or 14 cells and are left to the computation.

## Argument

The same as [BitGame](BitGame.md): for each block the kernel runs `gameCheck`, the game's criterion on bit tables, from
the block alone, and `center_not_bitGame` turns a passing check into the exclusion. The parameters, the width, the
number of images `D` after which the set reached stops changing (at most 89), the rounds of refinement (39 blocks
need at least one) and the search fuel, come from `criterion` in
[computations/bit_game.py](../../computations/bit_game.py). The module builds in about 213 seconds with a peak near
2 GB, most of it in the searches for the blocks with rounds; [BitBlocks17](BitBlocks17.md) holds period 17, so
the two build side by side.

## Relation to the kit

`kit_blocks` in [computations/game.py](../../computations/game.py) lists the kit's exclusions at this period: its blocks
whose runs of 1s all last at least nine steps, its padded words, and its white-padding families B, $0^r 1101$ with
$r \ge 14$, which first reaches period 18, and I, $0^r 1011$ with $r \ge 13$. The kit's other families, its Theorem B′
and its other white-padding families among them, start at period 19 or later.

## Lean

`Rule30Open.Columns.BitBlocks18`: `blocks18`, one kernel check `check_<block>` per block, `blocks18_check`,
`center_not_blocks18`, `not_eventually_blocks18`, `wallBlocks18`, `wallBlocks18_all` and `center_not_wallBlocks18`.
