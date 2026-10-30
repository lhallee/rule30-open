---
title: The game decided in the kernel and the window-set check exclude 99 more blocks of period 17
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.BitBlocks17
headline: [center_not_blocks17, not_eventually_blocks17, center_not_wallBlocks17]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/game.py, computations/bit_game.py]
---

# The game decided in the kernel and the window-set check exclude 99 more blocks of period 17

The center column of the single cell does not eventually repeat any of the 64 blocks of `blocks17`, from any time on
and in any rotation (`center_not_blocks17`); `not_eventually_blocks17` says the same in the kit's form
`Rule30StripCertificates.EventuallyWord`. The center column also does not repeat any of the 35 blocks of
`wallBlocks17` (`center_not_wallBlocks17`), for which the kernel evaluates the check of [WallSets](WallSets.md). The kit
excludes none of the 99.

## Statement

Of the 7,710 primitive blocks of period 17, [the finite game](FiniteGame.md) excludes 119 ([the game blocks of period 17
and 18](../../findings/columns/game-blocks-18.md)). The kit excludes 12 of them, WallSets 35 more, and 72 are new. This
module checks the 64 of those that the game excludes at a width of at most 12: 1 at width 5, 36 at 6, 4 at 7, 12 at 8, 4
at 9, 3 at 10, 2 at 11 and 2 at 12. The other 8 need 13 or 14 cells and are left to the computation.

## Argument

The same as [BitGame](BitGame.md): for each block the kernel runs `gameCheck`, the game's criterion on bit tables, from
the block alone, and `center_not_bitGame` turns a passing check into the exclusion. The parameters, the width, the
number of images `D` after which the set reached stops changing (at most 70), the rounds of refinement (40 blocks
need at least one) and the search fuel, come from `criterion` in
[computations/bit_game.py](../../computations/bit_game.py). The module builds in about 174 seconds with a peak near
2 GB, most of it in the searches for the blocks with rounds; [BitBlocks18](BitBlocks18.md) holds period 18, so
the two build side by side.

## Relation to the kit

`kit_blocks` in [computations/game.py](../../computations/game.py) lists the kit's exclusions at this period: its blocks
whose runs of 1s all last at least nine steps, its padded words, and its white-padding family I, $0^r 1011$ with
$r \ge 13$, which first reaches period 17. The kit's other families, its Theorem B′ and its other white-padding families
among them, start at period 19 or later.

## Lean

`Rule30Open.Columns.BitBlocks17`: `blocks17`, one kernel check `check_<block>` per block, `blocks17_check`,
`center_not_blocks17`, `not_eventually_blocks17`, `wallBlocks17`, `wallBlocks17_all` and `center_not_wallBlocks17`.
