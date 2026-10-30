---
title: The game decided phase by phase in the kernel excludes the 11 blocks of period 19 that need 13 or 14 cells
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.BitPhases19
headline: [center_not_blocksPhases19, not_eventually_blocksPhases19]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/bit_game.py, computations/game.py]
---

# The game decided phase by phase in the kernel excludes the 11 blocks of period 19 that need 13 or 14 cells

The center column of the single cell does not eventually repeat any of the 11 blocks of `blocksPhases19`, from any time
on and in any rotation (`center_not_blocksPhases19`); `not_eventually_blocksPhases19` says the same in the kit's form
`Rule30StripCertificates.EventuallyWord`. The kit excludes none of them.

## Statement

Of the primitive blocks of period 19, [the finite game](FiniteGame.md) excludes 217 ([the game blocks of period 19 and
20](../../findings/columns/game-blocks-20.md)). The kit and [WallSets](WallSets.md) exclude 83 of them, and of the
134 new ones the BitBlocks modules check the 123 that need at most 12 cells. This module checks the other 11, which need
13 or 14.

## Argument

The same as [BitPhases](BitPhases.md): for each block the kernel checks `phaseCheck` at each phase in its own
declaration, with no images and the rounds that `phase_rounds` in
[computations/bit_game.py](../../computations/bit_game.py) gives, and `center_not_phases_list` turns the passing checks
into the exclusions. The module builds in about three minutes with a peak of about 4.1 GB.

| Block | Width | Phases with rounds | Most rounds |
|---|---|---|---|
| $0000000000001111111$ | 14 | 12 | 2 |
| $0000000000101001111$ | 13 | 13 | 1 |
| $0000000000110101111$ | 14 | 12 | 2 |
| $0000000001001010111$ | 14 | 13 | 4 |
| $0000000101001111011$ | 13 | 11 | 3 |
| $0000001011011000011$ | 13 | 12 | 2 |
| $0000100111111111111$ | 13 | 6 | 2 |
| $0000101111111001001$ | 13 | 9 | 2 |
| $0001011100111111011$ | 14 | 7 | 4 |
| $0001011111111111001$ | 13 | 6 | 2 |
| $0010011011111111111$ | 13 | 5 | 2 |

## Relation to the kit

`kit_blocks` in [computations/game.py](../../computations/game.py) lists the kit's exclusions at this period; none of
the blocks here is among them.

## Lean

`Rule30Open.Columns.BitPhases19`: for each block one theorem `w<block>_<φ>` per phase and `w<block>` that gathers them;
`blocksPhases19`, `blocksPhases19_phases`, `blocksPhases19_pos`, `center_not_blocksPhases19` and
`not_eventually_blocksPhases19`. The checks come from `python -m computations.bit_game --phases 19`.
