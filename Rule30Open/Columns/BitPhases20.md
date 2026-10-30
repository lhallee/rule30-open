---
title: The game decided phase by phase in the kernel excludes the 15 blocks of period 20 that need 13 or 14 cells
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.BitPhases20
headline: [center_not_blocksPhases20, not_eventually_blocksPhases20]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/bit_game.py, computations/game.py]
---

# The game decided phase by phase in the kernel excludes the 15 blocks of period 20 that need 13 or 14 cells

The center column of the single cell does not eventually repeat any of the 15 blocks of `blocksPhases20`, from any time
on and in any rotation (`center_not_blocksPhases20`); `not_eventually_blocksPhases20` says the same in the kit's form
`Rule30StripCertificates.EventuallyWord`. The kit excludes none of them.

## Statement

Of the primitive blocks of period 20, [the finite game](FiniteGame.md) excludes 291 ([the game blocks of period 19 and
20](../../findings/columns/game-blocks-20.md)). The kit and [WallSets](WallSets.md) exclude 98 of them, and of the
193 new ones the BitBlocks modules check the 178 that need at most 12 cells. This module checks the other 15, which need
13 or 14.

## Argument

The same as [BitPhases](BitPhases.md): for each block the kernel checks `phaseCheck` at each phase in its own
declaration, with no images and the rounds that `phase_rounds` in
[computations/bit_game.py](../../computations/bit_game.py) gives, and `center_not_phases_list` turns the passing checks
into the exclusions. One of them, $0^{13}\,1\,0\,1\,0^3\,1$, did not fit in 13 GB as one declaration of
[BitGame](BitGame.md)'s `gameCheck`. The module builds in about five minutes with a peak of about 4.1 GB.

| Block | Width | Phases with rounds | Most rounds |
|---|---|---|---|
| $00000000000000110001$ | 14 | 17 | 3 |
| $00000000000001000001$ | 13 | 18 | 2 |
| $00000000000001010001$ | 14 | 17 | 2 |
| $00000000000011000101$ | 14 | 16 | 3 |
| $00000000001100101111$ | 14 | 13 | 2 |
| $00000000110001111011$ | 13 | 12 | 1 |
| $00000001011111100011$ | 13 | 11 | 2 |
| $00000001101111111011$ | 14 | 9 | 2 |
| $00000101111111001001$ | 14 | 10 | 3 |
| $00000101111111110111$ | 14 | 7 | 3 |
| $00001011111111001001$ | 14 | 9 | 3 |
| $00010111111111110111$ | 13 | 5 | 2 |
| $00100101110011111111$ | 13 | 7 | 3 |
| $00101001111111111101$ | 14 | 6 | 3 |
| $01111011111111111111$ | 14 | 2 | 2 |

## Relation to the kit

`kit_blocks` in [computations/game.py](../../computations/game.py) lists the kit's exclusions at this period; none of
the blocks here is among them.

## Lean

`Rule30Open.Columns.BitPhases20`: for each block one theorem `w<block>_<φ>` per phase and `w<block>` that gathers them;
`blocksPhases20`, `blocksPhases20_phases`, `blocksPhases20_pos`, `center_not_blocksPhases20` and
`not_eventually_blocksPhases20`. The checks come from `python -m computations.bit_game --phases 20`.
