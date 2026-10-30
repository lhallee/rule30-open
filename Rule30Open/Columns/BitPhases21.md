---
title: The game decided phase by phase in the kernel excludes the 35 blocks of period 21 that need 13 or 14 cells
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.BitPhases21
headline: [center_not_blocksPhases21, not_eventually_blocksPhases21]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/bit_game.py, computations/game.py]
---

# The game decided phase by phase in the kernel excludes the 35 blocks of period 21 that need 13 or 14 cells

The center column of the single cell does not eventually repeat any of the 35 blocks of `blocksPhases21`, from any time
on and in any rotation (`center_not_blocksPhases21`); `not_eventually_blocksPhases21` says the same in the kit's form
`Rule30StripCertificates.EventuallyWord`. The kit excludes none of them.

## Statement

Of the primitive blocks of period 21, [the finite game](FiniteGame.md) excludes 434 ([the game blocks of period
21](../../findings/columns/game-blocks-21.md)). The kit and [WallSets](WallSets.md) exclude 131 of them, and of the 303
new ones the BitBlocks modules check the 268 that need at most 12 cells. This module checks the other 35: 15 need 13
cells and 20 need 14.

## Argument

The same as [BitPhases](BitPhases.md): for each block the kernel checks `phaseCheck` at each phase in its own
declaration, with no images and the rounds that `phase_rounds` in
[computations/bit_game.py](../../computations/bit_game.py) gives, and `center_not_phases_list` turns the passing checks
into the exclusions. The module builds in about 11 minutes with a peak of about 3.2 GB.

| Block | Width | Phases with rounds | Most rounds |
|---|---|---|---|
| $000000000000001000001$ | 13 | 19 | 2 |
| $000000000000001010001$ | 14 | 18 | 2 |
| $000000000000001111111$ | 14 | 14 | 3 |
| $000000000000010010001$ | 14 | 18 | 2 |
| $000000000000011000101$ | 13 | 17 | 3 |
| $000000000000100001111$ | 13 | 16 | 2 |
| $000000000000100100111$ | 14 | 16 | 2 |
| $000000000000101000001$ | 13 | 18 | 3 |
| $000000000000110010111$ | 13 | 15 | 3 |
| $000000000000110100111$ | 13 | 15 | 3 |
| $000000000001100100011$ | 14 | 16 | 3 |
| $000000000001101100111$ | 14 | 14 | 2 |
| $000000000011001001011$ | 14 | 15 | 3 |
| $000000000100101111011$ | 14 | 13 | 2 |
| $000000000111100111111$ | 14 | 11 | 1 |
| $000000000111110000001$ | 13 | 15 | 4 |
| $000000001001011111011$ | 13 | 12 | 2 |
| $000000001011100111011$ | 14 | 12 | 2 |
| $000000001101100111011$ | 14 | 12 | 2 |
| $000000010111111100111$ | 14 | 10 | 3 |
| $000000101110011111011$ | 14 | 10 | 2 |
| $000001101111111111001$ | 14 | 8 | 3 |
| $000011111100111111111$ | 14 | 6 | 1 |
| $000011111110011111111$ | 14 | 6 | 2 |
| $000101111111110110011$ | 13 | 7 | 2 |
| $000101111111111011001$ | 13 | 7 | 4 |
| $000111110101111111111$ | 13 | 5 | 2 |
| $000111111001111111111$ | 13 | 5 | 2 |
| $000111111111100111111$ | 14 | 5 | 3 |
| $000111111111110110011$ | 13 | 6 | 1 |
| $001011111111111110111$ | 13 | 4 | 2 |
| $001101001111111111011$ | 13 | 6 | 3 |
| $001111010011111111111$ | 14 | 5 | 2 |
| $001111111111101111111$ | 14 | 3 | 2 |
| $010111110111111111111$ | 14 | 3 | 2 |

## Relation to the kit

`kit_blocks` in [computations/game.py](../../computations/game.py) lists the kit's exclusions at this period; none of
the blocks here is among them.

## Lean

`Rule30Open.Columns.BitPhases21`: for each block one theorem `w<block>_<φ>` per phase and `w<block>` that gathers them;
`blocksPhases21`, `blocksPhases21_phases`, `blocksPhases21_pos`, `center_not_blocksPhases21` and
`not_eventually_blocksPhases21`. The checks come from `python -m computations.bit_game --phases 21`.
