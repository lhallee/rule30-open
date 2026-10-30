---
title: The finite game excludes 508 of the 79,971 blocks of period 19 and 20
category: columns
problems: [1]
status: computed
formalization: partial
evidence: [computations/game.py, computations/bit_game.py, computations/wall_segments.py]
---

# The finite game excludes 508 of the 79,971 blocks of period 19 and 20

[The finite game](../../Rule30Open/Columns/FiniteGame.md), run on every primitive block of period 19 and 20 at widths
6, 10 and 14 in turn, excludes 508 of the 79,971 blocks as the eventual period of any column of any row with a leftmost
1: 217 of the 27,594 of period 19 and 291 of the 52,377 of period 20. The kit excludes 33 of them, all 33 that it
excludes at these periods, [WallSets](../../Rule30Open/Columns/WallSets.md) 148 more, and 327 are new. Lean checks
the 148 by WallSets' check and all 327 by the game decided in the kernel: 301 in one check per block
([BitBlocks19](../../Rule30Open/Columns/BitBlocks19.md), [BitBlocks19Wide](../../Rule30Open/Columns/BitBlocks19Wide.md),
[BitBlocks20](../../Rule30Open/Columns/BitBlocks20.md), [BitBlocks20Mid](../../Rule30Open/Columns/BitBlocks20Mid.md),
[BitBlocks20Wide](../../Rule30Open/Columns/BitBlocks20Wide.md)), and the 26 that need 13 or 14 cells in one check per
phase ([BitPhases19](../../Rule30Open/Columns/BitPhases19.md), [BitPhases20](../../Rule30Open/Columns/BitPhases20.md)).

## Result

| Period | Blocks | Excluded | By the kit | By WallSets | New | New, in Lean |
|---:|---:|---:|---:|---:|---:|---:|
| 19 | 27,594 | 217 | 16 | 67 | 134 | 134 |
| 20 | 52,377 | 291 | 17 | 81 | 193 | 193 |

- **Widths.** Of the 508, the game excludes 324 at width 6, 133 at width 10 and 51 at width 14; of the 327 new blocks,
  145, 131 and 51. At the least width the 327 need 5 to 14 cells: 3 need 5, 142 need 6, 29 need 7, 58 need 8, 25 need
  9, 19 need 10, 17 need 11, 8 need 12, 12 need 13 and 14 need 14.
- **The bit check.** `criterion` in [computations/bit_game.py](../../computations/bit_game.py) decides each of the 327
  at its least width, with at most 183 images, 3 rounds and closures of 123 steps.
- **Runs.** As at periods 17 and 18 ([the game blocks of period 17 and 18](game-blocks-18.md)), every excluded block has
  a run of at least six equal values. The least are $0000001010011111011$, $0000001011011000011$,
  $0000001011110000011$, $0000001011111100011$ and $0001011100111111011$ of period 19 and $00000010100111111011$,
  $00000010111110000011$ and $00000010111110110011$ of period 20.
- **Nine 1s.** 238 of the excluded blocks have nine 1s in a row, 102 of period 19 and 136 of period 20. The kit
  excludes 21 of them, WallSets 148, and the game 69 more.
- **Against the kit.** `kit_blocks` in [computations/game.py](../../computations/game.py) lists 33 blocks of period 19
  and 20 that the pinned kit excludes: 21 whose runs of 1s all last at least nine steps, 6 padded words and 6 of its
  padding and black-run families. The game excludes all 33.

## What it means

The share of blocks the game excludes falls with the period: 2.7% at period 12 and 1.7% at period 16 ([the game
blocks](game-blocks.md)), 1.5% at period 17 and 0.98% at period 18, 0.79% at period 19 and 0.56% at period 20. Every
exclusion rests on a run of six or more equal values, while a longer block is more likely to hold such a run, so the
game excludes a shrinking part even of the blocks with long runs. Block-by-block exclusion by the game covers less of
each period as the period grows, and a proof of Problem 1 along this route needs exclusions that do not depend on long
runs.

## Reproduce

```bash
python -m computations.game --min-period 19 --max-period 20 --widths 6,10,14 --workers 4
```

It takes about 85 minutes with four processes and prints the 508 blocks with the first width that excludes each.
`kit_blocks(20)` and `wall_segments.in_set_family` give the other columns of the table.
