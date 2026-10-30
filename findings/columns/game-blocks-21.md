---
title: The finite game excludes 434 of the 99,858 blocks of period 21
category: columns
problems: [1]
status: computed
formalization: partial
evidence: [computations/game.py, computations/bit_game.py, computations/wall_segments.py]
---

# The finite game excludes 434 of the 99,858 blocks of period 21

[The finite game](../../Rule30Open/Columns/FiniteGame.md), run on every primitive block of period 21 at widths 6, 10 and
14 in turn, excludes 434 of the 99,858 blocks as the eventual period of any column of any row with a leftmost 1. The kit
excludes 20 of them, all 20 that it excludes at this period, [WallSets](../../Rule30Open/Columns/WallSets.md) 111 more,
and 303 are new. Lean checks the 111 by WallSets' check and all 303 by the game decided in the kernel: 268 in one check
per block ([BitBlocks21](../../Rule30Open/Columns/BitBlocks21.md),
[BitBlocks21Mid](../../Rule30Open/Columns/BitBlocks21Mid.md),
[BitBlocks21Wide](../../Rule30Open/Columns/BitBlocks21Wide.md)), and the 35 that need 13 or 14 cells in one check per
phase ([BitPhases21](../../Rule30Open/Columns/BitPhases21.md)).

## Result

| Period | Blocks | Excluded | By the kit | By WallSets | New | New, in Lean |
|---:|---:|---:|---:|---:|---:|---:|
| 21 | 99,858 | 434 | 20 | 111 | 303 | 303 |

- **Widths.** Of the 434, the game excludes 239 at width 6, 126 at width 10 and 69 at width 14; of the 303 new blocks,
  109, 125 and 69. At the least width the 303 need 5 to 14 cells: 1 needs 5, 108 need 6, 44 need 7, 53 need 8, 14 need
  9, 14 need 10, 20 need 11, 14 need 12, 15 need 13 and 20 need 14.
- **The bit check.** `criterion` in [computations/bit_game.py](../../computations/bit_game.py) decides each of the 303
  at its least width, with at most 198 images, 3 rounds and closures of 123 steps.
- **Runs.** As at periods 17 to 20 ([the game blocks of period 19 and 20](game-blocks-20.md)), every excluded block has
  a run of at least six equal values. The least are $000000101110011111011$, $000000101111100111011$,
  $000000101111100111111$, $000000101111110000011$, $000000101111110110011$ and $000001011100111111011$.
- **Nine 1s.** 206 of the excluded blocks have nine 1s in a row. The kit excludes 14 of them, WallSets 111, and the game
  81 more.
- **Against the kit.** `kit_blocks` in [computations/game.py](../../computations/game.py) lists 20 blocks of period 21
  that the pinned kit excludes: 14 whose runs of 1s all last at least nine steps, 3 padded words and 3 of its padding
  and black-run families. The game excludes all 20.

## What it means

The share of blocks the game excludes keeps falling with the period: 0.79% at period 19, 0.56% at period 20 and 0.43% at
period 21. Every exclusion still rests on a run of six or more equal values. With these, the game excludes 1,400 blocks
of period at most 21, every one of them excluded in Lean, by the kit or here, and the share it reaches shrinks with each
period, as [the game blocks of period 19 and 20](game-blocks-20.md) found.

## Reproduce

```bash
python -m computations.game --min-period 21 --max-period 21 --widths 6,10,14 --workers 3
python -m computations.bit_game --phases 21
```

The first takes about 96 minutes with three processes and prints the 434 blocks with the first width that excludes
each; `kit_blocks(21)`, `wall_segments.in_set_family`, `game.least_width` and `bit_game.criterion` give the other
columns and the parameters of the Lean checks. The second prints the phase checks of
[BitPhases21](../../Rule30Open/Columns/BitPhases21.md), in about two and a half minutes.
