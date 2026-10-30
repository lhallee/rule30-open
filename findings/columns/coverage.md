---
title: Up to period 15, what the exclusions and reductions in Lean reach, period by period
category: columns
problems: [1]
status: computed
formalization: not-applicable
evidence: [computations/coverage.py, computations/game.py, computations/lock_chain.py]
---

# Up to period 15, what the exclusions and reductions in Lean reach, period by period

Problem 1 asks that no block be the eventual period of the center column. The repository and the kit reach a block in
three ways: an exclusion outright, a reduction to entry into a trap (if every finite right half driven by the block
enters a set of windows that keeps the cell beside the column fixed at the white phases, masked Jen excludes the
block), or a reduction by steering (once the center repeats the block, a column beyond the window never reads one fixed
sequence). This table counts, for each period up to 15, the primitive blocks each way reaches, each block once, in that
order.

## Result

| Period | Blocks | Excluded | Reduced to entry into a trap | Reduced by steering only | Not reached |
|---:|---:|---:|---:|---:|---:|
| 1 | 2 | 2 | 0 | 0 | 0 |
| 2 | 1 | 0 | 1 | 0 | 0 |
| 3 | 2 | 0 | 1 | 0 | 1 |
| 4 | 3 | 0 | 3 | 0 | 0 |
| 5 | 6 | 0 | 1 | 0 | 5 |
| 6 | 9 | 0 | 1 | 0 | 8 |
| 7 | 18 | 0 | 1 | 0 | 17 |
| 8 | 30 | 3 | 0 | 5 | 22 |
| 9 | 56 | 0 | 23 | 0 | 33 |
| 10 | 99 | 4 | 27 | 0 | 68 |
| 11 | 186 | 7 | 70 | 0 | 109 |
| 12 | 335 | 9 | 113 | 0 | 213 |
| 13 | 630 | 21 | 222 | 0 | 387 |
| 14 | 1161 | 31 | 380 | 0 | 750 |
| 15 | 2182 | 53 | 595 | 0 | 1534 |

- **Excluded**: the finite game at width 6, 10 or 14, or the kit ([the game blocks](game-blocks.md)); every such
  block up to period 20 is excluded in Lean, by the kit or here.
- **Reduced to entry into a trap**: the blocks of [WordTraps](../../Rule30Open/Columns/WordTraps.md),
  [NineTraps](../../Rule30Open/Columns/NineTraps.md), [TenTraps](../../Rule30Open/Columns/TenTraps.md),
  [ElevenTraps](../../Rule30Open/Columns/ElevenTraps.md), [TwelveTraps](../../Rule30Open/Columns/TwelveTraps.md),
  [ThirteenTraps](../../Rule30Open/Columns/ThirteenTraps.md),
  [FourteenTraps](../../Rule30Open/Columns/FourteenTraps.md),
  [NaturalTraps](../../Rule30Open/Columns/NaturalTraps.md),
  [NaturalTrapsLarge](../../Rule30Open/Columns/NaturalTrapsLarge.md),
  [NaturalTrapsLong](../../Rule30Open/Columns/NaturalTrapsLong.md),
  [NaturalTrapsLongLarge](../../Rule30Open/Columns/NaturalTrapsLongLarge.md),
  [FarWalls](../../Rule30Open/Columns/FarWalls.md),
  [CensusTraps13](../../Rule30Open/Columns/CensusTraps13.md),
  [CensusTraps14](../../Rule30Open/Columns/CensusTraps14.md),
  [CensusTraps15](../../Rule30Open/Columns/CensusTraps15.md),
  [CensusTrapsLarge](../../Rule30Open/Columns/CensusTrapsLarge.md),
  [CensusTrapsLarge15](../../Rule30Open/Columns/CensusTrapsLarge15.md) and
  [PeriodFourCertificate](../../Rule30Open/Columns/PeriodFourCertificate.md), and the kit's `t001` for $001$.
- **Reduced by steering only**: the blocks of [LockBlocks](../../Rule30Open/Columns/LockBlocks.md) and its two
  companions that no trap reaches.

## What it means

The reach is uneven in the period. Every block of period 1, 2 and 4 is excluded or reduced; at periods 5, 6 and 7 one
block each has a trap, which small halves almost never enter ([trap
entry](../../negative-results/columns/trap-entry.md)), and the rest is not reached at all. From period 9 the walls at
the edges of periodic backgrounds, and at periods 10 to 12 also the closed sets that driven halves settle into, give
traps to 23, 27, 70 and 113 blocks, a quarter to two fifths of each period ([natural traps](natural-traps.md)), and
there small halves do enter many of them. Every block of periods 11 and 12 that steering reduces has a trap too, so
steering alone reaches blocks only at period 8. At periods 13 and 14 sampling gives traps to 87 and 136 blocks that
nothing excludes, 14% and 12% of each period ([natural traps](natural-traps.md)); the census of every locked window of
16 cells, carried by its chain, raises this to 222 and 380, about a third, as at period 12 ([backgrounds periodic in
time](space-time-backgrounds.md)), though small halves enter few of the traps carried far, and at period 15, where
nothing reached a block before, to 595, more than a quarter. Every reduction still needs its open step, entry for every
finite half or the steering condition for the true orbit, and outright exclusions stay rare: 25 of the 747 blocks of
period at most 12. Period 8 has no wall wider than 16 cells: its traps are the window locks of 13 cells of its eight
blocks that have one, which every sampled half enters, three of them excluded by the game and five reduced by steering
([natural traps](natural-traps.md)).

## Reproduce

```bash
python -m computations.coverage --max-period 15
```

It takes about ten minutes: the game at widths 6, 10 and 14 for each block, and the block lists of the trap modules
from [computations/lock_chain.py](../../computations/lock_chain.py) and of the LockBlocks modules from their Lean
sources.
