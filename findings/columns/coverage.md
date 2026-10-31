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
enters a set of windows that keeps the cell beside the column fixed at the white phases, masked Jen excludes the block),
or a reduction by steering (once the center repeats the block, a column beyond the window never reads one fixed
sequence). This table counts, for each period up to 15, the primitive blocks each way reaches, each block once, in that
order. A trap counts only if it passes two tests that entry needs ([what
failed](../../negative-results/columns/missed-traps.md)): every node of the finite game of 20 cells can reach a window
whose first cells form one of its states, cut to 20 cells when the trap is wider, and no half of the block's natural
scan is inside a closed set apart from it; 35 that pass, three not carried along a chain and 32 carried ones, fail the
first in the game of 22 cells and do not count either, though for three of the carried ones the wall beside the trap
gives the block a pair that passes ([WideWalls](../../Rule30Open/Columns/WideWalls.md)). A block so reached comes down
to entry into some trap of the block, `WTrap.AbsorptionAny` of [Traps001](../../Rule30Open/Columns/Traps001.md), which
excludes it as entry into one trap does and which no further trap of the block can refute; the trap that passes is the
evidence that entry is within reach, not the whole hypothesis. Entry into that one trap alone can be false: for 48
blocks it is apart from another trap of the block, wider than the games tested, so the block comes down to entry into
one of the two ([ApartTraps](../../Rule30Open/Columns/ApartTraps.md)), and the chains of seeds with long runs of 1s give
still wider traps apart from the trap of $01111$, the only block of period 5 reached, and from those of $0000000101$ and
$0001001101$ ([what failed](../../negative-results/columns/missed-traps.md)).

## Result

| Period | Blocks | Excluded | Reduced to entry into a trap | Reduced by steering only | Only refuted traps | Not reached |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 2 | 2 | 0 | 0 | 0 | 0 |
| 2 | 1 | 0 | 0 | 0 | 1 | 0 |
| 3 | 2 | 0 | 1 | 0 | 0 | 1 |
| 4 | 3 | 0 | 3 | 0 | 0 | 0 |
| 5 | 6 | 0 | 1 | 0 | 0 | 5 |
| 6 | 9 | 0 | 0 | 0 | 1 | 8 |
| 7 | 18 | 0 | 1 | 0 | 0 | 17 |
| 8 | 30 | 3 | 0 | 5 | 0 | 22 |
| 9 | 56 | 0 | 16 | 0 | 7 | 33 |
| 10 | 99 | 4 | 23 | 0 | 4 | 68 |
| 11 | 186 | 7 | 53 | 2 | 15 | 109 |
| 12 | 335 | 9 | 96 | 0 | 17 | 213 |
| 13 | 630 | 21 | 176 | 0 | 45 | 388 |
| 14 | 1161 | 31 | 334 | 0 | 46 | 750 |
| 15 | 2182 | 53 | 612 | 0 | 62 | 1455 |

- **Excluded**: the finite game at width 6, 10 or 14, or the kit ([the game blocks](game-blocks.md)); every such
  block up to period 20 is excluded in Lean, by the kit or here.
- **Reduced to entry into a trap**: the blocks of [WordTraps](../../Rule30Open/Columns/WordTraps.md),
  [NineTraps](../../Rule30Open/Columns/NineTraps.md), [TenTraps](../../Rule30Open/Columns/TenTraps.md),
  [ElevenTraps](../../Rule30Open/Columns/ElevenTraps.md), [TwelveTraps](../../Rule30Open/Columns/TwelveTraps.md),
  [ThirteenTraps](../../Rule30Open/Columns/ThirteenTraps.md),
  [FourteenTraps](../../Rule30Open/Columns/FourteenTraps.md), [NaturalTraps](../../Rule30Open/Columns/NaturalTraps.md),
  [NaturalTrapsLarge](../../Rule30Open/Columns/NaturalTrapsLarge.md),
  [NaturalTrapsLong](../../Rule30Open/Columns/NaturalTrapsLong.md),
  [NaturalTrapsLongLarge](../../Rule30Open/Columns/NaturalTrapsLongLarge.md),
  [FarWalls](../../Rule30Open/Columns/FarWalls.md), [CensusTraps13](../../Rule30Open/Columns/CensusTraps13.md),
  [CensusTraps14](../../Rule30Open/Columns/CensusTraps14.md),
  [CensusTraps15](../../Rule30Open/Columns/CensusTraps15.md),
  [CensusTrapsLarge](../../Rule30Open/Columns/CensusTrapsLarge.md),
  [CensusTrapsLarge15](../../Rule30Open/Columns/CensusTrapsLarge15.md),
  [FifteenWalls](../../Rule30Open/Columns/FifteenWalls.md), [TrapPairs](../../Rule30Open/Columns/TrapPairs.md), whose
  four blocks need entry into one of two traps, [NaturalTrapsWalls](../../Rule30Open/Columns/NaturalTrapsWalls.md), six
  of whose blocks need the same, [TrapSets](../../Rule30Open/Columns/TrapSets.md), whose 29 blocks need entry into one
  of several traps, [ApartTraps](../../Rule30Open/Columns/ApartTraps.md), whose 48 blocks need entry into one of two
  traps, [WideWalls](../../Rule30Open/Columns/WideWalls.md), whose three blocks need the same, and
  [PeriodFourCertificate](../../Rule30Open/Columns/PeriodFourCertificate.md), and the kit's `t001` for $001$ with the
  three other traps of [Traps001](../../Rule30Open/Columns/Traps001.md). Of these traps only those that pass both tests
  count (`lock_chain.UNREACHED`, `lock_chain.APART`), and the test of reach at 22 cells too
  (`lock_chain.UNREACHED_WIDE`), as do the kit's `t001` and its ether-and-wall family, behind PeriodFourCertificate,
  which pass the test of reach ([reach of the kit's conjectures](kit-absorption-reach.md)).
- **Reduced by steering only**: the blocks of [LockBlocks](../../Rule30Open/Columns/LockBlocks.md) and its two
  companions that no trap that passes reaches.
- **Only refuted traps**: blocks whose every trap fails one of the tests, so that entry into each is false and its
  reduction empty ([what failed](../../negative-results/columns/missed-traps.md)).

## What it means

The reach is uneven in the period. Every block of period 1, 3 and 4 but $011$ is excluded or reduced, while the trap for
$01$, of the kit's ether-and-wall family read so, fails the test; at periods 5, 6 and 7 one block each has a trap, which
small halves almost never enter ([trap entry](../../negative-results/columns/trap-entry.md)), and the one of period 6
fails the test in the game of 22 cells; the rest is not reached at all. From period 9 the walls at the edges of periodic
backgrounds, and at periods 10 to 12 also the closed sets that driven halves settle into, give traps to 23, 27, 70 and
113 blocks ([natural traps](natural-traps.md)), but for 7, 4, 17 and 17 of them every trap fails the tests, which leaves
16, 23, 53 and 96 with a trap that passes, and steering alone reaches two of those of period 11. Where the walls carried
along their backgrounds' columns fail, the natural traps of
[NaturalTrapsWalls](../../Rule30Open/Columns/NaturalTrapsWalls.md) reduce 60 blocks of periods 10 to 14 again. At
periods 13 and 14 sampling gives traps to 87 and 136 blocks that nothing excludes ([natural traps](natural-traps.md));
the census of every locked window of 16 cells, carried by its chain, raises the count of blocks with some trap to 221
and 380, and at period 15, where nothing reached a block before, to 593 ([backgrounds periodic in
time](space-time-backgrounds.md)), and two walls of its largest background wider than 16 cells raise it to 674
([FifteenWalls](../../Rule30Open/Columns/FifteenWalls.md)), but 45, 46 and 62 of these have only traps that fail the
tests, which leaves 176, 334 and 612, 27.9% to 28.8% of each period. Most traps that fail are carried ones, but two
walls themselves, a census component and two natural traps, all of 16 cells, pass in the game of their own width and
fail in that of 20, where the cells after them follow the rule; the sampled halves of ten blocks split between two traps
apart from each other, so that only entry into one of the two can hold
([TrapPairs](../../Rule30Open/Columns/TrapPairs.md),
[NaturalTrapsWalls](../../Rule30Open/Columns/NaturalTrapsWalls.md)); and for 29 blocks some halves settle into closed
sets of 21 to 42 cells apart from every single trap, so that only entry into one of several can hold
([TrapSets](../../Rule30Open/Columns/TrapSets.md)); and for 48 blocks the natural trap that passes and the carried trap
that fails are apart from each other, so that again only entry into one of the two can hold
([ApartTraps](../../Rule30Open/Columns/ApartTraps.md)), as for three blocks whose carried trap fails in the game of 22
cells and the wall beside it, a trap that every node of that game can reach
([WideWalls](../../Rule30Open/Columns/WideWalls.md)). Every reduction still needs its open step, entry for every finite
half or the steering condition for the true orbit, and outright exclusions stay rare: 25 of the 747 blocks of period at
most 12. Period 8 has no wall wider than 16 cells: its traps are the window locks of 13 cells of its eight blocks that
have one, which every sampled half enters, three of them excluded by the game and five reduced by steering ([natural
traps](natural-traps.md)).

## Reproduce

```bash
python -m computations.coverage --max-period 15
```

It takes about ten minutes: the game at widths 6, 10 and 14 for each block, and the block lists of the trap modules
from [computations/lock_chain.py](../../computations/lock_chain.py), with the traps that fail the test of reach
(`UNREACHED`, from `python -m computations.lock_chain --reach 20`, about four hours), and of the LockBlocks modules
from their Lean sources.
