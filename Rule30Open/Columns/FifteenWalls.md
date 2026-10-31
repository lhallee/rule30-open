---
title: Traps for 86 blocks of period 15, from two walls wider than 16 cells carried leftward
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.FifteenWalls
headline: [fifteenWalls_check, fifteenWalls_blocks, fifteen_absorption_excludes]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/lock_chain.py]
---

# Traps for 86 blocks of period 15, from two walls wider than 16 cells carried leftward

The census of locked windows of 16 cells finds six backgrounds with walls at period 15, the largest of spatial period
2,145 ([backgrounds periodic in time](../../findings/columns/space-time-backgrounds.md)), and carried by their chains its
locks give traps to 569 blocks ([CensusTraps15](CensusTraps15.md)). Two walls of that background are wider than the
census sees. The sampled halves of [TrapSets](TrapSets.md) settle into them: the closures of the true windows at step
12,000 of right halves driven by $000111111011101$ and $000001101011101$, of 27 and 37 cells and 193 and 652 states,
the first for the white half and the second for a random half of 64 cells. The chain of the first is in the background
from the start; that of the second reaches it only at distance 152, and on the way passes blocks of period 15 that no
trap module reached. Carried leftward, the two walls give traps to 86 blocks of period 15 that no other trap that passes
reaches, and the kernel checks each.

## Statement

1. **The traps** (`fifteenWalls`, `fifteenWalls_check`). A list of 86 labelled traps `WTrap` with labels modulo 15: the
   wall of 27 cells carried 110 columns (`fw0_110`, 137 cells, 193 states) and the wall of 37 cells carried 2 to 120
   columns (`fw1_<distance>`, 39 to 157 cells, 652 states), each passing the check of [WordTraps](WordTraps.md) in its
   own declaration.
2. **The blocks** (`fifteenWalls_blocks`): 86 distinct blocks of period 15.
3. **The reduction** (`fifteen_absorption_excludes`). For each of them, if every finitely supported right half driven
   by the block enters its trap (`WTrap.Absorption`), the center column does not eventually repeat the block.

## Argument

Each wall is the closure, under both values of the cell beyond, of the window of one driven half at step 12,000, at
the least width whose closure fixes column 1 at the white phases (`natural_tables` in
[computations/lock_chain.py](../../computations/lock_chain.py)). Carried $d$ columns, a wall becomes the trap of the
block of the column $d$ to its left in its chain, with the chain's $d$ columns in front of each window (`carry`), as in
[ThirteenTraps](ThirteenTraps.md). The kernel checks each carried trap, so neither the closure nor the carrying is
trusted, and [WordTraps](WordTraps.md)'s `absorption_excludes` gives each reduction.

## Which traps were kept

Within 120 columns the two chains hold 118 and 116 blocks of period 15 with 15 distinct rotations. Of the 103 that no
module held, or whose every trap was refuted, the carried trap at the block's first distance passes both tests of
[MissedTraps](MissedTraps.md) for 86 ([what failed](../../negative-results/columns/missed-traps.md)): every node of the
game of 20 cells can reach it cut to 20 cells, and no half of the block's natural scan is inside a closed set apart
from it (`block_apart`). The other 17 fail the test of reach. Of the 86, 81 are blocks that no module held and 5 are
blocks whose traps were all refuted.

## What it covers

Each trap reduces its block to entry. The evidence for entry is thin: for 81 of the 86 blocks no half of the scan, the
white half and 30 random ones driven for 20,000 steps, locks column 1 at all, so entry rests on the two tests alone, as
it does for many traps carried far. For the other 5 every half that locks is inside a trap that meets this one. The 86
blocks count among those reduced to entry into a trap that passes, in [the coverage
table](../../findings/columns/coverage.md). For 3 of them the census trap of the block, which fails the test of reach,
is apart from the trap here, so entry into this trap alone is false and the block comes down to entry into one of the
two ([ApartTraps](ApartTraps.md)). Entry for every finite right half stays open.

## Relation to the kit

The kit's traps are `t001` for $001$ and its ether-and-wall family for the words of period four; it has none for a
block of period 15, and none of these blocks is among those it excludes.

## Lean

`Rule30Open.Columns.FifteenWalls`: the traps `fw<wall>_<distance>` with their checks, `fifteenWalls`,
`fifteenWalls_check`, `fifteenWalls_blocks` and `fifteen_absorption_excludes`. The tables come from
`python -m computations.lock_chain --lean-fifteen`.

## Reproduce

```bash
python -m computations.lock_chain --lean-fifteen
```

The traps, from the two walls and their chains, in a few seconds; `test_fifteen_walls` checks the walls' chains and
one carried trap.
