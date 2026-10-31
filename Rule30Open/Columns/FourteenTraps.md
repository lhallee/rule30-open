---
title: Traps for 101 of the 1,161 blocks of period 14, from a wall of period fourteen carried leftward
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.FourteenTraps
headline: [fourteenTraps_check, fourteenTraps_blocks, fourteen_absorption_excludes]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/lock_chain.py]
---

# Traps for 101 of the 1,161 blocks of period 14, from a wall of period fourteen carried leftward

[The natural scan](../../findings/columns/natural-traps.md) at period 14, closing windows of 16 cells, finds that the
commonest traps there, of 384, 225 and 5,269 states, are walls: the closures of the true windows of the white right
half driven by $00011010111101$, $00011100101011$ and $00000000000001$ at step 12,000, under both values of the cell
beyond. All three chains become periodic in the distance in the same background, of 728 cells, one of the six of
period 14 ([backgrounds periodic in time](../../findings/columns/space-time-backgrounds.md)). This module carries the
wall of 225 states leftward up to 103 columns and checks the traps of the 101 blocks of period 14 that it reaches
there, every block of period 14 among the columns of that background; the kit excludes none of them.

## Statement

1. **The traps** (`fourteenTraps`, `fourteenTraps_check`). A list of 101 labelled traps `WTrap`, each passing the check
   of [WordTraps](WordTraps.md) in its own declaration (`fo0_<d>_check`): for each block, the wall carried to the
   least distance $d \le 103$ that holds it, a trap of $16 + d$ cells with 225 states and labels modulo 14.
2. **The blocks** (`fourteenTraps_blocks`): 101 distinct blocks of period 14.
3. **The reduction** (`fourteen_absorption_excludes`). For each of them, if every finitely supported right half driven
   by the block enters its trap (`WTrap.Absorption`), the center column does not eventually repeat the block.

## Argument

As in [ThirteenTraps](ThirteenTraps.md): the wall is a closed set of windows on which column 1 is fixed at the white
phases, carried leftward column by column (`carried` in [computations/lock_chain.py](../../computations/lock_chain.py)),
and the kernel checks every trap, so the carrying is not trusted; [WordTraps](WordTraps.md)'s `absorption_excludes`
gives each reduction. The chain of this wall is periodic from distance 0 with spatial period 728 and holds 101 blocks
of period 14, each first by distance 103, so the traps have 16 to 119 cells.

## What it covers

Each trap reduces its block to entry. Small halves enter the wall and the traps carried a short way: of the 224 pairs
of a right half with support in cells 1 to 4 and a phase, 221 enter the wall itself within 20,000 steps, the latest at
step 2,425, every pair enters the traps at distances 1, 2, 3, 7 and 13, and some pairs enter 10 more, at distances 4 to
23; the other 85, carried farther, none do (`walls_entry`). Entry for every finite right half stays open, as for the
kit's traps.

**The test of reach.** In the game of 20 cells, 29 of the 101 traps here, of 32 to 109 cells, fail the test of
[MissedTraps](MissedTraps.md): some node cannot reach a window whose first cells form a state of the trap, cut to 20
cells when the trap is wider, so a right half whose first 20 cells start there never enters, and entry into the trap is
false ([what failed](../../negative-results/columns/missed-traps.md)). [RefutedTraps](RefutedTraps.md) checks the
refutation of 15 of them in Lean. For 13 of their blocks no trap of any module passes, so the reduction is empty; the
other 16 are reduced instead by natural traps of [NaturalTrapsWalls](NaturalTrapsWalls.md) that pass. The other 72 traps
pass the test, which entry needs but does not imply.

## Relation to the kit

The kit's traps are `t001` for $001$ and its ether-and-wall family for the words of period four; it has none for a
block of period 14, and none of these blocks is among those it excludes.

## Lean

`Rule30Open.Columns.FourteenTraps`: the traps `fo0_<distance>` with their checks, `fourteenTraps`,
`fourteenTraps_check`, `fourteenTraps_blocks` and `fourteen_absorption_excludes`. The tables come from
`python -m computations.lock_chain --lean-walls 14`.

## Reproduce

```bash
python -m computations.lock_chain --walls-entry 14 --cells 4 --steps 20000
```

Entry into each trap here, in about 32 minutes; the natural scan is that of [ThirteenTraps](ThirteenTraps.md).
