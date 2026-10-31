---
title: Traps for 83 of the 335 blocks of period 12, from walls of period twelve carried leftward
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.TwelveTraps
headline: [twelveTraps_check, twelveTraps_blocks, twelve_absorption_excludes]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/lock_chain.py]
---

# Traps for 83 of the 335 blocks of period 12, from walls of period twelve carried leftward

[The natural scan](../../findings/columns/natural-traps.md) finds that the commonest traps at period 12, of 119, 116 and
150 states, are walls of 16 cells: the closures of the true windows of right halves driven by $001011100111$,
$000110110011$ and $000010011111$ at step 12,000, under both values of the cell beyond. Their chains become periodic in
the distance, with spatial periods 60, 138 and 138 from distances 41, 0 and 7, as the wall of period 10 does in
[TenTraps](TenTraps.md). This module carries the walls leftward up to 40 columns and checks the traps of the 83 blocks
of period 12 that they reach there and that the kit does not exclude.

## Statement

1. **The traps** (`twelveTraps`, `twelveTraps_check`). A list of 83 labelled traps `WTrap`, all passing the check of
   [WordTraps](WordTraps.md): for each block, the wall that reaches it first carried to the least distance $d \le 40$
   that holds it, a trap of $16 + d$ cells with the wall's number of states and labels modulo 12.
2. **The blocks** (`twelveTraps_blocks`): 83 distinct blocks of period 12, 37, 36 and 10 by the three walls.
3. **The reduction** (`twelve_absorption_excludes`). For each of them, if every finitely supported right half driven by
   the block enters its trap (`WTrap.Absorption`), the center column does not eventually repeat the block.

## Argument

As in [TenTraps](TenTraps.md) and [NineTraps](NineTraps.md): each wall is a closed set of windows on which column 1 is
fixed at the white phases; if column $m$ repeats the block and column $m + 1$ reads the wall's values at its white
phases, each column to the left is a function of the two to its right, and putting the $d$ columns between
$m - d + 1$ and $m$ in front of every state gives a trap of $16 + d$ cells for the block of column $m - d$ (`carried`
in [computations/lock_chain.py](../../computations/lock_chain.py)). The kernel checks every trap, so the carrying is not
trusted, and [WordTraps](WordTraps.md)'s `absorption_excludes` gives each reduction.

## What it covers

Each trap reduces its block to entry. Two of the walls are entered fast: every right half with support in cells 1 to 8
enters the wall of $001011100111$ from every phase within 2,341 steps, and the white half within 836, which
[WallGaps](WallGaps.md) carries along the light cone, and that of $000110110011$ within 2,810 steps; the third, of
$000010011111$, is entered by 1 of the 192 pairs of a half of at most four cells and a phase. Of the 83 traps, small
halves enter 11 from every one of those pairs within 20,000 steps, 36 from some, and 36 from none (`walls_entry`). Entry
for every finite right half stays open, as for the kit's traps.

**The test of reach.** In the game of 20 cells, 26 of the 83 traps here, of 16 to 56 cells, fail the test of
[MissedTraps](MissedTraps.md): some node cannot reach a window whose first cells form a state of the trap, cut to 20
cells when the trap is wider, so a right half whose first 20 cells start there never enters, and entry into the trap is
false ([what failed](../../negative-results/columns/missed-traps.md)). [RefutedTraps](RefutedTraps.md) checks the
refutation of 13 of them in Lean. For 12 of their blocks no trap of any module passes, so the reduction is empty; the
other 14 are reduced instead by natural traps of [NaturalTrapsWalls](NaturalTrapsWalls.md) that pass, two of them to
entry into one of two. The other 57 traps pass the test, which entry needs but does not imply.

## Relation to the kit

The kit's traps are `t001` for $001$ and its ether-and-wall family for the words of period four; it has none for a
block of period 12, and none of these blocks is among those it excludes.

## Lean

`Rule30Open.Columns.TwelveTraps`: the traps `tw<wall>_<distance>`, `twelveTraps`, `twelveTraps_check`,
`twelveTraps_blocks` and `twelve_absorption_excludes`. The tables come from
`python -m computations.lock_chain --lean-walls 12`.
