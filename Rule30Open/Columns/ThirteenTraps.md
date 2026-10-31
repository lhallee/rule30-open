---
title: Traps for 53 of the 630 blocks of period 13, from a wall of period thirteen carried leftward
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ThirteenTraps
headline: [thirteenTraps_check, thirteenTraps_blocks, thirteen_absorption_excludes]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/lock_chain.py]
---

# Traps for 53 of the 630 blocks of period 13, from a wall of period thirteen carried leftward

[The natural scan](../../findings/columns/natural-traps.md) at period 13, closing windows of 16 cells, finds that the
commonest traps there, of 213, 5,088 and 13,904 states, are walls: the closures of the true windows of the white right
half driven by $0001110010011$, $0000000000001$ and $0000000000011$ at step 12,000, under both values of the cell
beyond. All three chains become periodic in the distance in the same background, of 689 cells, one of the four of
period 13 ([backgrounds periodic in time](../../findings/columns/space-time-backgrounds.md)). This module carries the
wall of 213 states leftward up to 53 columns and checks the traps of the 53 blocks of period 13 that it reaches there,
every block of period 13 among the columns of that background; the kit excludes none of them.

## Statement

1. **The traps** (`thirteenTraps`, `thirteenTraps_check`). A list of 53 labelled traps `WTrap`, each passing the check
   of [WordTraps](WordTraps.md) in its own declaration (`th0_<d>_check`): for each block, the wall carried to the
   least distance $d \le 53$ that holds it, a trap of $16 + d$ cells with 213 states and labels modulo 13.
2. **The blocks** (`thirteenTraps_blocks`): 53 distinct blocks of period 13.
3. **The reduction** (`thirteen_absorption_excludes`). For each of them, if every finitely supported right half driven
   by the block enters its trap (`WTrap.Absorption`), the center column does not eventually repeat the block.

## Argument

As in [TwelveTraps](TwelveTraps.md): the wall is a closed set of windows on which column 1 is fixed at the white phases;
if column $m$ repeats the block and column $m + 1$ reads the wall's values at its white phases, each column to the left
is a function of the two to its right, and putting the $d$ columns between $m - d + 1$ and $m$ in front of every state
gives a trap of $16 + d$ cells for the block of column $m - d$ (`carried` in
[computations/lock_chain.py](../../computations/lock_chain.py)). The kernel checks every trap, so the carrying is not
trusted, and [WordTraps](WordTraps.md)'s `absorption_excludes` gives each reduction. The chain of this wall repeats from
distance 1 with spatial period 689 and holds 53 blocks of period 13, each first by distance 53, so the traps have 16 to
69 cells.

## What it covers

Each trap reduces its block to entry. Small halves enter the wall itself: of the 208 pairs of a right half with support
in cells 1 to 4 and a phase, 171 enter it within 20,000 steps, the latest at step 3,840. The traps carried farther are
entered less: 7 by some of the pairs, at distances 1 to 12, and 45 by none (`walls_entry`), as at periods 11 and 12.
The walls of 5,088 and 13,904 states reach 37 more blocks within 40 columns, from the part of their chains before they
repeat, but their carried traps would take about 4 MB of tables, and they are left out. Entry for every finite right
half stays open, as for the kit's traps.

**The test of reach.** In the game of 20 cells, 22 of the 53 traps here, of 16 to 69 cells, fail the test of
[MissedTraps](MissedTraps.md): some node cannot reach a window whose first cells form a state of the trap, cut to 20
cells when the trap is wider, so a right half whose first 20 cells start there never enters, and entry into the trap is
false ([what failed](../../negative-results/columns/missed-traps.md)). [RefutedTraps](RefutedTraps.md) checks the
refutation of 13 of them in Lean. For 14 of their blocks no trap of any module passes, so the reduction is empty; the
other 8 are reduced instead by natural traps of [NaturalTrapsWalls](NaturalTrapsWalls.md) that pass. The other 31 traps
pass the test, which entry needs but does not imply.

## Relation to the kit

The kit's traps are `t001` for $001$ and its ether-and-wall family for the words of period four; it has none for a
block of period 13, and none of these blocks is among those it excludes. The walls of $0000000000001$ and
$0000000000011$ belong to blocks the kit excludes, as padded words.

## Lean

`Rule30Open.Columns.ThirteenTraps`: the traps `th0_<distance>` with their checks, `thirteenTraps`,
`thirteenTraps_check`, `thirteenTraps_blocks` and `thirteen_absorption_excludes`. The tables come from
`python -m computations.lock_chain --lean-walls 13`.

## Reproduce

```bash
python -m computations.lock_chain --natural 13,14 --steps 20000 --max-width 16 --workers 3
python -m computations.lock_chain --walls-entry 13 --cells 4 --steps 20000
```

The first, the natural scan with windows of 16 cells, takes about 40 minutes with three processes; the second, entry
into each trap here, about 18 minutes.
