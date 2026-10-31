---
title: Traps for 12 more blocks of period 12, from the wall of the background of 60 cells carried past 40 columns
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.FarWalls
headline: [farWalls_check, farWalls_blocks, far_absorption_excludes]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/lock_chain.py, computations/coverage.py]
---

# Traps for 12 more blocks of period 12, from the wall of the background of 60 cells carried past 40 columns

[The census of locked windows of 16 cells](../../findings/columns/space-time-backgrounds.md) at periods 10 to 14 sorts
every lock by the background its chain ends in, and lists the blocks those chains hold. At period 12 the chains of the
locks that end in the background of 60 cells hold 12 blocks that no trap module has and nothing excludes. The wall of
$001011100111$, at the edge of that background, reaches all 12 at distances 41 to 54, past the 40 columns that
[TwelveTraps](TwelveTraps.md) carries it. This module carries it to each of them.

## Statement

1. **The traps** (`farWalls`, `farWalls_check`). A list of 12 labelled traps `WTrap`, each passing the check of
   [WordTraps](WordTraps.md) in its own declaration (`far12_<d>_check`): for each block, the wall of $001011100111$
   carried to the least distance $d$ that holds it, $41 \le d \le 54$, a trap of $16 + d$ cells with 119 states and
   labels modulo 12.
2. **The blocks** (`farWalls_blocks`): 12 distinct blocks of period 12, none among the blocks of the other trap
   modules, the kit's, or those the finite game excludes at width 6, 10 or 14.
3. **The reduction** (`far_absorption_excludes`). For each of them, if every finitely supported right half driven by
   the block enters its trap (`WTrap.Absorption`), the center column does not eventually repeat the block.

## Argument

As in [TwelveTraps](TwelveTraps.md): the wall is a closed set of windows on which column 1 is fixed at the white
phases; if column $m$ repeats the block and column $m + 1$ reads the wall's values at its white phases, each column to
the left is a function of the two to its right, and putting the $d$ columns between $m - d + 1$ and $m$ in front of
every state gives a trap of $16 + d$ cells for the block of column $m - d$ (`carried` in
[computations/lock_chain.py](../../computations/lock_chain.py)). The kernel checks every trap, so the carrying is not
trusted, and [WordTraps](WordTraps.md)'s `absorption_excludes` gives each reduction. The chain of this wall repeats
with the 60 cells of its background, and the 12 blocks are those of its columns that the walls of
[TwelveTraps](TwelveTraps.md) do not reach within 40 columns.

## What it covers

Each trap reduces its block to entry, and these are the weakest reductions here: no right half with support in cells 1
to 4 enters any of the 12 traps within 20,000 steps from any phase (`far_entry`), as for the traps that
[ThirteenTraps](ThirteenTraps.md) and [FourteenTraps](FourteenTraps.md) carry farthest. Entering a trap carried $d$
columns means the $d$ columns beside the center settle into the background, which a small half does not do in that time.
With them 113 of the 335 blocks of period 12 have a trap in Lean, and 86 a trap that passes the test of reach below
([the coverage](../../findings/columns/coverage.md)).

**The test of reach.** Cut to their first 20 cells, 2 of the 12 traps here, of 57 and 58 cells, fail the test of
[MissedTraps](MissedTraps.md): some node of the finite game of 20 cells cannot reach the trap's states so cut, so a
right half whose first 20 cells start there never enters, and entry into the trap is false ([what
failed](../../negative-results/columns/missed-traps.md)). No trap of any module passes for their two blocks, so the
reduction is empty. The other 10 traps pass the test, which entry needs but does not imply.

## Relation to the kit

The kit's traps are `t001` for $001$ and its ether-and-wall family for the words of period four; it has none for a block
of period 12, and none of these blocks is among those it excludes.

## Lean

`Rule30Open.Columns.FarWalls`: the traps `far12_<distance>` with their checks, `farWalls`, `farWalls_check`,
`farWalls_blocks` and `far_absorption_excludes`. The tables come from `python -m computations.lock_chain --lean-far`;
the kernel checks the module in a few seconds.

## Reproduce

```bash
python -m computations.lock_chain --lock-backgrounds 12 --width 16 --workers 3
python -m computations.lock_chain --far-entry --cells 4 --steps 20000
```

The first, the census at period 12, takes about five minutes with three processes; the second, entry into each trap
here, a few minutes.
