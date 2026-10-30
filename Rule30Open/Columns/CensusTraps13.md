---
title: Traps for 124 more blocks of period 13, from every locked window of 16 cells carried leftward
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.CensusTraps13
headline: [censusTraps13_check, censusTraps13_blocks, census13_absorption_excludes]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/lock_chain.py, computations/coverage.py]
---

# Traps for 124 more blocks of period 13, from every locked window of 16 cells carried leftward

[The census of locked windows of 16 cells](../../findings/columns/space-time-backgrounds.md) takes every block of
period 13 and finds the bottom components of its locked windows, with the phase counted modulo 13: 89 blocks have
one. The chain of each component ends in the background of 533 cells or in that of 689, and the chains hold 243 blocks
of period 13. Of these, 135 are in no other trap module and not excluded; [ThirteenTraps](ThirteenTraps.md),
[NaturalTrapsLong](NaturalTrapsLong.md) and [TrapPairs](TrapPairs.md) reach 87 blocks of period 13 together. For 125 of
the 135 a component of at most 3,000 states carries to the block. For one of them, $0000010111001$, that component is
the block's own, which some node of the finite game cannot reach, and so are the two carried to it one and two columns;
[MissedTraps](MissedTraps.md) refutes entry into the first. For the other 124 this module checks the component of least
cost, states times cells.

## Statement

1. **The traps** (`censusTraps13`, `censusTraps13_check`). A list of 124 labelled traps `WTrap` with labels modulo 13,
   each passing the check of [WordTraps](WordTraps.md) in its own declaration (`cen<block>_check`): 117 to 718 states,
   16 to 108 cells.
2. **The blocks** (`censusTraps13_blocks`): 124 distinct blocks of period 13, none among the blocks of the other trap
   modules, the kit's, or those the finite game excludes at width 6, 10 or 14.
3. **The reduction** (`census13_absorption_excludes`). For each of them, if every finitely supported right half
   driven by the block enters its trap (`WTrap.Absorption`), the center column does not eventually repeat the block.

## Argument

A node of [the finite game](FiniteGame.md) of a block is locked when along every continuation, whatever the cell
beyond the window does, the column left of the block takes one value at each phase; a bottom component is a strongly
connected set of locked nodes that no move leaves (`bottom_components` in
[computations/lock_chain.py](../../computations/lock_chain.py)). So it is a closed set of windows on which column 1 is
fixed at the white phases of the block: a trap. In a component, columns $1, \dots, k$ may themselves be functions of
the phase; the chain then starts at column $k$, with the values the component fixes for column $k + 1$, and carries
leftward through the block, as for the walls of [ThirteenTraps](ThirteenTraps.md): each column is a function of the
two to its right, and putting the $d$ columns of the chain in front of every node gives a trap of $16 + d$ cells for
the block $d$ columns left (`component_tables`). The kernel checks every trap, so neither the census nor the carrying
is trusted, and [WordTraps](WordTraps.md)'s `absorption_excludes` gives each reduction.

The traps come from eight components, of 117 to 718 states, carried 0 to 92 columns. 93 of the blocks lie in chains that
end in the background of 689 cells, where [ThirteenTraps](ThirteenTraps.md) carries one wall, in the part before those
chains repeat; 31 lie in chains that end in the background of 533 cells, where 16 traps of
[NaturalTrapsLong](NaturalTrapsLong.md) end as well, though no module carried them leftward. The other 10 blocks are
reached only by their own components, of 3,336 to 22,746 states, which [CensusTrapsLarge](CensusTrapsLarge.md) checks in
parts.

## What it covers

Each trap reduces its block to entry. Small halves enter the traps carried a short way: of the 208 pairs of a right half
with support in cells 1 to 4 and a phase, every pair enters 9 of the traps, carried 1 to 4 columns, within 20,000 steps,
the latest at step 17,918; some pairs enter 37 more, carried up to 31 columns; and no pair enters the other 78, carried
4 to 92 columns (`census_entry`). For eight of the blocks every sampled half of the natural scan is inside a larger trap
of 16 cells, which [NaturalTrapsLongLarge](NaturalTrapsLongLarge.md) checks. Entry for every finite right half stays
open, as for the kit's traps.

## Relation to the kit

The kit's traps are `t001` for $001$ and its ether-and-wall family for the words of period four; it has none for a block
of period 13, and none of these blocks is among those it excludes.

## Lean

`Rule30Open.Columns.CensusTraps13`: the traps `cen<block>` with their checks, `censusTraps13`, `censusTraps13_check`,
`censusTraps13_blocks` and `census13_absorption_excludes`. The tables come from
`python -m computations.lock_chain --lean-census 13`; the kernel checks the module in about 11 seconds with a peak near
350 MB.

## Reproduce

```bash
python -m computations.lock_chain --lock-backgrounds 13 --width 16 --workers 3
python -m computations.lock_chain --census-entry 13 --cells 4 --steps 20000
```

The first, the census at period 13, takes about 15 minutes with three processes; the second, entry into each trap
here, about half an hour.
