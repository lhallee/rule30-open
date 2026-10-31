---
title: Traps for 232 more blocks of period 14, from every locked window of 16 cells carried leftward
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.CensusTraps14
headline: [censusTraps14_check, censusTraps14_blocks, census14_absorption_excludes]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/lock_chain.py, computations/coverage.py]
---

# Traps for 232 more blocks of period 14, from every locked window of 16 cells carried leftward

[The census of locked windows of 16 cells](../../findings/columns/space-time-backgrounds.md), as in
[CensusTraps13](CensusTraps13.md), takes every block of period 14 and finds the bottom components of its locked
windows, with the phase counted modulo 14: 109 blocks have one. The chain of each component ends in the background of
644, 728 or 1,316 cells, and the chains hold 411 blocks of period 14. Of these, 244 are in no other trap module and not
excluded; [FourteenTraps](FourteenTraps.md) and [NaturalTrapsLong](NaturalTrapsLong.md) reach 141 blocks of period 14
together. For 232 of the 244 a component of at most 3,000 states carries to the block; this module checks, for each,
the component of least cost, states times cells.

## Statement

1. **The traps** (`censusTraps14`, `censusTraps14_check`). A list of 232 labelled traps `WTrap` with labels modulo 14,
   each passing the check of [WordTraps](WordTraps.md) in its own declaration (`cen<block>_check`): 126 to 174 states,
   17 to 104 cells.
2. **The blocks** (`censusTraps14_blocks`): 232 distinct blocks of period 14, none among the blocks of the other trap
   modules, the kit's, or those the finite game excludes at width 6, 10 or 14.
3. **The reduction** (`census14_absorption_excludes`). For each of them, if every finitely supported right half
   driven by the block enters its trap (`WTrap.Absorption`), the center column does not eventually repeat the block.

## Argument

As in [CensusTraps13](CensusTraps13.md): a bottom component of a block's locked nodes is a closed set of windows on
which column 1 is fixed at the white phases, and its chain, from the last column it fixes as a function of the phase,
carries it leftward to a trap of $16 + d$ cells for the block $d$ columns left (`component_tables` in
[computations/lock_chain.py](../../computations/lock_chain.py)). The kernel checks every trap, so neither the census
nor the carrying is trusted, and [WordTraps](WordTraps.md)'s `absorption_excludes` gives each reduction.

The traps come from seven components, of 126 to 174 states, carried 0 to 88 columns. 116 of the blocks lie in chains
that end in the background of 1,316 cells and 69 in chains that end in that of 644, where 15 and 14 traps of
[NaturalTrapsLong](NaturalTrapsLong.md) end as well, though no module carried them leftward; 47 lie in chains that end
in the background of 728 cells, where [FourteenTraps](FourteenTraps.md) carries one wall, in the part before those
chains repeat. The other 12 blocks are reached only by their own components, of 3,169 to 15,546 states, which
[CensusTrapsLarge](CensusTrapsLarge.md) checks in parts.

## What it covers

Each trap reduces its block to entry. Small halves enter the traps carried a short way: of the 224 pairs of a right
half with support in cells 1 to 4 and a phase, every pair enters 11 of the traps, carried 1 to 6 columns, within
20,000 steps, the latest at step 17,233; some pairs enter 49 more, carried 2 to 20 columns; and no pair enters the
other 172, carried 5 to 88 columns (`census_entry`). For four of the blocks every sampled half of the natural scan is
inside a larger trap of 16 cells, which [NaturalTrapsLongLarge](NaturalTrapsLongLarge.md) checks. Entry for every
finite right half stays open, as for the kit's traps.

**The test of reach.** In the game of 20 cells, 30 of the 232 traps here, of 18 to 104 cells, fail the test of
[MissedTraps](MissedTraps.md): some node cannot reach a window whose first cells form a state of the trap, cut to 20
cells when the trap is wider, so a right half whose first 20 cells start there never enters, and entry into the trap is
false ([what failed](../../negative-results/columns/missed-traps.md)). [RefutedTraps](RefutedTraps.md) checks the
refutation of seven of them in Lean. For 27 of their blocks no trap of any module passes, so the reduction is empty; the
other 3 keep a natural trap of [NaturalTrapsLongLarge](NaturalTrapsLongLarge.md) that passes. The other 202 traps pass
the test, which entry needs but does not imply.

## Relation to the kit

The kit's traps are `t001` for $001$ and its ether-and-wall family for the words of period four; it has none for a block
of period 14, and none of these blocks is among those it excludes.

## Lean

`Rule30Open.Columns.CensusTraps14`: the traps `cen<block>` with their checks, `censusTraps14`, `censusTraps14_check`,
`censusTraps14_blocks` and `census14_absorption_excludes`. The tables come from
`python -m computations.lock_chain --lean-census 14`; the kernel checks the module in about 19 seconds with a peak near
380 MB. The lists are long enough that the two theorems over them raise Lean's recursion limit (`maxRecDepth`).

## Reproduce

```bash
python -m computations.lock_chain --lock-backgrounds 14 --width 16 --workers 3
python -m computations.lock_chain --census-entry 14 --cells 4 --steps 20000
```

The first, the census at period 14, takes about half an hour with three processes; the second, entry into each trap
here, about an hour.
