---
title: Traps for 569 blocks of period 15, from every locked window of 16 cells carried leftward
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.CensusTraps15
headline: [censusTraps15_check, censusTraps15_blocks, census15_absorption_excludes]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/lock_chain.py, computations/coverage.py]
---

# Traps for 569 blocks of period 15, from every locked window of 16 cells carried leftward

[The census of locked windows of 16 cells](../../findings/columns/space-time-backgrounds.md), as in
[CensusTraps13](CensusTraps13.md), takes every block of period 15 and finds the bottom components of its locked windows,
with the phase counted modulo 15: 197 of the 2,182 blocks have one. The chain of each component ends in one of six
backgrounds of period 15, of 64, 85, 105, 540, 795 and 2,145 cells, each confirmed by running one of its rows on its
ring, and the chains hold 648 blocks of period 15: the 53 that the game or the kit excludes, and 595 that no trap module
reached before, since none had a trap of period 15. For 571 of the 595 a component of at most 3,000 states carries to
the block. For two of them, $000001010110101$ and $001001111010111$, that component is the block's own, which some node
of the finite game cannot reach, and so are those carried to them one and two columns; [MissedTraps](MissedTraps.md)
refutes entry into the first. For the other 569 this module checks the component of least cost, states times cells.

## Statement

1. **The traps** (`censusTraps15`, `censusTraps15_check`). A list of 569 labelled traps `WTrap` with labels modulo 15,
   each passing the check of [WordTraps](WordTraps.md) in its own declaration (`cen<block>_check`): 131 to 2,829
   states, 16 to 129 cells.
2. **The blocks** (`censusTraps15_blocks`): 569 distinct blocks of period 15, none the kit's or excluded by the finite
   game at width 6, 10 or 14.
3. **The reduction** (`census15_absorption_excludes`). For each of them, if every finitely supported right half
   driven by the block enters its trap (`WTrap.Absorption`), the center column does not eventually repeat the block.

## Argument

As in [CensusTraps13](CensusTraps13.md): a bottom component of a block's locked nodes is a closed set of windows on
which column 1 is fixed at the white phases, and its chain, from the last column it fixes as a function of the phase,
carries it leftward to a trap of $16 + d$ cells for the block $d$ columns left (`component_tables` in
[computations/lock_chain.py](../../computations/lock_chain.py)). The kernel checks every trap, so neither the census
nor the carrying is trusted, and [WordTraps](WordTraps.md)'s `absorption_excludes` gives each reduction.

The traps come from 62 components, of 131 to 2,829 states, carried 0 to 113 columns. By the background their chains
end in, 370 of the blocks belong to that of 2,145 cells, 85 to that of 795, 56 to that of 64, 27 to that of 540, 19 to
that of 105 and 12 to that of 85. The other 24 blocks are reached only by their own components, of 3,172 to 30,345
states, which [CensusTrapsLarge15](CensusTrapsLarge15.md) checks in parts.

## What it covers

Each trap reduces its block to entry. With [CensusTrapsLarge15](CensusTrapsLarge15.md), 593 of the 2,182 blocks of
period 15 have a trap in Lean, every block that a chain of a locked window of 16 cells holds and nothing excludes but
the two of [MissedTraps](MissedTraps.md), and 538 a trap that passes the test of reach below. No entry census of small
halves has been run at this period; at periods 13 and 14 small halves enter the traps carried a short way and few of
those carried far ([CensusTraps13](CensusTraps13.md), [CensusTraps14](CensusTraps14.md)). Entry for every finite right
half stays open, as for the kit's traps.

**The test of reach.** In the game of 20 cells, 56 of the 569 traps here, of 16 to 115 cells, fail the test of
[MissedTraps](MissedTraps.md): some node cannot reach a window whose first cells form a state of the trap, cut to 20
cells when the trap is wider, so a right half whose first 20 cells start there never enters, and entry into the trap is
false ([what failed](../../negative-results/columns/missed-traps.md)). [RefutedTraps](RefutedTraps.md) checks the
refutation of 22 of them in Lean. For 56 of their blocks no trap of any module passes, so the reduction is empty. The
other 513 traps pass the test, which entry needs but does not imply. For 14 of the traps that pass, a half of the
block's natural scan, closing windows of 16 to 64 cells, is inside a closed set apart from the trap, so entry into each
is false too, and [TrapSets](TrapSets.md) reduces their blocks to entry into one of several traps.

## Relation to the kit

The kit's traps are `t001` for $001$ and its ether-and-wall family for the words of period four; it has none for a block
of period 15, and none of these blocks is among those it excludes.

## Lean

`Rule30Open.Columns.CensusTraps15`: the traps `cen<block>` with their checks, `censusTraps15`, `censusTraps15_check`,
`censusTraps15_blocks` and `census15_absorption_excludes`. The tables come from
`python -m computations.lock_chain --lean-census 15`; the kernel checks the module in about 80 seconds with a peak near
650 MB. The lists are long enough that the two theorems over them raise Lean's recursion limit (`maxRecDepth`).

## Reproduce

```bash
python -m computations.lock_chain --lock-backgrounds 15 --width 16 --workers 3
```

The census at period 15, about an hour with three processes; it prints each background with the number of steps after
which one of its rows returns on its ring.
