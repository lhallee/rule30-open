---
title: Traps for 24 more blocks of period 15, from locked windows of 16 cells, checked in parts
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.CensusTrapsLarge15
headline: [censusTrapsLarge15_check, censusTrapsLarge15_blocks, censusLarge15_absorption_excludes]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/lock_chain.py, computations/coverage.py]
---

# Traps for 24 more blocks of period 15, from locked windows of 16 cells, checked in parts

[The census of locked windows of 16 cells](../../findings/columns/space-time-backgrounds.md) reaches 595 blocks of
period 15 that nothing excludes. [CensusTraps15](CensusTraps15.md) checks traps of at most 3,000 states for 569 of them,
[MissedTraps](MissedTraps.md) refutes the traps of two more, and only its own bottom component, of 3,172 to 30,345
states, reaches each of the other 24. This module checks those 24 components as they are, in parts, as
[CensusTrapsLarge](CensusTrapsLarge.md) does at periods 13 and 14. With it every block of period 15 that the chains of
the locked windows of 16 cells hold is excluded or has a trap in Lean, but the two of MissedTraps; for 55 of them,
though, the trap fails the test of reach of [CensusTraps15](CensusTraps15.md), so their reductions are empty.

## Statement

1. **The traps** (`censusTrapsLarge15`, `censusTrapsLarge15_check`). A list of 24 labelled traps `WTrap` of 16 cells,
   with labels modulo 15, of 3,172 to 30,345 states, each passing the check of [WordTraps](WordTraps.md)
   (`cen<block>_check`), gathered from parts of 1,024 states (`cen<block>_<part>`, `cen<block>_parts`).
2. **The blocks** (`censusTrapsLarge15_blocks`): 24 distinct blocks of period 15, none among the blocks of the other
   trap modules, the kit's, or those the finite game excludes at width 6, 10 or 14.
3. **The reduction** (`censusLarge15_absorption_excludes`). For each of them, if every finitely supported right half
   driven by the block enters its trap (`WTrap.Absorption`), the center column does not eventually repeat the block.

## Argument

As in [CensusTrapsLarge](CensusTrapsLarge.md): each trap is a bottom component of the block's locked windows of 16
cells, not carried (`component_tables` at distance 0 in [computations/lock_chain.py](../../computations/lock_chain.py)),
its numbers written in pieces of 65,536 bits and its check run over ranges of 1,024 states, one kernel check each,
gathered by `allRange_cover` and `allBelowT_of_forall` of [NaturalTrapsLarge](NaturalTrapsLarge.md) (`lean_parts`).
The kernel checks every part, so the census is not trusted, and `absorption_excludes` gives each reduction.

## What it covers

Each trap reduces its block to entry. Their chains end in the backgrounds of 2,145 cells (17 blocks), 795 (4), 64 (2)
and 540 (1). Entry for every finite right half stays open, as for the kit's traps.

**The test of reach.** Cut to their first 20 cells, every trap here passes the test of [MissedTraps](MissedTraps.md):
every node of the finite game of 20 cells can reach the trap's states so cut ([what
failed](../../negative-results/columns/missed-traps.md)). Entry needs this but is not implied by it.

## Relation to the kit

The kit's traps are `t001` for $001$ and its ether-and-wall family for the words of period four; it has none for a block
of period 15, and none of these blocks is among those it excludes.

## Lean

`Rule30Open.Columns.CensusTrapsLarge15`: the traps `cen<block>` with their parts and checks, `censusTrapsLarge15`,
`censusTrapsLarge15_check`, `censusTrapsLarge15_blocks` and `censusLarge15_absorption_excludes`. The traps and parts
come from `python -m computations.lock_chain --lean-census-large 15`; the kernel checks the module in about three
minutes with a peak near 810 MB.

## Reproduce

```bash
python -m computations.lock_chain --lock-backgrounds 15 --width 16 --workers 3
```

The census at period 15, about an hour with three processes.
