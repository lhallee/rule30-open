---
title: Traps for 22 more blocks of periods 13 and 14, from locked windows of 16 cells, checked in parts
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.CensusTrapsLarge
headline: [censusTrapsLarge_check, censusTrapsLarge_blocks, censusLarge_absorption_excludes]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/lock_chain.py, computations/coverage.py]
---

# Traps for 22 more blocks of periods 13 and 14, from locked windows of 16 cells, checked in parts

[The census of locked windows of 16 cells](../../findings/columns/space-time-backgrounds.md) reaches 135 blocks of
period 13 and 244 of period 14 that no earlier trap module has and nothing excludes. [CensusTraps13](CensusTraps13.md)
and [CensusTraps14](CensusTraps14.md) check traps of at most 3,000 states for all but 23 of them. For one,
$0000010111001$, [MissedTraps](MissedTraps.md) refutes entry into its trap; only its own bottom component, of 3,169 to
22,746 states, reaches each of the other 22, 10 of period 13 and 12 of period 14. This module checks those 22 components
as they are, in parts, as [NaturalTrapsLarge](NaturalTrapsLarge.md) checks its trap. With it every block that the chains
of the locked windows of 16 cells hold at periods 13 and 14 is excluded or reduced in Lean, four of them by
[TrapPairs](TrapPairs.md), but $0000010111001$.

## Statement

1. **The traps** (`censusTrapsLarge`, `censusTrapsLarge_check`). A list of 22 labelled traps `WTrap` of 16 cells, with
   labels modulo the period, of 3,169 to 22,746 states, each passing the check of [WordTraps](WordTraps.md)
   (`cen<block>_check`), gathered from parts of 1,024 states (`cen<block>_<part>`, `cen<block>_parts`).
2. **The blocks** (`censusTrapsLarge_blocks`): 10 blocks of period 13 and 12 of period 14, distinct, none among the
   blocks of the other trap modules, the kit's, or those the finite game excludes at width 6, 10 or 14.
3. **The reduction** (`censusLarge_absorption_excludes`). For each of them, if every finitely supported right half
   driven by the block enters its trap (`WTrap.Absorption`), the center column does not eventually repeat the block.

## Argument

Each trap is a bottom component of the block's locked windows of 16 cells, a closed set of windows on which column 1 is
fixed at the white phases, as in [CensusTraps13](CensusTraps13.md), here not carried (`component_tables` at distance 0
in [computations/lock_chain.py](../../computations/lock_chain.py)). Each is also the natural trap of its block, the one
that [NaturalTrapsLong](NaturalTrapsLong.md) leaves out for its size: every one of the 31 sampled halves of the natural
scan is inside it at step 12,000. The packed numbers of each have up to about 370,000 bits, so they are written in
pieces of 65,536 bits, and the check runs over ranges of 1,024 states, one kernel check each, which `allRange_cover` and
`allBelowT_of_forall` of [NaturalTrapsLarge](NaturalTrapsLarge.md) gather into the check of [WordTraps](WordTraps.md)
(`lean_parts`). The kernel checks every part, so the census is not trusted, and `absorption_excludes` gives each
reduction.

## What it covers

Each trap reduces its block to entry. Entry for every finite right half stays open, as for the kit's traps.

## Relation to the kit

The kit's traps are `t001` for $001$ and its ether-and-wall family for the words of period four; it has none for a block
of period 13 or 14, and none of these blocks is among those it excludes.

## Lean

`Rule30Open.Columns.CensusTrapsLarge`: the traps `cen<block>` with their parts and checks, `censusTrapsLarge`,
`censusTrapsLarge_check`, `censusTrapsLarge_blocks` and `censusLarge_absorption_excludes`. The traps and parts come from
`python -m computations.lock_chain --lean-census-large`; the kernel checks the module in about three minutes with a peak
near 700 MB.

## Reproduce

```bash
python -m computations.lock_chain --lock-backgrounds 13,14 --width 16 --workers 3
```

The census at periods 13 and 14, about 45 minutes with three processes; the test builds each trap from its component
and checks it with the rule on whole windows (`is_lock`).
