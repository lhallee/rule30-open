---
title: The natural traps of 12 more blocks of periods 13 and 14, of 3,295 to 18,132 states, checked in parts
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.NaturalTrapsLongLarge
headline: [naturalTrapsLongLarge_check, naturalTrapsLongLarge_blocks, naturalLongLarge_absorption_excludes]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/lock_chain.py]
---

# The natural traps of 12 more blocks of periods 13 and 14, of 3,295 to 18,132 states, checked in parts

[The natural scan](../../findings/columns/natural-traps.md) of periods 13 and 14 with windows of 16 cells finds traps
for 34 blocks that nothing excludes and no wall carries whose smallest trap has more than 3,000 states, which
[NaturalTrapsLong](NaturalTrapsLong.md) leaves out. For each of them every one of the 31 sampled right halves is inside
that trap at step 12,000. For 22 the trap is a bottom component of the block's locked windows, which
[CensusTrapsLarge](CensusTrapsLarge.md) checks. For the other 12, 8 of period 13 and 4 of period 14, the census of
locked windows gives a smaller trap carried from farther left ([CensusTraps13](CensusTraps13.md),
[CensusTraps14](CensusTraps14.md)), which small halves enter less; this module checks the natural traps themselves, so
that the reduction of each block is to entry into a trap that sampled halves do enter.

## Statement

1. **The traps** (`naturalTrapsLongLarge`, `naturalTrapsLongLarge_check`). A list of 12 labelled traps `WTrap` of 16
   cells, with labels modulo the period, of 3,295 to 18,132 states, each passing the check of
   [WordTraps](WordTraps.md) (`nat<block>_check`), gathered from parts of 1,024 states.
2. **The blocks** (`naturalTrapsLongLarge_blocks`): 8 blocks of period 13 and 4 of period 14, distinct, none among
   the blocks of [NaturalTrapsLong](NaturalTrapsLong.md), each also a block of
   [CensusTraps13](CensusTraps13.md) or [CensusTraps14](CensusTraps14.md).
3. **The reduction** (`naturalLongLarge_absorption_excludes`). For each of them, if every finitely supported right half
   driven by the block enters its trap (`WTrap.Absorption`), the center column does not eventually repeat the block.

## Argument

As in [NaturalTrapsLong](NaturalTrapsLong.md): each trap is the closure, under both values of the cell beyond, of the
window of the white right half driven by the block at step 12,000 (`natural_tables` in
[computations/lock_chain.py](../../computations/lock_chain.py)). Its numbers are written in pieces of 65,536 bits and
its check runs over ranges of 1,024 states, one kernel check each, gathered as in
[NaturalTrapsLarge](NaturalTrapsLarge.md) (`lean_parts`). The kernel checks every part, so the closure is not trusted,
and [WordTraps](WordTraps.md)'s `absorption_excludes` gives each reduction.

## What it covers

Each trap reduces its block to entry, into a set that every sampled half of the scan has entered by step 12,000. With
this module and [CensusTrapsLarge](CensusTrapsLarge.md), every block of periods 13 and 14 for which the scan finds a
trap of 16 cells is excluded or reduced in Lean, as at periods 10 to 12, four of them by [TrapPairs](TrapPairs.md) to
entry into one of two traps. Entry for every finite right half stays open, as for the kit's traps.

**The test of reach.** In the game of 20 cells, where the cells after the trap's 16 follow the rule instead of taking
any value, every trap here passes the test of [MissedTraps](MissedTraps.md): every node can reach a window whose first
16 cells form a state of the trap ([what failed](../../negative-results/columns/missed-traps.md)). Entry needs this but
is not implied by it.

## Relation to the kit

The kit's traps are `t001` for $001$ and its ether-and-wall family for the words of period four; it has none for a block
of period 13 or 14, and none of these blocks is among those it excludes.

## Lean

`Rule30Open.Columns.NaturalTrapsLongLarge`: the traps `nat<block>` with their parts and checks,
`naturalTrapsLongLarge`, `naturalTrapsLongLarge_check`, `naturalTrapsLongLarge_blocks` and
`naturalLongLarge_absorption_excludes`. The traps and parts come from
`python -m computations.lock_chain --lean-long-large`; the kernel checks the module in about 70 seconds with a peak
near 620 MB.

## Reproduce

```bash
python -m computations.lock_chain --natural 13,14 --steps 20000 --max-width 16 --workers 3
```

The natural scan of [ThirteenTraps](ThirteenTraps.md), about 40 minutes with three processes.
