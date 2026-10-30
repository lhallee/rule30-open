---
title: Traps for 74 blocks of periods 13 and 14, the closed sets that driven right halves settle into
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.NaturalTrapsLong
headline: [naturalTrapsLong_check, naturalTrapsLong_blocks, naturalLong_absorption_excludes]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/lock_chain.py]
---

# Traps for 74 blocks of periods 13 and 14, the closed sets that driven right halves settle into

[The natural scan](../../findings/columns/natural-traps.md) with windows of 16 cells finds traps for 86 blocks of period
13 and 109 of period 14. The walls of [ThirteenTraps](ThirteenTraps.md) and [FourteenTraps](FourteenTraps.md) carry
traps to some of them, the kit or the finite game excludes others, and 52 and 56 are left. This module checks, for each
of those, the smallest trap the scan finds, when it has at most 3,000 states: 34 blocks of period 13 and 40 of period
14, as [NaturalTraps](NaturalTraps.md) does at periods 10 to 12.

## Statement

1. **The traps** (`naturalTrapsLong`, `naturalTrapsLong_check`). A list of 74 labelled traps `WTrap` of 16 cells with
   labels modulo the period, each passing the check of [WordTraps](WordTraps.md) in its own declaration
   (`nat<block>_check`).
2. **The blocks** (`naturalTrapsLong_blocks`): 34 blocks of period 13 and 40 of period 14, distinct, none among the
   blocks of the other trap modules.
3. **The reduction** (`naturalLong_absorption_excludes`). For each of them, if every finitely supported right half
   driven by the block enters its trap (`WTrap.Absorption`), the center column does not eventually repeat the block.

## Argument

As in [NaturalTraps](NaturalTraps.md): each trap is the closure, under both values of the cell beyond, of the window of
one driven half at step 12,000, the white half for all but four blocks (`natural_tables` in
[computations/lock_chain.py](../../computations/lock_chain.py)). The kernel checks each, so the closure is not trusted,
and [WordTraps](WordTraps.md)'s `absorption_excludes` gives each reduction.

## What it covers

Each trap reduces its block to entry. For 67 of the blocks every one of the 31 halves of the scan is inside a trap at
step 12,000. Carried leftward, the chains of the traps end in the backgrounds of 533 and 689 cells at period 13, 16 and
18 of them, and of 644, 728 and 1,316 cells at period 14, 14, 11 and 15 ([backgrounds periodic in
time](../../findings/columns/space-time-backgrounds.md)). Small halves enter these traps fast: every right half with
support in cells 1 to 4, driven from every phase, enters 61 of them within 8,255 steps, 52 within 2,500, and some of
those halves enter each of the other 13 (`extra_entry` with `--long-entry`). Entry for every finite right half stays
open, as for the kit's traps. The blocks whose traps have more than 3,000 states, 18 of period 13 and 16 of period 14,
are left out here and checked in parts: 22 in [CensusTrapsLarge](CensusTrapsLarge.md), where the trap is a component of
the census of locked windows, and 12 in [NaturalTrapsLongLarge](NaturalTrapsLongLarge.md).

## Relation to the kit

The kit's traps are `t001` for $001$ and its ether-and-wall family for the words of period four; it has none for a block
of period 13 or 14, and none of these blocks is among those it excludes.

## Lean

`Rule30Open.Columns.NaturalTrapsLong`: the traps `nat<block>` with their checks, `naturalTrapsLong`,
`naturalTrapsLong_check`, `naturalTrapsLong_blocks` and `naturalLong_absorption_excludes`. The tables come from
`python -m computations.lock_chain --lean-long`.

## Reproduce

```bash
python -m computations.lock_chain --long-entry --cells 4 --steps 20000
```

Entry into each trap here, in about four minutes; the scan is that of [ThirteenTraps](ThirteenTraps.md).
