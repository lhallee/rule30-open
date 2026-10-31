---
title: Lean refutations of entry into 102 traps of the trap modules
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.RefutedTraps
headline: [refutedTraps_not_absorption, nine15_not_absorption, tw1_4_not_absorption, cen0011111101111_not_absorption]
kit: new
kit_modules: [Rule30EtherThree, Rule30Ether]
evidence: [computations/lock_chain.py]
---

# Lean refutations of entry into 102 traps of the trap modules

In the game of 20 cells some node cannot reach each of 240 traps that the trap modules still hold, so entry into each
is false and its reduction is empty ([what failed](../../negative-results/columns/missed-traps.md)). That is a
computation. This module checks the refutation in Lean for 102 of them: 1 of [WordTraps](WordTraps.md), 1 of
[NineTraps](NineTraps.md), 7 of [TenTraps](TenTraps.md), 15 of [ElevenTraps](ElevenTraps.md), 13 of
[TwelveTraps](TwelveTraps.md), 13 of [ThirteenTraps](ThirteenTraps.md), 15 of [FourteenTraps](FourteenTraps.md), 1 of
[FarWalls](FarWalls.md), 7 of [CensusTraps13](CensusTraps13.md), 7 of [CensusTraps14](CensusTraps14.md) and 22 of
[CensusTraps15](CensusTraps15.md).

## Statement

1. **The closed sets** (`away_<trap>`, `away_<trap>_closed`, `away_<trap>_apart`). For each of the 102 traps, a set of
   windows of 2 to 17 cells with labels modulo the period, 21 to 1,935 states, that passes `WTrap.closedCheck` of
   [MissedTraps](MissedTraps.md), so that the move of each state, under either value of the cell beyond, is a state,
   and that is apart from the trap: no state of the trap, cut to the set's width, is a state of the set whose label
   reads the same phase.
2. **The refutations** (`<trap>_not_absorption`, `refutedTraps_not_absorption`). For each of the 102 traps, some
   finitely supported right half driven by its block, from some phase, never has its first cells in a state of the
   trap: $\lnot\,$`C.Absorption`.

## Argument

`not_absorption` of [MissedTraps](MissedTraps.md): the right half whose first cells are state 0 of the closed set,
white beyond, driven from the phase that state's label reads, keeps its first cells in the set whatever the cells
beyond them do, and the set is apart from the trap, so the half never enters. Each set comes from the game
(`miss_tables` in [computations/lock_chain.py](../../computations/lock_chain.py)): at the least width $w$ at which some
node of the game of $w$ cells cannot reach the trap cut to $w$ cells, the least strongly connected component, among
those nodes, that no move leaves. The kernel checks closure and separation for each set, so the game is not trusted.

## What it covers

The 102 are the traps of `UNREACHED` that fail at a width up to 17, where `miss_tables` gives a set of at most 2,000
states and the separation compares at most 300,000 pairs of states (`refuted_entries`). Three fail already at 2 cells:
the period-9 wall carried 15 columns, to $001101111$ (`nine15`, 58 cells), a period-12 wall carried 4 columns, to
$001101101111$ (`tw1_4`, 20 cells), and the census trap of $0011111101111$ (20 cells). For each, a set of 21 to 31
windows of the first two cells, with their phases, is never left, while the trap fixes those two cells to the columns
of its background at those phases. The other 138 traps of `UNREACHED` fail only at 18 to 20 cells or need larger sets;
`not_absorption` and `not_absorption_wide` would check them the same way. With the seven of MissedTraps and the ten
single traps of the pairs of [NaturalTrapsWalls](NaturalTrapsWalls.md), entry into 119 traps found here is refuted in
Lean.

## Relation to the kit

The kit refutes entry into each of its own period-four certificates `S0001`, `S0011` and `S0111`
(`Rule30Ether.never_enters_S0001` and the two after it) with an explicit right half that stays in deeper members of
the ether-and-wall family. Here the refutations are for traps of periods 2 and 9 to 15, by a closed set the kernel
checks, in the form of the kit's `AbsorptionT`.

## Lean

`Rule30Open.Columns.RefutedTraps`: the sets `away_<trap>` with `_closed` and `_apart`, the refutations
`<trap>_not_absorption`, the list `refutedTraps` and `refutedTraps_not_absorption`. The traps are those of their
modules, by name (`module_entries`). The sets come from `python -m computations.lock_chain --lean-refuted`.

## Reproduce

```bash
python -m computations.lock_chain --lean-refuted
```

The sets, in about six minutes; `test_refuted_traps` checks one of them against the rule directly.
