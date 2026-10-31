---
title: Entry into 48 traps that pass the tests of reach is false, refuted by a wider trap of the same block
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ApartTraps
headline: [natw00001111111_not_absorption_apart, pair_00001111111_excludes, fw1_106_not_absorption_apart, nat0000110111001_not_absorption_apart]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/lock_chain.py]
---

# Entry into 48 traps that pass the tests of reach is false, refuted by a wider trap of the same block

The test of reach of [MissedTraps](MissedTraps.md) refutes entry into a trap when, in a finite game, the nodes that
cannot reach it form a set that no move leaves. A set that no move leaves can also be wider than every game searched:
another trap of the same block, closed whatever the cells beyond it do. For 48 traps that pass the test of reach at 20
or 22 cells and the test of halves apart, another trap of their block is apart from them: no state of it, cut to the
narrower width, is a state of the first whose label reads the same phase. A right half that starts in the other trap
never enters the first, so entry into the first is false. In each case the other trap is a carried trap whose own entry
was already false, and the block comes down to entry into one of the two.

| refuted traps | their module | states | refuted by carried traps of | cells | states |
|---|---|---|---|---|---|
| 40 of 16 cells | [NaturalTrapsWalls](NaturalTrapsWalls.md) | 110 to 11,099 | the wall modules: TenTraps 4, ElevenTraps 8, TwelveTraps 9, ThirteenTraps 6, FourteenTraps 13 | 27 to 85 | 100 to 313 |
| 5 of 16 cells | [NaturalTrapsLongLarge](NaturalTrapsLongLarge.md) | 3,295 to 6,669 | [CensusTraps13](CensusTraps13.md) 2, [CensusTraps14](CensusTraps14.md) 3 | 28 to 104 | 123 to 162 |
| 3 of 48, 143 and 146 cells | [FifteenWalls](FifteenWalls.md) | 652 | [CensusTraps15](CensusTraps15.md) 3 | 30 to 115 | 139 to 166 |

The blocks are 4 of period 10, 8 of 11, 9 of 12, 8 of 13, 16 of 14 and 3 of 15.

## Statement

For each entry of `APART_TRAPS` in [computations/lock_chain.py](../../computations/lock_chain.py), a refuted trap $C$
and the other trap $S$ of its block:

1. **The other trap is closed** (`apart_<C>_closed`): $S$ passes `WTrap.closedCheck`.
2. **The separation** (`apart_<C>`, `apart_<C>_holds`, `apart_<C>_avoids`). The states of $C$ cut to the narrower of
   the two widths, by label modulo the period, form a set of windows of [ReachRefuted](ReachRefuted.md) that holds them
   all, and no state of $S$, so cut, is in it at a label of the same phase.
3. **Entry into $C$ is false** (`<C>_not_absorption_apart`): the right half of state 0 of $S$, white beyond, driven from
   the phase of that state's label, never enters $C$, by `not_absorption_fwd`.
4. **The reduction** (`pair_<block>`, `pair_<block>_excludes`). If every finitely supported right half driven by the
   block enters $S$ or $C$, the center column does not eventually repeat the block, by `absorption_some_excludes` of
   [TrapPairs](TrapPairs.md) with both traps checked.

## Argument

`apart_pairs` in [computations/lock_chain.py](../../computations/lock_chain.py) takes every two traps of one block among
the traps checked in Lean, and computes the largest set of states of one that every move, under either value of the
cell beyond, keeps inside, among the states whose windows, cut to the narrower width, are not those of a state of the
other at a label of the same phase (`apart_closed`). Over all the trap modules it finds 228 ordered pairs with such a
set, refuting 202 traps; `apart_traps` keeps those whose refutation is new, where the trap passes the tests of reach and
of halves apart and the set is the whole other trap. The kernel then checks each as above, so neither the search nor
the cut is trusted. The natural traps of 16 cells pass the test of reach because the carried traps that refute them
are 27 to 104 cells wide, wider than the games of 20 and 22 cells; the natural scans found the natural traps where the
halves sampled settle, and the carried traps are the walls of the backgrounds carried along their chains, which no
sampled half was in.

## What it covers

These reductions were counted as entry into one trap that passes; they are entry into one of two traps, which passes
the test of reach since one of the two does. The coverage of each period is unchanged ([the
coverage](../../findings/columns/coverage.md)), and the number of traps whose entry is false grows by 48. The same
separation refutes the kit's `AbsorptionT t001` ([Traps001](Traps001.md)).

## Relation to the kit

The kit refutes entry into its own period-four certificates with a right half that stays in deeper members of its
family (`Rule30Ether.never_enters_S0001`), the same move: a trap of the block that the first one misses.

## Lean

`Rule30Open.Columns.ApartTraps`: for each of the 48 entries, `apart_<C>_closed`, `apart_<C>` with `_holds` and
`_avoids`, `<C>_not_absorption_apart`, and `pair_<block>` with `pair_<block>_excludes`. It builds in about six minutes.
The tables come from `python -m computations.lock_chain --lean-apart-traps`.

## Reproduce

```bash
python -m computations.lock_chain --apart-pairs
```

```bash
python -m computations.lock_chain --lean-apart-traps
```

The census of pairs builds every trap of the trap modules and takes about 12 minutes; the declarations take half a
minute. `test_apart_traps` checks each entry with `apart_closed` and that the declarations are those of the module,
and `test_apart_closed` checks `apart_closed` against closed sets computed from the rule cell by cell.
