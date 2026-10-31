---
title: The kit's trap for 001 does not take every right half, so its AbsorptionT t001 is false
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.Traps001
headline: [not_absorptionT_t001, trap001fifteen_not_absorption, traps001_excludes]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30EtherThree]
evidence: [computations/period_three.py]
---

# The kit's trap for 001 does not take every right half, so its AbsorptionT t001 is false

The kit reduces the word $001$ of least period three to entry into its trap `t001`: 815 states of the first 47 cells
beside the center, with labels modulo 21, closed under both values of cell 48. If every finitely supported right half
driven by $001$, from any phase, enters `t001` (`AbsorptionT t001`), the center column is not eventually $001$
repeated; the kit states the entry as open, with every one of 18,258 tested halves entering. [WordTraps](WordTraps.md)
has a second trap for $001$, `trap001fifteen`: 153 states of the first 52 cells, with labels modulo 15. No state of
either trap, cut to 47 cells, is a state of the other with a label of the same phase. A right half that starts in one
trap stays in it whatever the cells beyond do, so it never enters the other, and entry into either trap alone is false.

## Statement

1. **The kit's statement is false** (`not_absorptionT_t001`): $\lnot\,$`Rule30EtherThree.AbsorptionT t001`, the
   kit's own proposition about its own trap. The right half whose cells 1 to 52 are
   $$0101000110001001110111111110101000000111010011010000,$$
   cell 1 first, state 0 of `trap001fifteen` with label 0, white from cell 49 on, driven by $001$ from phase 0, never
   has its cells 1 to 47 in a state of `t001` whose label reads the drive's phase.
2. **Entry into the second trap is false too** (`trap001fifteen_not_absorption`): the half of state 0 of `t001`, white
   from cell 48 on, never enters `trap001fifteen`.
3. **The reduction that remains** (`traps001_excludes`). If every finitely supported right half driven by $001$, from
   any phase, enters one of the two traps (`WTrap.AbsorptionSome traps001`), the center column does not eventually
   repeat $001$.

## Argument

`t001W` is the kit's trap with the kit's packed tables, written as a trap of WordTraps; the kit's `AbsorptionT t001`
is `t001W.Absorption` by definition (`absorptionT_t001_iff`, `Iff.rfl`). The kernel checks that each trap is closed
(`t001W_closed`, `trap001fifteen_closed`, `WTrap.closedCheck` of [MissedTraps](MissedTraps.md)) and that no state of
`trap001fifteen`, cut to its first 47 cells, is a state of `t001` whose label is congruent to it modulo 3, the drive's
phase (`fifteen_apart_t001`, `t001_apart_fifteen`): 124,695 comparisons. A half that starts in `trap001fifteen` keeps
its first 52 cells in it at every step, the label advancing with the phase, so its first 47 cells are never a state of
`t001` with the right label; that is `not_absorption_wide` of MissedTraps, and the other direction is its
`not_absorption`. The reduction to entry into one of the two is `absorption_some_excludes` of
[TrapPairs](TrapPairs.md), with both traps checked (`t001W_check`, `trap001fifteen_check`).

The separation is forced. On each trap, cell 1 at the white phases is a function of the label, with period 21 on
`t001` and 15 on `trap001fifteen`; on a common orbit it would repeat with period 3, and the kit's function for `t001`
does not.

## What it means

The kit's route for $001$ needs more than one trap. Small halves enter `t001`: every one of at most ten cells, from each
phase ([the census for 001](../../findings/columns/t001-census.md)), and none of them the second trap; the test of reach
for `t001` passes in every game up to 26 cells ([reach of the kit's
conjectures](../../findings/columns/kit-absorption-reach.md)), games too narrow to hold the second trap, so `t001` fails
the test in the game of 52 cells at the latest. Whether every finite half enters one of the two traps is open, as is the
weaker `Lock` for $001$ that the kit's pull request #65 proposes, which entry into any trap implies ([the kit's pull
requests](../../literature/kit-pull-requests.md)); a third trap for $001$ apart from both would refute the pair in turn.

## Relation to the kit

`Rule30EtherThreeTrap` defines `t001`, `AbsorptionT` and `not_eventually_001_of_absorption`, and calls the entry
open. This module refutes it with the kit's own definitions and proposes entry into one of two traps in its place.

## Lean

`Rule30Open.Columns.Traps001`: `t001W`, `absorptionT_t001_iff`, the checks `t001W_check`, `t001W_closed`,
`trap001fifteen_closed`, `fifteen_apart_t001` and `t001_apart_fifteen`, the refutations `not_absorptionT_t001` and
`trap001fifteen_not_absorption`, and `traps001`, `traps001_excludes`. It builds in about 20 seconds.

## Reproduce

```bash
python -m computations.period_three --trap --cells 10 --steps 400000
```

The census of entry into `t001` for every small half. The trap of 52 cells is the one of WordTraps, whose tables
`python -m computations.lock_chain --lean` prints.
