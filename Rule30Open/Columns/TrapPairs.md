---
title: Four blocks of periods 13 and 14 reduced to entry into one of two traps
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.TrapPairs
headline: [absorption_some_excludes, pair0001101101011_excludes, pair0010101111111_excludes]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/lock_chain.py]
---

# Four blocks of periods 13 and 14 reduced to entry into one of two traps

The reduction of [WordTraps](WordTraps.md) asks every finitely supported right half driven by a block to enter one
trap. Nothing in its argument needs a single trap: a half that enters any checked trap of the block contradicts Jen's
theorem on adjacent columns from then on. This module proves the reduction for a list of traps and applies it to four
blocks whose locked windows of 16 cells have two bottom components each:

| block | period | traps, in states | nodes of the 16-cell game that can reach each | that can reach one of the two |
|---|---|---|---|---|
| $0001101101011$ | 13 | 616 and 430 | 97.37% and 95.35% | all |
| $0010010010111$ | 13 | 678 and 423 | 97.17% and 92.09% | all |
| $0010101111111$ | 13 | 13,159 and 1,196 | 94.87% and 34.58% | all |
| $00001101111001$ | 14 | 168 and 428 | 47.34% and 95.62% | all |

Entry into either trap alone is false, since the nodes that cannot reach it form a set that no move leaves;
[MissedTraps](MissedTraps.md) proves this for the second of each pair, the trap the natural scan took. Entry into one of
the two passes that test and is open.

## Statement

1. **Entry into one of several traps** (`WTrap.AbsorptionSome`). For a list $C_1, \dots, C_k$ of traps of one block
   $b$: every finitely supported right half driven by $b$, from any phase, eventually has its first cells in a state
   of some $C_j$ with the label of the right phase.
2. **The reduction** (`absorption_some_excludes`). If every $C_j$ passes the check of [WordTraps](WordTraps.md) and
   entry into one of them holds, the center column does not eventually repeat $b$, for any transient
   (`Rule30StripCertificates.EventuallyWord`).
3. **The four blocks** (`pair<block>_excludes`). For each block of the table, with `pair<block>` its two traps
   `pair<block>_0` and `pair<block>_1`, each passing the check: entry into one of the two excludes the block.

## Argument

Suppose the center column repeats $b$ from time $T$. The right half at time $T$ is finitely supported, by the light
cone, and from then on it is the half driven by $b$ from phase 0 (`Rule30Ether.cell_eq_drv`). Entry into one of the
traps gives a time $t_1$ and a state of some $C_j$, with the label of the right phase, that cells $1, \dots, K$ of the
single cell's row form at $T + t_1$. From there the argument is that of `absorption_excludes` for the single trap
$C_j$: the window stays in $C_j$, so the cell beside the center is a function of the phase at the white phases, the
column left of the center repeats with period the labels' modulus, and Jen's theorem on adjacent columns rules that
out. `entry_excludes` is that step, written for one trap and the half of time $T$; `absorption_some_excludes` picks
the trap that entry gives.

The traps are the bottom components of the locked windows of 16 cells (`pair_tables`, `component_tables` at distance 0
in [computations/lock_chain.py](../../computations/lock_chain.py)). The two of each block fix different values of
column 1 at the white phases, so their union is not one trap. `trap_reach` gives the shares of the table, and with both
traps at once the share 1: every node can reach a locked node, and every locked node reaches one of the two
components. The kernel checks each trap, the one of 13,159 states in parts of 1,024 as in
[NaturalTrapsLarge](NaturalTrapsLarge.md).

## What it covers

The four blocks are reduced again, to a hypothesis that the test of [MissedTraps](MissedTraps.md) does not refute. The
natural scan's own sampled halves show why a pair is needed: driven by $0001101101011$, its 31 halves end in the trap of
430 states or in that of 616, and driven by $0010101111111$ in that of 1,196 or that of 13,159. The chains of the two
components of $0001101101011$ end in different backgrounds, of 689 and 533 cells. Entry into one of two traps for every
finite right half stays open, as entry does for the kit's traps.

**The test of reach.** In the game of 20 cells as well, where the cells after the traps' 16 follow the rule instead of
taking any value, every node can reach a window whose first 16 cells form a state of one of the two traps of each pair,
as the test of [MissedTraps](MissedTraps.md) needs ([what failed](../../negative-results/columns/missed-traps.md)).
Entry into one of the two needs this but is not implied by it. A half of the natural scan of $0001101101011$, closing
windows of 16 to 64 cells, is inside a closed set of 21 cells apart from both of its traps, so entry into one of the two
is false for that block, and [TrapSets](TrapSets.md) reduces it to entry into one of three.

## Relation to the kit

The kit's `AbsorptionT` asks entry into one trap, `t001`; its period-four `Absorption` asks entry into one member of
the ether-and-wall family, an infinite list of traps, after its single certificates fail
(`Rule30Ether.never_enters_S0001` and the two after it). `AbsorptionSome` is the same move for a finite list of
`WTrap`s of any period.

## Lean

`Rule30Open.Columns.TrapPairs`: `WTrap.AbsorptionSome`, `entry_excludes`, `absorption_some_excludes`; the traps
`pair<block>_0` and `pair<block>_1` with their checks, `pair<block>` and `pair<block>_excludes`. The tables come from
`python -m computations.lock_chain --lean-pairs`; the kernel checks the module in about 15 seconds.

## Reproduce

```bash
python -m computations.lock_chain --lean-pairs
```

The traps, from the bottom components of each block's game of 16 cells, in about a minute; `test_trap_pairs` checks
the shares.
