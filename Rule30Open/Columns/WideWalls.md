---
title: Walls of 22 cells beside traps carried far along a background's columns, and entry into one of the two
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.WideWalls
headline: [wideWalls_check, widePair_00100100101_excludes, el0_33_not_absorption_fwd, wide_el0_33_not_absorption]
kit: new
kit_modules: [Rule30EtherThree, Rule30Ether]
evidence: [computations/lock_chain.py]
---

# Walls of 22 cells beside traps carried far along a background's columns, and entry into one of the two

A trap carried $d$ columns along the chain of a background periodic in time fixes its first $d$ cells to the
background's columns ([ElevenTraps](ElevenTraps.md), [FourteenTraps](FourteenTraps.md)). In the game of 22 cells
three such traps, of 46 to 49 cells carried 30 to 33 columns, fail the test of reach of [MissedTraps](MissedTraps.md)
while all but 0.03 to 0.08 percent of the nodes can reach them
([what failed](../../negative-results/columns/missed-traps.md)). The nodes that cannot form a set that no move leaves,
and its least part that no move leaves is a set of 130 to 225 windows of 22 cells on which column 1 is fixed at the
white phases: a trap of the same block, a wall that the census of locked windows of 16 cells does not see. Every node
of the game of 22 cells can reach it. The carried trap and its wall are apart from each other: no state of one, cut to
22 cells, is a state of the other at a label of the same phase. So entry into either alone is false,
and each block comes down to entry into one of the two, which passes the test at 22 cells.

## Statement

1. **The walls** (`wideWalls`, `wideWalls_check`, `wideWalls_blocks`). Three labelled traps `WTrap` of 22 cells with
   labels modulo the period, `wide_<trap>` for the carried trap `<trap>`, each passing the check of
   [WordTraps](WordTraps.md):

   | Block | Carried trap | Its cells | Its states | Share of nodes that can reach it | Wall | Wall's states |
   |---|---|---:|---:|---:|---|---:|
   | $00100100101$ | `el0_33` | 49 | 313 | 0.999709 | `wide_el0_33` | 195 |
   | $00010100100011$ | `fo0_30` | 46 | 225 | 0.999214 | `wide_fo0_30` | 225 |
   | $00111011110101$ | `fo0_31` | 47 | 225 | 0.999517 | `wide_fo0_31` | 130 |

2. **Entry into the carried trap is false** (`<trap>_not_absorption_fwd`). Each wall is a closed set
   (`wide_<trap>_closed`) that avoids the carried trap's states cut to 22 cells (`wide_<trap>_cut`, `_holds`,
   `_avoids`), so by `not_absorption_fwd` of [ReachRefuted](ReachRefuted.md) the right half of state 0 of the wall
   never enters the carried trap.
3. **Entry into the wall is false** (`wide_<trap>_not_absorption`). The carried trap is closed
   (`<trap>_closed_wide`) and avoids the wall's states (`wide_<trap>_apart`, `_holds`, `_avoids`), so the right half
   of state 0 of the carried trap never enters the wall.
4. **The reduction** (`widePair_<block>`, `widePair_<block>_excludes`). For each block, if every finitely supported
   right half driven by it enters the carried trap or its wall (`WTrap.AbsorptionSome` of [TrapPairs](TrapPairs.md)),
   the center column does not eventually repeat the block.

## Argument

The test of reach in the game of 22 cells finds, for each carried trap, the nodes from which some values of cell 23
lead into the trap cut to 22 cells (`reach_nodes` in [computations/lock_chain.py](../../computations/lock_chain.py)).
The rest form a set that no move leaves; `fwd_tables` takes the least strongly connected part of it that no move leaves
and writes it as a trap (`wide_wall`). The kernel checks that it is closed and that column 1 is fixed on it at the white
phases (`WTrap.check`), and that no state of it is a state of the carried trap cut to 22 cells with the same phase, and
no state of the carried trap so cut a state of it, so neither the search nor the cut is trusted. A right half that
starts in either stays in it, so it never enters the other; entry into one of the two gives column 1 eventually
periodic, which `absorption_some_excludes` turns into the exclusion of the block.

## What it covers

Every node of the game of 22 cells can reach each wall, so the pair passes the test of reach there, and the blocks
count as reduced in [the coverage table](../../findings/columns/coverage.md). Entry into one of the two for every finite
right half stays open, and, as for the other blocks reduced to entry into a trap, the hypothesis that no further trap
can refute is entry into some trap of the block ([Traps001](Traps001.md)).

## Relation to the kit

The kit's traps are `t001` and the ether-and-wall family for the words of period four; it has none for these blocks.

## Lean

`Rule30Open.Columns.WideWalls`: the walls `wide_<trap>` with `_check`, `_closed`, `_cut`, `_holds` and `_avoids`, the
refutations `<trap>_not_absorption_fwd` and `wide_<trap>_not_absorption` with `<trap>_closed_wide` and
`wide_<trap>_apart`, the pairs `widePair_<block>` with `widePair_<block>_excludes`, and `wideWalls`, `wideWalls_check`
and `wideWalls_blocks`. The tables come from `python -m computations.lock_chain --lean-wide-walls`.

## Reproduce

```bash
python -m computations.lock_chain --lean-wide-walls
```

The walls, from the test of reach at 22 cells of each carried trap, in a few minutes; `test_wide_walls` checks each
wall with the rule and the separation both ways.
