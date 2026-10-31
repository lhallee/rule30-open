---
title: Entry into the only trap of period 6 is false
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.SixRefuted
headline: [back_trap001011_check, trap001011_not_absorption_back]
kit: new
kit_modules: [Rule30EtherThree, Rule30Ether]
evidence: [computations/lock_chain.py]
---

# Entry into the only trap of period 6 is false

[WordTraps](WordTraps.md) checks `trap001011`, a trap of 29 cells for $001011$ with labels modulo 12, and reduces the
block to entry into it (`not_eventually_001011_of_absorption`). It is the only trap here for a block of period 6, and
in the game of 22 cells only 0.11% of the nodes can reach it ([what
failed](../../negative-results/columns/missed-traps.md)). This module checks that refutation in Lean.

## Statement

1. **The windows that can reach the trap** (`back_trap001011`, `back_trap001011_check`, `back_trap001011_holds`). A set
   of 28,666 of the 25,165,824 nodes of the game of 22 cells for $001011$, windows of 22 cells by label modulo 6, that
   holds every window with a move into one of its own (`WinSet.check` of [ReachRefuted](ReachRefuted.md)) and the
   states of `trap001011` cut to 22 cells (`WinSet.holds`).
2. **The refutation** (`trap001011_not_absorption_back`). The white right half driven by $001011$ from phase 0 never has
   its first 29 cells in a state of `trap001011`: $\lnot\,$`trap001011.Absorption`.

## Argument

`not_absorption_back` of [ReachRefuted](ReachRefuted.md): a set of windows closed under predecessors that holds the
trap's states, cut to its width, holds every node from which some cells beyond lead into the trap, so a right half whose
first 22 cells start outside it never has them in a state of the trap, whatever the cells after them do. The white
window at phase 0 is outside the set. The set comes from the game (`back_tables` in
[computations/lock_chain.py](../../computations/lock_chain.py), `--lean-six`), the nodes that can reach the trap found
backward from its states; the kernel checks closure label by label, in parts of 1,024 windows, so the game is not
trusted.

## What it covers

With this refutation every trap for a block of period 6 in Lean has a false hypothesis. The chains of seeds with a long
run of 1s give $001011$ three more traps, of 33, 35 and 154 cells, whose first 22 cells are those of `trap001011`, and
no window of up to 22 cells is locked for the block ([what failed](../../negative-results/columns/missed-traps.md)), so
a hypothesis for $001011$ that can hold needs a trap that does not begin with the background's columns, wider than 22
cells. The reduction to entry into some trap of the block, `WTrap.AbsorptionAny` of [Traps001](Traps001.md), is not
refuted.

## Relation to the kit

The kit has no trap for a block of period 6. Its `Rule30EtherThree.PTrap` and `AbsorptionT` are the form of
`WTrap` and `WTrap.Absorption` for period 3, and the kit refutes entry into its own period-four certificates with
explicit right halves (`Rule30Ether.never_enters_S0001`); the refutation here is by a set of windows the kernel checks
closed under predecessors.
