---
title: Refuting entry into a trap from the few windows that can reach it
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ReachRefuted
headline: [pre_move, not_absorption_back, not_absorption_fwd]
kit: new
kit_modules: [Rule30EtherThree, Rule30Ether, Rule30StripCertificates]
evidence: [computations/lock_chain.py]
---

# Refuting entry into a trap from the few windows that can reach it

A trap of [WordTraps](WordTraps.md) reduces its block to entry, `WTrap.Absorption`: every finitely supported right half
driven by the block, from any phase, eventually has its first cells in a state of the trap. Entry needs every node of
the finite game, a phase and a window of $w$ cells, to be able to reach the trap cut to $w$ cells, whatever the cells
beyond do ([what failed](../../negative-results/columns/missed-traps.md)). [MissedTraps](MissedTraps.md) refutes entry
with a closed set of windows apart from the trap, which the kernel checks state by state. Some traps fail the test only
in a game wider than any such set the kernel can hold, and there the nodes that can reach the trap are few. This module
refutes entry with those nodes instead.

## Statement

1. **The old window** (`back`, `pre`, `pre_move`). For a window $r$ of $K \ge 1$ cells, the column's value $c$ and the
   cell beyond $z$, let $v$ be the move of $r$ (the kit's `stripStep`). Then `pre K v` applied to the last cell of $r$
   and to $z$ returns $r$ and $c$.
2. **Sets of windows** (`WinSet`, `WinSet.mem`, `WinSet.mem_spec`). Windows of $K$ cells for a block, by label modulo
   its period, each label's windows packed in increasing order. `mem l w` searches label $l$ for $w$ by halving, and
   `mem_spec` says that when it answers yes, $w$ is a window of the set at label $l$.
3. **Closed under predecessors** (`WinSet.backOK`, `WinSet.check`). For every window $v$ of the set at label $l$, every
   value of the last cell and of the cell beyond, the window `pre` gives is in the set at label $l - 1$ whenever the
   column's value it needs is the block's at that phase.
4. **The refutation** (`not_absorption_back`). Let $C$ be a trap and $S$ a set of windows of $K \le C.K$ cells for its
   block that passes the check, holds every state of $C$ cut to $K$ cells with its label modulo the period
   (`WinSet.holds`), and misses some window $w_0$ at some label $l_0$ (`WinSet.misses`). Then $\lnot\,$`C.Absorption`.
5. **The same with a closed set** (`not_absorption_fwd`). Let $S$ be a closed set of windows for the block of $C$
   (`WTrap.closedCheck` of [MissedTraps](MissedTraps.md)) with at least one state, and $T$ a set of windows of at most
   as many cells as either that holds the states of $C$ cut to it and that no state of $S$, cut to it, meets at the
   label of the same phase (`WinSet.avoids`). Then $\lnot\,$`C.Absorption`. This is `not_absorption` and
   `not_absorption_wide` of MissedTraps with the check of separation done against the few windows that the trap's
   states give when cut, instead of against every state of the trap.

## Argument

The rule is permutive in its left cell: cell $i$ one step later is cell $i - 1$ now, exclusive-or cell $i$ or cell
$i + 1$ now. So the new window, the old last cell and the cell beyond fix the old window from the right, cell by cell,
and at cell 0 the value the column must have. `back` does this from the top bit down, and `back_spec` shows, by
induction on the bit, that it returns the old window and the column's value when the new window is a move (`pre_move`).

Take the right half whose first $K$ cells are $w_0$, white beyond, and drive it by the block from phase $l_0$; call its
window at time $s$ $r_s$, so $r_{s+1}$ is the move of $r_s$ under the column's value at $s$ and cell $K + 1$ at $s$
(`winSeq`, `winSeq_enc`, from the kit's `encF_step`). Suppose it enters $C$ at time $t_1$: its first $C.K$ cells are a
state of $C$ whose label reads the phase of $t_1$. Cut to $K$ cells that state is $r_{t_1}$, and $S$ holds it at the
label of $t_1$ modulo the period. Now go back. If $S$ holds $r_{s+1}$ at the label of $s + 1$, then `pre` applied to
$r_{s+1}$, the last cell of $r_s$ and cell $K + 1$ at $s$ gives $r_s$ and the column's value at $s$, which is the
block's at that label, so the check puts $r_s$ in $S$ at the label of $s$. Down to time 0, $S$ holds $w_0$ at label
$l_0$, which `misses` excludes.

The set is the one the test of reach computes, the nodes from which the trap cut to $K$ cells can be reached
(`reach_nodes` and `back_tables` in [computations/lock_chain.py](../../computations/lock_chain.py)): it holds the cut
states, and every node with a move into it can reach them too. When it is not every node, the window it misses is a
start that never enters. Its complement is a closed set apart from the trap, which `not_absorption_fwd` would take, but
for a trap carried along a background's columns it is the whole game less a few windows, and its least part that no
move leaves still has hundreds of thousands. When instead almost every node can reach the trap, the few that cannot
hold a small closed set (`fwd_tables`), and `not_absorption_fwd` refutes entry with it: the half that starts there
keeps its first cells in it, as in MissedTraps, and at an entry time they would, cut to $T$'s width, be a window of
$T$ at the label of the same phase, which `avoids` excludes.

## The traps

The module checks the method on the census trap of $000001010110101$ of MissedTraps, which MissedTraps refutes with a
closed set of 1,472 states at 8 cells. At 8 cells 123 of the 3,840 nodes of the game can reach it, and
`cen000001010110101_not_absorption_back` refutes entry from them and the white window at phase 0, which they miss.

## Lean

`Rule30Open.Columns.ReachRefuted`: `back`, `pre`, `back_spec`, `pre_move`, `pred_label`; `WinSet` with `cnt`, `win`,
`find`, `mem`, `mem_spec`, `predOK`, `backOK`, `check`, `holds`, `misses`, `avoids`, and the parts lemmas `allRangeT`,
`allRange_cover`, `check_of_labels`, as in [NaturalTrapsLarge](NaturalTrapsLarge.md); `winSeq`, `winSeq_enc`,
`not_absorption_back` and `not_absorption_fwd`. The sets come from `python -m computations.lock_chain --lean-back`
(`REACH_REFUTED`).

## Reproduce

```bash
python -m pytest tests/test_computations.py -k "back_tables or predecessors or reach_wide_carried"
```

The tests compare the set with the moves of the game built cell by cell.
