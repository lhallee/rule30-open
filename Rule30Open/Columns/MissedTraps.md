---
title: Seven checked traps of periods 13 to 15 that some finitely supported right half never enters
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.MissedTraps
headline: [not_absorption, missedTraps_check, missedTraps_not_absorption]
kit: new
kit_modules: [Rule30EtherThree, Rule30Ether]
evidence: [computations/lock_chain.py]
---

# Seven checked traps of periods 13 to 15 that some finitely supported right half never enters

A trap of [WordTraps](WordTraps.md) reduces its block to entry, `WTrap.Absorption`: every finitely supported right
half driven by the block, from any phase, eventually has its first cells in a state of the trap. Entry fails whenever
some node of the finite game cannot reach the trap. The nodes that cannot form a set that no move leaves, whatever the
cell beyond the window does, and a right half that starts there stays there. Checking every trap of at most 16 cells in
the trap modules this way (`trap_reach`) finds seven, of 228, that some node cannot reach at their own width. This
module checks each of the seven as a trap and refutes entry into it, so their reductions held only because their
hypothesis was false. The trap modules no longer list them. Cut to their first 20 cells, 233 wider traps that the
modules still hold fail the same test ([what failed](../../negative-results/columns/missed-traps.md)), and
`not_absorption` applies to each of them as well, given a closed set apart from it.

| block | trap from | states | nodes of the 16-cell game that can reach it | cut width | closed set |
|---|---|---|---|---|---|
| $0001101101011$ | the natural scan | 430 | 95.35% | 13 | 128 states |
| $0010010010111$ | the natural scan | 423 | 92.09% | 13 | 137 states |
| $0010101111111$ | the natural scan | 1,196 | 34.58% | 7 | 142 states |
| $00001101111001$ | the natural scan | 428 | 95.62% | 13 | 174 states |
| $0000010111001$ | the census of locked windows | 162 | 0.81% | 9 | 1,014 states |
| $000001010110101$ | the census of locked windows | 186 | 0.61% | 8 | 1,472 states |
| $001001111010111$ | the census of locked windows | 135 | 2.52% | 10 | 2,446 states |

## Statement

1. **Closed sets** (`WTrap.closedCheck`, `WTrap.apart`). A `WTrap` passes `closedCheck` when its labels count the phase
   modulo a multiple of the period and the move of every state, under either value of the cell beyond, is a state with
   the next label. Nothing is asked of the first cell, so a closed set need not be locked. `S.apart C` says that no
   state of `C`, cut to its first `S.K` cells, is a state of `S` whose label reads the same phase of the block.
2. **The refutation** (`not_absorption`). Let $C$ be a trap and $S$ a closed set for the same block, with
   $S.K \le C.K$, $S$ apart from $C$, and at least one state. Then $\lnot\,$`C.Absorption`.
3. **The traps** (`missedTraps`, `missedTraps_check`, `missedTraps_blocks`). Seven labelled traps `WTrap` of 16 cells,
   with labels modulo the period, each passing the check of [WordTraps](WordTraps.md): the natural traps of
   $0001101101011$, $0010010010111$, $0010101111111$ (period 13) and $00001101111001$ (period 14), and the census
   traps of $0000010111001$ (period 13), $000001010110101$ and $001001111010111$ (period 15).
4. **Entry into each fails** (`missedTraps_not_absorption`, and `<trap>_not_absorption` for each). For every trap of
   the list, some finitely supported right half driven by its block, from some phase, never enters it.

## Argument

Let $S$ be closed and apart from $C$, with $w = S.K$ cells. Take the right half $x$ whose cells $1, \dots, w$ are the
window of state $0$ of $S$, white beyond, and drive it by the block from the phase $\varphi$ that the label of that
state reads. At time 0 its first $w$ cells are that state. Suppose at time $s$ they are a state $j$ of $S$ whose label
reads the phase of time $s$. One step later they are the move of that window under the block's cell at that phase and
whatever value cell $w + 1$ has (the kit's `encF_step` on the driven half `drv`). Closure says this move is a state of
$S$ with the next label. So at every time the first $w$ cells are a state of $S$ with the right label.

Now suppose entry: at some time $t_1$ the first $C.K$ cells are a state $i$ of $C$ whose label reads the phase of
$t_1$. Cut to $w$ cells, that state is the window of the state of $S$ at $t_1$, since both describe cells $1, \dots, w$
at $t_1$, and the two labels read the same phase. This is a pair that `apart` excludes, so entry fails for $x$ and
$\varphi$. `not_absorption` is this argument; the kernel checks closure and separation for each of the seven sets.

Each set comes from the game (`miss_tables` in [computations/lock_chain.py](../../computations/lock_chain.py)). Cut the
trap's states to their first $w$ cells, for $w = 1, 2, \dots$, and take the least $w$ at which some node of the game of
$w$ cells cannot reach the cut states. Those nodes form a set that no move leaves, and the set takes the least strongly
connected component among them that no move leaves. Cutting first keeps the sets small, of 128 to 2,446 states, where
at 16 cells the nodes that cannot reach the trap of $0000010111001$ are 99.19% of the 851,968.

## What it means

The seven reductions to entry were true and empty: their hypothesis is false.

The four natural traps fail for a reason that a larger reduction avoids. Each of their blocks has two bottom
components of locked windows of 16 cells, with different values of column 1 at the white phases, and the natural trap
is one of them. Neither is reachable from every node, but every node reaches a locked node, so every node reaches one
of the two: entry into one of two traps passes the test that entry into either alone fails, and
[TrapPairs](TrapPairs.md) reduces the four blocks to it. The census traps of the other three fail for good at this
width: from the white window no locked node of 16 cells can be reached at all (`locks.lock_info`), so no trap of 16
cells with labels modulo the period can be entered by the white right half.

The test is necessary, not sufficient: the traps that pass it still need entry proved. Cut to 20 cells it refutes 233
more traps of the modules, all carried ones, while every natural trap passes
([what failed](../../negative-results/columns/missed-traps.md)).

## Relation to the kit

The kit refutes entry into each of its own period-four certificates `S0001`, `S0011` and `S0111`
(`Rule30Ether.never_enters_S0001`, `never_enters_S0011`, `never_enters_S0111`): an explicit finite right half stays in
deeper members of the ether-and-wall family forever. This is why its `Absorption` asks for entry into the whole family.
Here the same failure is found for traps of periods 13 to 15 by a general test, and refuted with a closed set that the
kernel checks, in the form of the kit's `AbsorptionT`. The kit's family and its `t001` pass the same test at every width
searched, 23 and 24 cells ([reach of the kit's conjectures](../../findings/columns/kit-absorption-reach.md)).

## Lean

`Rule30Open.Columns.MissedTraps`: `WTrap.closedOK`, `WTrap.closedCheck`, `WTrap.apart`, `not_absorption`; the traps
`nat<block>` and `cen<block>` with `_check`, the closed sets `miss<block>` with `_closed` and `_apart`, and
`<trap>_not_absorption`; the list `missedTraps` with `missedTraps_check`, `missedTraps_blocks` and
`missedTraps_not_absorption`. The tables come from `python -m computations.lock_chain --lean-missed`. The kernel checks
the module in about 90 seconds.

## Reproduce

```bash
python -m computations.lock_chain --reach 16
```

The test of every trap of at most 16 cells in the trap modules, about an hour; before the seven were taken out it
reported each of them, with the share of the nodes that can reach it.
