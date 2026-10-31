---
title: Entry into 240 of the 1,459 traps of the trap modules is false, so their reductions were empty
category: columns
problems: [1]
status: negative
kind: refuted
evidence: [computations/lock_chain.py, computations/locks.py, computations/game.py]
---

# Entry into 240 of the 1,459 traps of the trap modules is false, so their reductions were empty

**Question.** Each trap module reduces a block to entry, the statement that every finitely supported right half driven
by the block eventually enters the trap (`WTrap.Absorption` of [WordTraps](../../Rule30Open/Columns/WordTraps.md)). The
kernel checks that each trap is closed and locked, so each reduction is a theorem. Is each hypothesis one that could be
true?

**What was done.** Entry needs every node of the finite game, a phase and a window, to have some values of the cell
beyond that lead into the trap. The nodes that cannot reach the trap form a set that no move leaves, whatever the cell
beyond does, so a right half that starts in it never enters. The same holds with the trap cut to its first $w$ cells and
the game of $w$ cells, for any $w$ up to the trap's width: a half whose first $w$ cells start among the nodes that cannot
reach the cut states keeps them there, and so never has its first cells in a state of the trap. A failure at one width
is a failure at every wider one, so the test only grows stricter with $w$. `trap_reach` in
[computations/lock_chain.py](../../computations/lock_chain.py) computes the share of the nodes of the game of $w$ cells
that can reach a trap cut to $w$ cells, with the phase counted modulo the block's period, as `WTrap.Absorption` compares
labels. `reach_census` runs it on every trap of the trap modules (`module_traps`), 1,455 traps, and on the four pairs of
[TrapPairs](../../Rule30Open/Columns/TrapPairs.md). For the seven traps of MissedTraps, and for seven more failing traps
of six modules, a half started among the nodes that cannot reach was also run directly with the rule for 20,000 steps,
to check the encoding: each stayed among them and never entered.

**Outcome.** At their own width, up to 16 cells, seven traps fail: those of
[MissedTraps](../../Rule30Open/Columns/MissedTraps.md), which proves in Lean that entry into each is false, with a closed
set of windows of 7 to 13 cells apart from the trap. Cut to 18 cells, 211 traps and pairs fail; cut to 20 cells, 240.
`UNREACHED` in [computations/lock_chain.py](../../computations/lock_chain.py) lists the 233 of them that are still in the
modules:

| Module | Traps | Fail at 20 cells | Their widths | Blocks left with no trap that passes |
|---|---:|---:|---|---:|
| [WordTraps](../../Rule30Open/Columns/WordTraps.md) | 7 | 2 | 19 and 52 | 1 |
| [NineTraps](../../Rule30Open/Columns/NineTraps.md) | 22 | 7 | 53 to 64 | 7 |
| [TenTraps](../../Rule30Open/Columns/TenTraps.md) | 25 | 11 | 26 to 46 | 11 |
| [ElevenTraps](../../Rule30Open/Columns/ElevenTraps.md) | 57 | 27 | 23 to 49 | 27 |
| [TwelveTraps](../../Rule30Open/Columns/TwelveTraps.md) | 83 | 25 | 20 to 56 | 25 |
| [ThirteenTraps](../../Rule30Open/Columns/ThirteenTraps.md) | 53 | 21 | 17 to 69 | 21 |
| [FourteenTraps](../../Rule30Open/Columns/FourteenTraps.md) | 101 | 29 | 32 to 109 | 29 |
| [FarWalls](../../Rule30Open/Columns/FarWalls.md) | 12 | 2 | 57 and 58 | 2 |
| [CensusTraps13](../../Rule30Open/Columns/CensusTraps13.md) | 124 | 25 | 19 to 105 | 22 |
| [CensusTraps14](../../Rule30Open/Columns/CensusTraps14.md) | 232 | 29 | 18 to 104 | 26 |
| [CensusTraps15](../../Rule30Open/Columns/CensusTraps15.md) | 569 | 55 | 18 to 115 | 55 |

Every natural trap passes, the closed sets that sampled halves settle into (NaturalTraps, NaturalTrapsLarge,
NaturalTrapsLong and NaturalTrapsLongLarge, 117 traps), as do the 46 large census components, which are bottom
components of 16 cells, and the four pairs. Each of the 233 is a carried trap, a lock carried leftward along the chain
of columns of a background, 17 to 115 cells wide; the share of the nodes that can reach it ranges from 0.002% to
99.96%. The blocks left with no trap that passes number 226: one of period 2, $01$, and 7, 11, 27, 27, 43, 55 and 55 of
periods 9 to 15. For $001$ the kit's `t001` still passes, at every width up to 24 ([reach of the kit's
conjectures](../../findings/columns/kit-absorption-reach.md)).

**Where it stops, and why.** Three different failures.

- *A carried trap fixes the columns to the wall.* A trap carried $d$ columns from a wall, or from a census component,
  has its first $d$ cells fixed to the background's columns between the block and the wall, as functions of the phase.
  Entry asks the half to rebuild those columns exactly, and cut to 20 cells it asks the first 20 cells to become them.
  For the traps that fail, some windows can never do that, whatever arrives from the right. Small halves do enter some
  of these traps, as the entry censuses of the modules record, but not every half can.
- *Two traps where one was taken.* Each of the four natural blocks of MissedTraps has two bottom components of locked
  windows of 16 cells, with different values of column 1 at the white phases. The natural scan's own sampled halves
  split between them: driven by $0001101101011$, the 31 halves end in the trap of 430 states or in one of 616, and for
  $0010101111111$ in one of 1,196 or one of 13,159 states. The module took the smaller. Every node can reach one of the
  two, so entry into one of two traps is still a hypothesis that could hold, and the four blocks are reduced to it.
- *No lock in reach.* For the three census blocks of MissedTraps no locked node of the game of 16 cells can be reached
  from the white window at all. No trap of 16 cells with the phase counted modulo the period can be entered by the
  white right half. Neither wider windows nor longer label cycles change this: at 17 and 18 cells, and at 16 cells with
  the phase counted modulo twice or three times the period, the white window still reaches no locked node, and the
  nodes that can reach one are 0.56% to 2.52% of the game (`python -m computations.locks --reach <block> --width 18`,
  or `--repeat 2`). The census components carried to these blocks one or two columns fail the same way.

**What it means.** The reductions of 226 blocks were true theorems with false hypotheses, and [the coverage
table](../../findings/columns/coverage.md) now counts a block as reduced only when one of its traps passes the test at
20 cells. The test is necessary, not sufficient, and stricter at every larger width: 29 traps that pass at 18 cells
fail at 20, so wider games would likely refute more of the carried traps, while the natural traps pass at every width
tried. The kit met the same failure for its period-four certificates `S0001`, `S0011` and `S0111`
(`Rule30Ether.never_enters_S0001` and the two after it) and states its absorption conjecture for the whole
ether-and-wall family instead of one certificate; that family, and the kit's `t001`, pass the test at 23 and 24 cells.
Of the refutations here only the seven of MissedTraps are checked in Lean; its `not_absorption` would check any of the
others, given a closed set apart from the trap (`miss_tables`).

**Reproduce.**

```bash
python -m computations.lock_chain --reach 20
```

About three hours with one process; `--reach 18` takes about forty minutes.
