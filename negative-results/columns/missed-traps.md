---
title: Entry into seven checked traps of periods 13 to 15 is false, so their reductions were empty
category: columns
problems: [1]
status: negative
kind: refuted
evidence: [computations/lock_chain.py]
---

# Entry into seven checked traps of periods 13 to 15 is false, so their reductions were empty

**Question.** Each trap module reduces a block to entry, the statement that every finitely supported right half driven
by the block eventually enters the trap (`WTrap.Absorption` of [WordTraps](../../Rule30Open/Columns/WordTraps.md)). The
kernel checks that each trap is closed and locked, so each reduction is a theorem. Is each hypothesis one that could be
true?

**What was done.** Entry needs every node of the finite game, a phase and a window, to have some values of the cell
beyond that lead into the trap. The nodes that cannot reach the trap form a set that no move leaves, whatever the cell
beyond does, so a right half that starts in it never enters. `trap_reach` in
[computations/lock_chain.py](../../computations/lock_chain.py) computes the share of the nodes that can reach a trap.
`reach_census` runs it on every trap of the trap modules that is at most 16 cells wide and labels the phase modulo the
period: the walls and their carried traps within reach, the natural traps, and the census traps. A half started in the
unreachable set was also run directly with the rule for 20,000 steps, to check the encoding: it stayed in the set and
never entered.

**Outcome.** Of the 228 traps, 221 can be reached from every node. Seven cannot:

| block | trap module | states | nodes that can reach it |
|---|---|---|---|
| $0001101101011$ | NaturalTrapsLong | 430 | 95.35% |
| $0010010010111$ | NaturalTrapsLong | 423 | 92.09% |
| $0010101111111$ | NaturalTrapsLong | 1,196 | 34.58% |
| $00001101111001$ | NaturalTrapsLong | 428 | 95.62% |
| $0000010111001$ | CensusTraps13 | 162 | 0.81% |
| $000001010110101$ | CensusTraps15 | 186 | 0.61% |
| $001001111010111$ | CensusTraps15 | 135 | 2.52% |

[MissedTraps](../../Rule30Open/Columns/MissedTraps.md) proves in Lean that entry into each of the seven is false, with
a closed set of windows of 7 to 13 cells apart from the trap, which the kernel checks. The seven are out of the trap
modules. [TrapPairs](../../Rule30Open/Columns/TrapPairs.md) reduces the four natural blocks again, to entry into one of
two traps; the three census blocks are out of the count of blocks reduced to entry
([the coverage table](../../findings/columns/coverage.md)).

**Where it stops, and why.** Two different failures.

- *Two traps where one was taken.* Each of the four natural blocks has two bottom components of locked windows of 16
  cells, with different values of column 1 at the white phases. The natural scan's own sampled halves split between
  them: driven by $0001101101011$, the 31 halves end in the trap of 430 states or in one of 616, and for $0010101111111$
  in one of 1,196 or one of 13,159 states. The module took the smaller. Every node can reach one of the two, so entry
  into one of two traps is still a hypothesis that could hold, and the four blocks are reduced to it.
- *No lock in reach.* For the three census blocks no locked node of the game of 16 cells can be reached from the white
  window at all. No trap of 16 cells with the phase counted modulo the period can be entered by the white right half.

**What it means.** The test is cheap and necessary, and every trap of at most 16 cells left in the trap modules passes
it. It is not sufficient: those 221 traps still need entry proved. It also cannot reach the carried traps wider than
about 18 cells, whose games are too large to search; entry into those rests on samples of small halves only. The kit
met the same failure for its period-four certificates `S0001`, `S0011` and `S0111` (`Rule30Ether.never_enters_S0001`
and the two after it) and states its absorption conjecture for the whole ether-and-wall family instead of one
certificate.
