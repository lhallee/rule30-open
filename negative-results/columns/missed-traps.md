---
title: Entry into 277 of the 1,595 traps of the trap modules is false, so their reductions were empty
category: columns
problems: [1]
status: negative
kind: refuted
evidence: [computations/lock_chain.py, computations/locks.py, computations/game.py]
---

# Entry into 277 of the 1,595 traps of the trap modules is false, so their reductions were empty

**Question.** Each trap module reduces a block to entry, the statement that every finitely supported right half driven
by the block eventually enters the trap (`WTrap.Absorption` of [WordTraps](../../Rule30Open/Columns/WordTraps.md)). The
kernel checks that each trap is closed and locked, so each reduction is a theorem. Is each hypothesis one that could be
true?

**What was done.** Entry needs every node of the finite game, a phase and a window, to have some values of the cell
beyond that lead into the trap. The nodes that cannot reach the trap form a set that no move leaves, whatever the cell
beyond does, so a right half that starts in it never enters. The same holds in the game of any width $w$: a node of $w$
cells must be able to reach a window whose first cells form a state of the trap, cut to $w$ cells when the trap is
wider. A failure at one width is a failure at every wider one, so the test only grows stricter with $w$. When the trap
is narrower than $w$, the cells after it follow the rule instead of taking any value, so a trap can pass in the game of
its own width and fail in a wider one. `trap_reach` in [computations/lock_chain.py](../../computations/lock_chain.py)
computes the share of the nodes of the game of $w$ cells that can reach a trap, with the phase counted modulo the
block's period, as `WTrap.Absorption` compares labels. `reach_census` runs it at 20 cells on every trap of the trap
modules (`module_traps`), 1,595 traps, and on the ten pairs of [TrapPairs](../../Rule30Open/Columns/TrapPairs.md)
and [NaturalTrapsWalls](../../Rule30Open/Columns/NaturalTrapsWalls.md), each pair together. For the seven traps of
MissedTraps, and for seven more failing traps of six modules, a half started among the nodes that cannot reach was also
run directly with the rule for 20,000 steps, to check the encoding: each stayed among them and never entered. A second
test asks more of a trap that passes the first: a half of its block's natural scan, the white half or a random one of 64
cells driven by the block, that is inside a closed set apart from the trap at step 12,000 never enters it
(`halves_apart`). `apart_census` runs it on every trap and pair that passes the first test, 1,272 of them in 1,265
blocks, with one scan per block closing windows of 16 to 64 cells.

**Outcome.** At their own width, up to 16 cells, seven traps fail: those of
[MissedTraps](../../Rule30Open/Columns/MissedTraps.md), which proves in Lean that entry into each is false, with a
closed set of windows of 7 to 13 cells apart from the trap. In the game of 20 cells, 247 traps fail. `UNREACHED` in
[computations/lock_chain.py](../../computations/lock_chain.py) lists the 240 of them that are still in the modules:

| Module | Traps | Fail at 20 cells | Their widths | Blocks left with no trap that passes |
|---|---:|---:|---|---:|
| [WordTraps](../../Rule30Open/Columns/WordTraps.md) | 7 | 2 | 19 and 52 | 1 |
| [NineTraps](../../Rule30Open/Columns/NineTraps.md) | 22 | 7 | 53 to 64 | 7 |
| [TenTraps](../../Rule30Open/Columns/TenTraps.md) | 25 | 12 | 19 to 46 | 3 |
| [ElevenTraps](../../Rule30Open/Columns/ElevenTraps.md) | 57 | 27 | 23 to 49 | 14 |
| [TwelveTraps](../../Rule30Open/Columns/TwelveTraps.md) | 83 | 26 | 16 to 56 | 12 |
| [ThirteenTraps](../../Rule30Open/Columns/ThirteenTraps.md) | 53 | 22 | 16 to 69 | 14 |
| [FourteenTraps](../../Rule30Open/Columns/FourteenTraps.md) | 101 | 29 | 32 to 109 | 13 |
| [FarWalls](../../Rule30Open/Columns/FarWalls.md) | 12 | 2 | 57 and 58 | 2 |
| [NaturalTrapsLong](../../Rule30Open/Columns/NaturalTrapsLong.md) | 70 | 2 | 16 | 2 |
| [CensusTraps13](../../Rule30Open/Columns/CensusTraps13.md) | 124 | 25 | 19 to 105 | 22 |
| [CensusTraps14](../../Rule30Open/Columns/CensusTraps14.md) | 232 | 30 | 18 to 104 | 27 |
| [CensusTraps15](../../Rule30Open/Columns/CensusTraps15.md) | 569 | 56 | 16 to 115 | 51 |

The traps of NaturalTraps, NaturalTrapsLarge, NaturalTrapsLongLarge and NaturalTrapsWalls pass, 101 natural traps, as do
the 46 large census components, which are bottom components of 16 cells, and the ten pairs. Of the 240, 235 are carried
traps, a lock carried leftward along the chain of columns of a background, 17 to 115 cells wide; the share of the nodes
that can reach a failing trap ranges from 0.002% to 99.98%. Where the blocks of the five wall modules were left with no
trap that passes, the natural scans give traps that pass for 60 of them, checked in NaturalTrapsWalls; and two walls of
period 15 wider than 16 cells give traps that pass to 5 blocks of CensusTraps15 left so, checked in
[FifteenWalls](../../Rule30Open/Columns/FifteenWalls.md). The blocks left with no trap that passes number 168: one of
period 2, $01$, and 7, 3, 14, 14, 38, 40 and 51 of periods 9 to 15. For $001$ the kit's `t001` still passes, at every
width up to 26 ([reach of the kit's conjectures](../../findings/columns/kit-absorption-reach.md)), but the second
trap for $001$ of WordTraps, 52 cells wide, is a closed set apart from it, so entry into `t001` alone is false
([Traps001](../../Rule30Open/Columns/Traps001.md)).

The second test refutes 28 more traps, and one pair, that pass the first (`APART`): 2 of ElevenTraps, 1 of
TwelveTraps, 6 of ThirteenTraps, 2 of FourteenTraps, 1 of NaturalTrapsLong, 1 each of CensusTraps13 and CensusTraps14,
14 of CensusTraps15, and the pair of $0001101101011$ in TrapPairs. For 18 of their blocks no half that the scan finds
in a trap is in the module's: the halves settle into closed sets of 21 to 42 cells that the module's trap, a carried
wall or a census component, is apart from. For each of the 29 blocks the block's traps and the natural traps its halves
are inside together pass the test of reach at 20 cells, and [TrapSets](../../Rule30Open/Columns/TrapSets.md) reduces
the block to entry into one of them, so the count of blocks left with no trap that passes stays 168.

The test only grows stricter with the width. In the game of 22 cells, of the 252 hypotheses that pass both tests at
20 cells and are not carried along a chain, the natural traps, the large census components, the pairs and the sets,
three fail, with 99.984% to 99.994% of the nodes able to reach (`wide_reach`, `UNREACHED_WIDE`): the pair of
$00101101111$ in NaturalTrapsWalls, and the natural traps of 16 cells of $0010011110101$ in NaturalTrapsWalls and
$0101011111111$ in [NaturalTrapsLongLarge](../../Rule30Open/Columns/NaturalTrapsLongLarge.md). Their three blocks are
left with no hypothesis that passes, which makes 171.

**Where it stops, and why.** Four different failures.

- *A carried trap fixes the columns to the wall.* A trap carried $d$ columns from a wall, or from a census component,
  has its first $d$ cells fixed to the background's columns between the block and the wall, as functions of the phase.
  Entry asks the half to rebuild those columns exactly, and in the game of 20 cells it asks the first 20 cells to
  become them. For the traps that fail, some windows can never do that, whatever arrives from the right. Small halves
  do enter some of these traps, as the entry censuses of the modules record, but not every half can.
- *A trap that passes at its own width fails in a wider game.* In the game of its own width a trap's cell beyond takes
  any value; in a wider game it follows the rule from the cells after it, and some windows can no longer be steered
  in. Seven traps of 16 to 19 cells pass at their own width and fail at 20 cells, with 98.02% to 99.98% of the nodes
  able to reach: two walls themselves, $000010011111$ of period 12 and $0001110010011$ of period 13; the wall of period
  10 carried 3 columns, to $0001010111$; a census component of period 15 and one carried 2 columns at period 14; and
  the natural traps of $0001111110011$ and $0010011010111$ in NaturalTrapsLong. The natural trap of $0001111110011$
  already fails in the game of 17 cells, with 98.65%.
- *Two traps where one was taken.* Each of the four natural blocks of MissedTraps has two bottom components of locked
  windows of 16 cells, with different values of column 1 at the white phases. The natural scan's own sampled halves
  split between them: driven by $0001101101011$, the 31 halves end in the trap of 430 states or in one of 616, and for
  $0010101111111$ in one of 1,196 or one of 13,159 states. The module took the smaller. Every node can reach one of the
  two, so entry into one of two traps is still a hypothesis that could hold, and TrapPairs reduces the four blocks to
  it. Six more blocks split the same way between two natural traps apart from each other, $0001010111$,
  $00101101111$, $000000101101$, $000010011111$, $0000001111111$ and $00101101101101$, and NaturalTrapsWalls reduces
  them to entry into one of the two. For three of them only the halves show it: the natural traps of 17, 16 and 16
  cells of $000000101101$, $0000001111111$ and $00101101101101$ pass the test at 20 cells, but 3, 4 and 1 of the scan's
  31 halves are inside closed sets of 26, 25 and 32 cells apart from them.
- *No lock in reach.* For the three census blocks of MissedTraps no locked node of the game of 16 cells can be reached
  from the white window at all. No trap of 16 cells with the phase counted modulo the period can be entered by the
  white right half. Neither wider windows nor longer label cycles change this: at 17 and 18 cells, and at 16 cells with
  the phase counted modulo twice or three times the period, the white window still reaches no locked node, and the
  nodes that can reach one are 0.56% to 2.52% of the game (`python -m computations.locks --reach <block> --width 18`,
  or `--repeat 2`). The census components carried to these blocks one or two columns fail the same way.

**What it means.** For 171 blocks every reduction is a true theorem with a false hypothesis, and [the coverage
table](../../findings/columns/coverage.md) now counts a block as reduced only when one of its traps passes the test at
20 cells. The test is a probabilistic one, that of [the coin beyond the window](../../findings/columns/coin-lock.md): a
trap passes at $w$ cells exactly when, with a fair coin in column $w + 1$, every window of $w$ cells reaches it with
probability 1, since in the finite game a node that can reach it does so with a chance bounded below within a bounded
time, and a node that cannot never does. Each refuted trap is a counterexample of that kind, a set of windows the coin
never brings in, and each half apart is one that the true rule supplies. The test is necessary, not sufficient, and
stricter at every larger width: traps that pass at their own width fail at 20 cells, so wider games would likely refute
more traps, natural ones among them. The kit met the same failure for its period-four certificates `S0001`, `S0011` and
`S0111` (`Rule30Ether.never_enters_S0001` and the two after it) and states its absorption conjecture for the whole
ether-and-wall family instead of one certificate; that family, and the kit's `t001`, pass the test at 26 cells, and
`t001` fails it by 52 cells, where the second trap for $001$ fits. Of the refutations here 119 are checked in Lean: the
seven of MissedTraps, 102 of the 240, with closed sets of 2 to 17 cells
([RefutedTraps](../../Rule30Open/Columns/RefutedTraps.md)), and the ten single traps of five pairs of NaturalTrapsWalls;
`not_absorption` and `not_absorption_wide` of MissedTraps would check any of the others, given a closed set apart from
the trap (`miss_tables`).

**Reproduce.**

```bash
python -m computations.lock_chain --reach 20
```

```bash
python -m computations.lock_chain --halves-apart
```

```bash
python -m computations.lock_chain --apart-census 3
```

```bash
python -m computations.lock_chain --wide-reach 2
```

The census of every trap in the game of 20 cells, about four hours with one process; the halves of the natural scans
in traps apart from those of NaturalTrapsWalls, about ten minutes; and from every trap and pair that passes the test of
reach, about an hour with three processes; and the test in the game of 22 cells, about two and a half hours with two.
