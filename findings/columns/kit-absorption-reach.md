---
title: The kit's two absorption conjectures pass the test of reach that refutes seven traps found here
category: columns
problems: [1]
status: computed
formalization: not-applicable
evidence: [computations/absorption.py, computations/lock_chain.py, computations/game.py]
---

# The kit's two absorption conjectures pass the test of reach that refutes seven traps found here

The kit reduces the word $001$ to entry into its trap `t001` (`Rule30EtherThreeTrap.AbsorptionT`), and the three words
of period four to entry into the ether-and-wall family (`Rule30Ether.Absorption`). Both are open. Entry into a set of
windows needs every node of the finite game to reach it. The nodes that cannot form a set that no move leaves, whatever
the cell beyond does, and a right half that starts there never enters. That test refutes entry into seven traps of
periods 13 to 15 ([MissedTraps](../../Rule30Open/Columns/MissedTraps.md)). Neither of the kit's conjectures fails it at
any width that can be searched:

- **The family**, for $0001$, $0011$ and $0111$ with the kit's alignments: at every width $w$ from 1 to 23, every node
  of the game of $w$ cells, with the phase modulo 4, can reach a window that is the first $w$ cells of a member. At 23
  cells those windows are 21,123, 87,928 and 112,511 nodes of the 33,554,432.
- **`t001`**, for $001$, with the phase modulo 3 as `AbsorptionT` compares it: at every width from 1 to 24, every node
  of the game can reach the states of `t001` cut to $w$ cells. Columns 1 to 38 of `t001` are functions of the label
  modulo 21, so up to 38 cells the cut trap is 21 windows, one for each label, the columns of the chain that carries
  the trap's lock to the center.

## Method

A member of the family has the ether, aligned with the center, on columns $1, \dots, k$ for some depth $k$ at which
column $k$ is a B3 column, and a wall state of 13 cells after it; columns beyond $k + 13$ are free. Cut to $w$ cells,
the members give, at each phase and alignment, the aligned ether alone when $k \ge w$, and otherwise the ether on
columns $1, \dots, k$ followed by the first $\min(13, w - k)$ cells of a wall state (`family_cut` in
[computations/absorption.py](../../computations/absorption.py), with the kit's 109 wall states computed by
`kit_wall`). `family_reach` takes the nodes of the game from which some values of the cell beyond reach these, by
search backward along the moves (`game.moves`, `locks.back_closure`). For `t001`, `t001_reach` in
[computations/lock_chain.py](../../computations/lock_chain.py) does the same with the kit's 815 states, read from its
source, cut to $w$ cells, each with its label modulo 3.

A test at one width covers every smaller one. If some node of the game of $w$ cells cannot reach the cut set, the
windows of $w' > w$ cells that begin with such a node form a set that no move leaves either, and it contains no window
of $w'$ cells that is the start of a member. So the results are: every node of the game of 23 cells reaches the family,
and every node of the game of 24 cells reaches `t001`. `test_kit_reach` checks that `game.moves` gives the moves of
`game.game_graph`, that `family_cut` holds every window that `family_depth`, on whole rows, puts in the family with a
wall that ends inside it, and the tests at 14 cells.

## What it means

A counterexample to either conjecture of the simplest kind, a right half whose first few cells start in a set of
windows that no move leaves and that misses every member, has to be wider than 23 cells for the family and 24 for
`t001`. For the seven traps of [MissedTraps](../../Rule30Open/Columns/MissedTraps.md) such sets have 7 to 13 cells.
The kit's own single certificates `S0001`, `S0011` and `S0111` are refuted differently, by halves that stay in deeper
members of the family forever (`Rule30Ether.never_enters_S0001` and the two after it), which this test does not see
for the family as a whole, since those halves are inside it. Passing the test is necessary for entry, not sufficient:
whether the true cells beyond the window ever steer a half in is the open question.

## Reproduce

```bash
python -m computations.absorption reach --width 23
```

```bash
python -m computations.lock_chain --t001-reach 24
```

About four minutes and two, most of it at the widest game; the search at 23 cells holds two arrays of 67 million
moves.
