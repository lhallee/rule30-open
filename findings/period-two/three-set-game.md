---
title: Beside an alternating center every state of the double-step game of up to 26 cells can reach the three closed sets, and from 61% of the states of 22 cells every play enters them
category: period-two
problems: [1]
status: computed
formalization: not-applicable
evidence: [computations/three_set_game.py, computations/gate_census.py, computations/absorption.py]
---

# Beside an alternating center every state of the double-step game of up to 26 cells can reach the three closed sets, and from 61% of the states of 22 cells every play enters them

Beside an alternating center every right half of up to 20 cells enters one of three closed sets: the gap trap, the
kit's ether-and-wall family for $0101$, or the lock of period seven ([the census](gate-census.md)). Period two then
splits into a statement about the right half, that every finite right half enters one of the three, and the kit's
open `Q01Gap`. This entry tests the right statement in the finite game of the windows, at every width from 10 to 26
cells, with the cells beyond the window free:

1. **Reach.** At every width from 10 to 26, every state of the game can reach the three sets, cut to the window. So
   no set of windows that the rule never leaves, whatever the cells beyond do, avoids them, and the simplest kind of
   counterexample to the right statement, a half that starts in such a set, needs more than 26 cells. This is the test
   that refutes entry into seven traps of 16 cells, at cut widths of 7 to 13
   ([MissedTraps](../../Rule30Open/Columns/MissedTraps.md)), and that the kit's family passes to 26 cells for the words
   of period four ([the kit's family](../columns/kit-absorption-reach.md)).
2. **The forced basin.** The states from which every play enters the three sets, with each set certified inside the
   window, are 35.3% of the states at 16 cells and 60.5% at 22, and 31.8% to 57.3% of the windows that a half shows at
   its first white step. Outside the forced basin, the plays that avoid the three sets forever end in at most three
   components, of 2,695 to 15,322 states in all; column 1 is not locked on the large ones, and one of them holds the
   aligned ether at every width; [the residue](../../negative-results/period-two/game-residue.md) shows why no width
   closes that gap.

## The game

A state at width $W$ is a window of columns $1, \dots, W$ at a white step of the center, with the count $d$ of white
steps since the last black cell of column 1: $d = 0$ when column 1 is black, $1$ to $4$ when it is white ($4$ meaning
four or more), and $5$ when column 1 has not been black yet. A state is consistent when $d = 0$ exactly when column 1
is black, so there are $3 \cdot 2^W$ consistent states. A move is a double step, the center white and then black, for
one of the four values of column $W + 1$ at the two steps. The game is the same in both phases of the center: the
phase only decides which window a half shows at its first white step. In phase 1 (the center black at the odd steps)
that is the half's own first $W$ cells, so every window; in phase 0 it is their image under one black step, weighted
here by the window and the cell beyond it.

The three sets, as states of the game:

- **The gap trap** (`gate_census.gap_states`): the pairs of a window of 16 columns and a count that are good, that is,
  every play from them has the black cells of column 1 come 3 or 5 white steps apart. A half enters when its window is
  black in column 1 and good with count 0 (`gate_census.gap_entry`, 3,562 windows).
- **The kit's family** (`Rule30Ether.InFamily` for $0101$ with the alignments $(3, 0)$ and $(3, 2)$): the ether on
  columns $1, \dots, k$ and one of the kit's 109 wall states on columns $k + 1, \dots, k + 13$, with $k = 6, 13, 20,
  \dots$. Membership at the two white phases of the drive is the same, since the two alignments differ by two steps.
- **The lock of period seven**: 195 windows of 32 columns ([SevenLock](../../Rule30Open/PeriodTwo/SevenLock.md)).

## The test of reach

Here the targets are taken as large as the window allows, so that a closed set that avoids them would be a sound
refutation: a state is a target if it could be the cut to $W$ cells of a good state of the gap trap with the same
count (for $W \ge 16$ its first 16 columns are good), if its window is the cut of a member of the family at any depth,
including the aligned ether alone when the wall lies beyond the window (`absorption.family_cut`), or if its window is
the cut of a window of the lock, of any class. `reach` adds, sweep by sweep, every state with some move into what it
has found. The states it never adds would form a closed set that avoids the targets.

| $W$ | consistent states | targets | gap trap | family | lock | cannot reach the three | sweeps | cannot reach the gap trap | sweeps |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 10 | 3,072 | 811 | 769 | 18 | 27 | 0 | 11 | 0 | 18 |
| 12 | 12,288 | 2,686 | 2,641 | 18 | 27 | 0 | 15 | 0 | 22 |
| 14 | 49,152 | 8,827 | 8,782 | 18 | 27 | 0 | 20 | 0 | 26 |
| 16 | 196,608 | 29,866 | 29,797 | 42 | 27 | 0 | 24 | 0 | 34 |
| 18 | 786,432 | 119,322 | 119,188 | 107 | 27 | 0 | 32 | 0 | 38 |
| 19 | 1,572,864 | 238,578 | 238,376 | 175 | 27 | 0 | 34 | 5,931 | 43 |
| 20 | 3,145,728 | 477,111 | 476,752 | 332 | 27 | 0 | 38 | 17,601 | 46 |
| 22 | 12,582,912 | 1,908,326 | 1,907,008 | 1,291 | 27 | 0 | 43 | 111,247 | 55 |
| 24 | 50,331,648 | 7,633,154 | 7,628,032 | 5,095 | 27 | 0 | 47 | 646,403 | 63 |
| 26 | 201,326,592 | 30,532,442 | 30,512,128 | 20,271 | 43 | 0 | 54 | 3,229,386 | 65 |

The columns of the targets count consistent states, and the gap trap and the family overlap. A test at one width
covers every smaller one: the cut of a move is a move, and the cut of a target is a target, so a state of $W$ cells
that cannot reach the targets would extend to states of $W' > W$ cells that cannot reach them either.

The gap trap alone does not suffice from 19 cells on, and what it misses is exactly the family's share: at 19, 20, 21
and 22 cells the 5,931, 17,601, 45,221 and 111,247 states from which no play reaches the gap trap are, state for
state, the forced basin of the family below (and at 16 and 18 cells both are empty). So every play from a state that
cannot reach the gap trap enters the family.

## The forced basin

Here the targets are taken as small as entry needs, so that every play from a state of the basin really enters: the
gap trap's 3,562 entry windows at count 0 (from $W = 16$), the members of the family whose wall ends inside the window
($k + 13 \le W$, so none below 19 cells), and no state of the lock, which needs 32 columns. `forced_basin` adds,
sweep by sweep, every state all four of whose moves land in what it has found; the rank of a state is the sweep that
adds it. The shares of the starts are of the states a half shows at its first white step, with count 0 when column 1
is black and 5 otherwise.

| $W$ | target | basin | share of states | starts, phase 1 | starts, phase 0 | largest rank |
|---:|---:|---:|---:|---:|---:|---:|
| 16 | 3,562 | 69,436 | 0.3532 | 0.3184 | 0.3583 | 14 |
| 17 | 7,124 | 156,833 | 0.3988 | 0.3633 | 0.4041 | 18 |
| 18 | 14,248 | 348,064 | 0.4426 | 0.4070 | 0.4479 | 20 |
| 19 | 28,653 | 769,797 | 0.4894 | 0.4546 | 0.4949 | 22 |
| 20 | 57,306 | 1,672,015 | 0.5315 | 0.4970 | 0.5360 | 33 |
| 21 | 114,612 | 3,578,738 | 0.5688 | 0.5354 | 0.5722 | 39 |
| 22 | 229,224 | 7,617,642 | 0.6054 | 0.5732 | 0.6075 | 39 |

The part that excludes period two outright, the family and the lock without the gap trap, has an empty target below
19 cells, and its basin is small where it exists:

| $W$ | target | basin | share of states | starts, phase 1 | starts, phase 0 | largest rank |
|---:|---:|---:|---:|---:|---:|---:|
| 19 | 157 | 5,931 | 0.0038 | 0.0044 | 0.0044 | 14 |
| 20 | 314 | 17,601 | 0.0056 | 0.0064 | 0.0063 | 17 |
| 21 | 628 | 45,221 | 0.0072 | 0.0082 | 0.0079 | 19 |
| 22 | 1,256 | 111,247 | 0.0088 | 0.0100 | 0.0095 | 20 |

The share of the three sets grows by about four points per cell from 16 to 22 cells, and the largest rank stays below
40. Every play from a state of rank $r$ enters within $r$ double steps, so a half whose window ever lies in the basin
of 22 cells enters within 39 further double steps, whatever its cells beyond the window.

## Spatially periodic halves

`run_periodic` drives every right half that repeats a primitive word of period at most 12 (8,032 halves) and 100
random words of each period from 13 to 32, in both phases, for 10,000 double steps, and records the first white step
at which the half is exactly in one of the three sets (its first 16 columns an entry window of the gap trap, its first
64 a member of the family by `absorption.family_depth`, or its first 32 a window of the lock). Of the 10,032 halves
in each phase, all enter by step 2,437 except two, the aligned ether at its two white phases ($0000010$ and $1001100$
repeated, cell 1 first, and one step earlier in phase 0), which the rule keeps with period four in time and which
never enters any of the three sets. Its states lie outside the forced basin at every width from 16 to 22, in a
component of the residue on which column 1 is not locked.

## What it means

The test of reach is necessary for the right statement, not sufficient. The right statement passes it, as the kit's
family passes it for the words of period four, and the counterexample it would detect has to be wider than 26 cells.
The forced basin is the other side: a half whose first 22 cells lie in it, about three windows in five, is proved to
enter whatever lies beyond. It does not reach every window at any width, and
[the residue](../../negative-results/period-two/game-residue.md) gives the reason: the deep members of the family keep
the aligned ether on every window narrower than their depth, so their windows never certify entry.

## Reproduce

```bash
python -m computations.three_set_game reach --widths 10 12 14 16 18 19 20 22 24 26   # about 6 min, 2.1 GB at 26
python -m computations.three_set_game basin --widths 16 17 18 19 20 21 22   # about 30 s, 1 GB at 22
python -m computations.three_set_game halves --period 12 --random 100 --max-period 32 --double-steps 10000 --widths 16 18 20 22   # about 1 min
```

`tests/test_three_set_game.py` checks the moves against direct runs of Python integers at 6 and 10 cells; at 8 cells
the forced basin, the rank of every state and the states that can reach a target against an iteration and a listing
of plays written with its own double step and count; that every state of a component of the residue has a move that
stays in it; the family's targets against `absorption.family_depth` on rows and `absorption.family_cut`; and that the
aligned ether never enters while the white half enters the gap trap at step 293, as in the kit's `u_empty_gaps`.
