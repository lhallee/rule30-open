---
title: Every background of Rule 30 periodic in time, to period 14, and the traps at their edges
category: columns
problems: [1]
status: computed
formalization: partial
evidence: [computations/space_time_periodic.py, computations/lock_chain.py]
---

# Every background of Rule 30 periodic in time, to period 14, and the traps at their edges

A background of period $P$ is a configuration of Rule 30 on the whole line in which every column repeats with a period
dividing $P$. Column $j - 1$ is a function of columns $j$ and $j + 1$, so the pairs of adjacent columns, read leftward,
follow one map on the $4^P$ pairs of words of length $P$ (`column_map` in
[computations/space_time_periodic.py](../../computations/space_time_periodic.py), the `left_column` of
[lock chains](lock-chains.md)). A background is a chain of the map infinite both ways, and on a finite set such a chain
lies on the map's cycles: every background is periodic in space, its spatial period the length of its cycle, and every
cycle is a background. Repeated squaring of the map finds all its cycles, so for each period the list below is
complete. The kit proves the first part in Lean, in its equivalent forms: every configuration $x$ with $F^k x = x$ is
periodic in space with period $(4^k)!$ (`evol_add_factorial` in `Rule30Equivalents.PeriodicPoints`), at most $4^k$
configurations satisfy it (`ncard_recurs_le`), and exactly three are fixed (`evol_one_eq_self_iff`). The list, the
walls and the witnesses below are computed here; the traps of the walls of periods 9 to 14 are checked in Lean.

## Result

| Period | Backgrounds | Of exactly this period, by spatial period | Blocks among their columns |
|---:|---:|---|---:|
| 1 | 2 | 1, 2 | 2 of 2 |
| 2 | 2 | none | 0 of 1 |
| 3 | 3 | 12 | 2 of 2 |
| 4 | 3 | 7 | 3 of 3 |
| 5 | 5 | 5, 15, 25 | 6 of 6 |
| 6 | 4 | 84 | 9 of 9 |
| 7 | 3 | 15 | 13 of 18 |
| 8 | 5 | 4, 80 | 8 of 30 |
| 9 | 5 | 15, 135 | 18 of 56 |
| 10 | 8 | 30, 90, 155 | 45 of 99 |
| 11 | 4 | 143, 275 | 35 of 186 |
| 12 | 8 | 60, 100, 138 | 78 of 335 |
| 13 | 6 | 117, 130, 533, 689 | 102 of 630 |
| 14 | 9 | 14, 28, 84, 644, 728, 1,316 | 274 of 1,161 |

Backgrounds are counted up to a shift in time; the white row and the alternating stripe are the two of period 1, and the
backgrounds of a divisor of $P$ count again at $P$. The last column counts the primitive blocks of period $P$ that some
background has as a column. The only background of exactly period 4 is the kit's ether, on 7 cells. At periods 5 and 6
every block of the period is a column of a background, and at 7 thirteen of the 18.

- **The traps are walls of a few backgrounds.** Carried leftward, the chain of a trap repeats from some distance on
  ([lock chains](lock-chains.md)), so it ends in a background. For the traps that [the natural scan](natural-traps.md)
  finds, with the phase counted modulo the period, it is always one of the table: at period 8 the kit's ether, for all
  eight window locks; at 9 the background of 135 cells, for the first wall of
  [NineTraps](../../Rule30Open/Columns/NineTraps.md), which carries traps to 21 blocks; at 10 the one of 155 cells, for
  24 blocks; at 11 those of 143 and 275 cells, for 28 and 19 blocks; at 12 those of 60 and 138 cells, for 34 and 39. The
  traps that count the phase modulo a multiple end in backgrounds of that multiple: of period 27 and 15,663 cells for
  the second wall of period 9, 22 and 13,123 cells for four blocks of period 11, and 24 and 14,985 or 38,304 cells for
  two of period 12; two traps of period 10 modulo 20 end in the background of 155 cells, and one modulo 30 in none
  within 100,000 columns. No trap found ends in the backgrounds of 4 or 80 cells at period 8, 30 or 90 at 10, or 100 at
  12, nor does a wall of period 9 end in the one of 15 cells, and at periods 5 to 7, which have backgrounds, the scan
  finds no trap at all ([trap entry](../../negative-results/columns/trap-entry.md)).
- **Every locked window of 16 cells, by background.** Sampling finds the traps that driven halves enter; a census
  finds every lock of a given width. For every block of periods 10 to 16, `lock_backgrounds` in
  [computations/lock_chain.py](../../computations/lock_chain.py) takes the bottom components of its locked windows of
  16 cells, with the phase counted modulo the period, and follows the chain of each to its background:

  | Period | Blocks with a lock | Backgrounds the chains end in: spatial period (blocks) | Blocks the chains hold |
  |---:|---:|---|---:|
  | 10 | 12 | 155 (12) | 28 |
  | 11 | 30 | 143 (16), 275 (14) | 73 |
  | 12 | 41 | 60 (12), 138 (29) | 121 |
  | 13 | 89 | 533 (35), 689 (55) | 243 |
  | 14 | 109 | 644 (26), 728 (55), 1,316 (28) | 411 |
  | 15 | 197 | 64 (17), 85 (16), 105 (12), 540 (22), 795 (24), 2,145 (107) | 648 |
  | 16 | 257 | 216 (12), 325 (217), 2,032 (28) | 1,365 |

  So the backgrounds of 30 and 90 cells at period 10, of 100 at 12, of 117 and 130 at 13, and of 14, 28 and 84 at 14
  have no wall of 16 cells. A wider window does not change this at periods 10 to 12: with 18 cells, 14, 36 and 47 blocks
  have a lock, against 12, 30 and 41, but their chains end in the same backgrounds and hold the same 28, 73 and 121
  blocks, so the wider locks lie along the same chains. Those of 533, 644 and 1,316 cells have walls too, which the
  traps of [NaturalTrapsLong](../../Rule30Open/Columns/NaturalTrapsLong.md) already end in, 13, 14 and 14 of its 70.
  Periods 15 and 16 are past the list above, since their maps have $4^{15}$ and $4^{16}$ states; the census finds six
  backgrounds of period 15 and three of period 16, each confirmed by running one of its rows on its ring. At period 16
  one background, of 325 cells, takes the chains of 217 of the 257 blocks with a lock, and the chains hold 1,365 of the
  4,080 blocks, a third, as at periods 10 to 15 (28%, 39%, 36%, 39%, 35% and 30%): the 68 that the game or the kit
  excludes, and 1,297 that no trap module reaches yet. The chains hold every block of these periods that the game or the
  kit excludes; every block that a trap module reached before the census, except eight whose natural traps count the
  phase modulo twice or three times the period; and 12, 135, 244 and 595 blocks of periods 12 to 15 that nothing
  reached. [FarWalls](../../Rule30Open/Columns/FarWalls.md), [CensusTraps13](../../Rule30Open/Columns/CensusTraps13.md),
  [CensusTraps14](../../Rule30Open/Columns/CensusTraps14.md) and
  [CensusTraps15](../../Rule30Open/Columns/CensusTraps15.md) check traps for all of them but 22 of periods 13 and 14 and
  24 of period 15, whose only components have 3,169 to 30,345 states and which
  [CensusTrapsLarge](../../Rule30Open/Columns/CensusTrapsLarge.md) and
  [CensusTrapsLarge15](../../Rule30Open/Columns/CensusTrapsLarge15.md) check in parts, and but three, one of period 13
  and two of period 15, whose components some node of the finite game cannot reach
  ([MissedTraps](../../Rule30Open/Columns/MissedTraps.md)). The scan with windows of 16 cells, which samples 31 halves
  per block, finds traps for 12, 31, 41, 86 and 109 blocks at periods 10 to 14 ([natural traps](natural-traps.md)): it
  misses few of the blocks with a lock, but most of what their chains hold. The background of 2,145 cells at period 15
  also has walls wider than 16 cells, which the census does not see: the natural traps of 27 and 37 cells of
  $000111111011101$ and $000001101011101$, which sampled halves settle into
  ([TrapSets](../../Rule30Open/Columns/TrapSets.md)). The chain of the first is in the background from the start; that
  of the second reaches it at distance 152, and within 120 columns holds 81 blocks that nothing reached, to which
  [FifteenWalls](../../Rule30Open/Columns/FifteenWalls.md) carries it.
- **Witnesses against the game.** In a background a column can repeat a block of period $p$, a proper divisor of $P$,
  while the column left of it does not repeat with period $p$. Its right side then makes a closed walk of [the finite
  game](../../Rule30Open/Columns/FiniteGame.md) on which the left column takes both values at one phase, so the game
  does not exclude the block at any width ([ring orbits](../../negative-results/columns/ring-orbits.md)). The
  backgrounds of period up to 14, on rings of 7 to 728 cells, witness this for $01$ (from period 4), $0001$ (period 8),
  $00101$ (10), $000101$ and $001011$ (12), and $0000011$, $0010011$, $0011101$ and $0011111$ (14), and for no other
  block (`witnesses`). For $0001$ this settles what [Jen's farther
  columns](../../negative-results/columns/jen-farther-columns.md) found at widths 6 to 12: the game fails at every
  width.
- **Seeding with the background does not find the walls.** Closing the background's own window right of a column,
  rather than a driven half's, gives a trap only on two backgrounds at width 16: at 60 of the 150 columns of period 10
  of the background of 155 cells (70 at width 24), and at 36 of the 135 of period 12 of the one of 138 (42 at 24). It
  gives none on the backgrounds of 143 and 275 cells at period 11 or of 689 at 13, which the traps found by sampling
  have as theirs, nor on the others of periods 8 to 13, nor on that of 135 cells at period 9 even at 43 cells, the
  width of its wall (`background_walls`). The walls are closures of windows where a background meets an irregular
  right side, not of the background itself.

## What it means

The traps that driven halves enter are not scattered: from period 8 to 12 each is the edge, or wall, of one of a handful
of backgrounds, and the backgrounds themselves are few, at most nine per period up to 14, with spatial periods up to
1,316. Their columns hold a sixth to a half of the blocks of each period from 10 on, so a block that is no column of a
background can be reached only from the part of a chain before it repeats, as many carried traps are. Traps at longer
periods come from the same place: the census of locked windows of 16 cells finds the walls of every block at once and
brings a third of each of periods 12, 13 and 14 down to entry into a trap ([the coverage](coverage.md)), against about
an eighth from sampling at 13 and 14, and more than a quarter of period 15. Whether a background has a wall that every
finite half enters is the open entry question again; the backgrounds of periods 5 to 7 show that having a background is
not enough.

## In *A New Kind of Science*

The first part of the argument is in the book. Its [note on repeating blocks in cellular
automata](https://www.wolframscience.com/nks/notes-6-6--repeating-blocks-in-cellular-automata/), to section 6.6, says
that in Rule 30, as in the other rules additive on one side, every configuration that repeats is a sequence of identical
blocks, of at most $2^{2p}$ cells for period $p$: the bound $4^P$ on the length of a cycle here. The section says no
block gives period exactly 2 and blocks give every larger period up to at least 15, as the table shows to 14. The note's
counts differ from the table. It lists 3, 3, 15, 10, 8, 99, 18, 14, 30 and 163 configurations that repeat with periods
dividing 1 to 10. Counting every row of the line whose evolution repeats with such a period gives 3, 3, 15, 31, 48, 99,
108, 119, 195 and 598, the states on the cycles; counting each background up to a shift in time once per cell of its
spatial period gives 3, 3, 15, 10, 48, 99, 18, 94, 165 and 323 (`counts`). The list equals the second count at periods
1 to 4, 6 and 7. At 5, 8 and 9 it falls short by exactly the backgrounds of 15 and 25 cells, of 80 cells and of 135
cells, and at 10 by 160, the backgrounds of 15, 25, 30 and 90 cells (or of 5 and 155). Each of these returns on its ring
after its period in a direct run, so the list leaves them out. [Page
268](https://www.wolframscience.com/nks/p268--special-initial-conditions/) gives a block of 275 cells for period 11; the
background of 143 cells has period 11 as well.

## Reproduce

```bash
python -m computations.space_time_periodic 1,2,3,4,5,6,7,8,9,10,11,12,13,14 --table
python -m computations.space_time_periodic 4,8,10,12,14 --witnesses
python -m computations.space_time_periodic 8,9,10,11,12,13 --walls 16
python -m computations.space_time_periodic 1,2,3,4,5,6,7,8,9,10 --counts
python -m computations.lock_chain --lock-backgrounds 10,11,12,13,14,15 --width 16 --workers 3
python -m computations.lock_chain --lock-backgrounds 16 --width 16 --workers 3
python -m computations.lock_chain --lock-backgrounds 10,11,12 --width 18 --workers 3
```

Each lists the backgrounds by squaring the map on $4^P$ pairs: under a minute to period 13, and period 14 in about two
minutes with a peak of about 6 GB. The census of locked windows takes about two hours with three processes, half of it
at period 15, and two more for period 16, and prints, for each background, after how many steps one of its rows returns on its ring; at width 18 it
takes about an hour for periods 10 to 12. The chains of the traps come from `chain_cycle` in
[computations/lock_chain.py](../../computations/lock_chain.py), on the traps of `natural_tables`, `tables` and
`carried`. The test compares the backgrounds of periods up to 6 with every ring of up to 16 cells run directly, runs
every background of period up to 10 on its ring and counts its rows, and runs the witness for $0001$ on its ring.
