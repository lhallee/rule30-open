---
title: Every background of Rule 30 periodic in time, to period 14, and the traps at their edges
category: columns
problems: [1]
status: computed
formalization: wanted
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
complete.

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
background can be reached only from the part of a chain before it repeats, as many carried traps are. The table also
says where to look for traps at longer periods: at the edges of the backgrounds of periods 13 and 14 rather than by
sampling. Whether a background has a wall that every finite half enters is the open entry question again; the
backgrounds of periods 5 to 7 show that having a background is not enough.

## Reproduce

```bash
python -m computations.space_time_periodic 1,2,3,4,5,6,7,8,9,10,11,12,13,14 --table
python -m computations.space_time_periodic 4,8,10,12,14 --witnesses
python -m computations.space_time_periodic 8,9,10,11,12,13 --walls 16
```

Each lists the backgrounds by squaring the map on $4^P$ pairs: under a minute to period 13, and period 14 in about two
minutes with a peak of about 6 GB. The chains of the traps come from `chain_cycle` in
[computations/lock_chain.py](../../computations/lock_chain.py), on the traps of `natural_tables`, `tables` and
`carried`. The test compares the backgrounds of periods up to 6 with every ring of up to 16 cells run directly, and runs
the witness for $0001$ on its ring.
