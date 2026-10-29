---
title: After nine 1s, the set of possible three-cell windows excludes every block with nine 1s that the game excludes
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.WallSets
headline: [center_wall_set_block, center_runs_odd_100, center_runs_odd_110, center_runs_even_1010, wall_sets_column]
kit: refines
kit_modules: [Rule30BlackRuns, Rule30BlackRunBlocks]
evidence: [computations/wall_segments.py]
---

# After nine 1s, the set of possible three-cell windows excludes every block with nine 1s that the game excludes

[WallSegments](WallSegments.md) follows the two cells right of a column after nine 1s with three values per cell, and
excludes every eventual period whose segments between long runs of 1s the three-valued run follows. Three values
forget how unknown cells are correlated. Here the state is the set of windows of three cells, right of the column,
that the true row may hold: one of $2^8$ subsets, kept as the bits of a number. The set keeps the correlations, knows
the cell right of the column more often, and can come to know it again after the column reads 1s.

## Statement

1. **Any block** (`wall_set_block_column`, `center_wall_set_block`). No column of the orbit of a row with a leftmost 1
   repeats a block $B$ with `wallSet B = true`: some place of $B$, read cyclically, follows nine 1s, and from there the
   set of windows, back at the wall after every nine 1s, has one value of the first cell at every 0 of one period.
2. **One run and one segment** (`run_set_column`, `center_run_set`). For every $a \ge 9$, no column repeats $1^a u$,
   for every $u$ that starts with 0, passes `segSet` from the wall, and has a 0 among any nine consecutive places.
3. **Three parity families** (`center_runs_odd_100`, `center_runs_odd_110`, `center_runs_even_1010`). For every
   $a \ge 9$ and $k \ge 0$, the center column does not repeat $1^a 0^{2k+3} 1 0 0$, $1^a 0^{2k+3} 1 1 0$ or
   $1^a 0^{2k+2} 1 0 1 0$ from any time on. The three-valued run of WallSegments excludes none of them.
4. **The general form** (`wall_sets_column`), along the column itself.

## Argument

1. **Sets of windows** (`sstep`, `sstep_sound`). The window is cells $k + 1$, $k + 2$ and $k + 3$; one step beside a
   column reading $x$ maps window $c_1 c_2 c_3$, with the next cell $c_4$ free, to
   $x \oplus (c_1 \lor c_2)$, $c_1 \oplus (c_2 \lor c_3)$, $c_2 \oplus (c_3 \lor c_4)$. The set step takes every
   window of the set and both values of $c_4$; the kernel checks over all 256 sets that the true next window is in the
   next set. Nine 1s put the window in the wall, the four windows $0 1 *$ (`wall3`), by the wall of
   [LongRuns](LongRuns.md).
2. **Knowing the next cell** (`sknown`, `sknown_val`). When every window of the set has the same first cell, that is
   the true value of cell $k + 1$.
3. **The rest** is the argument of [WallSegments](WallSegments.md) with the set in place of the three values: the set
   is sound along the real column (`sstate_sound`), repeats with the column (`sstate_periodic`), and where it knows
   cell $k + 1$ at the 0s of column $k$, column $k - 1$ is a function of column $k$, so two adjacent columns are
   eventually periodic (`wall_sets_column`). Blocks and single segments follow as there (`wall_set_block_column`,
   `run_set_column`).
4. **The parity families.** From the wall, 0s take the set through 136, 34, 168, 34, 168, … (as numbers), each with
   one value of the first cell (`segSet_zeros_168`, `segSet_zeros_34`). After an odd number of 0s, at least three,
   the tails $1 0 0$ and $1 1 0$ pass; after an even number, at least two, the tail $1 0 1 0$ does. The kernel checks
   the tails, and the cycle carries them to every length.

## What it adds

[computations/wall_segments.py](../../computations/wall_segments.py) runs the same sets (`in_set_family`, which agrees
with `wallSet` on all 8,800 primitive blocks up to period 16). Up to period 16 the family has 77 blocks, exactly the
77 blocks with nine 1s in a row that [the finite game](../../findings/columns/game-blocks.md) excludes, 43 of them
beyond the blocks of that range that the kit excludes (`--max-period 16 --game`); the three-valued family has 64 of
them. The game proves those blocks one certificate at a time; this module proves them, and the family at every period,
with one argument. Up to period 22 it has 616 blocks, against 275 for the three values
(`python -m computations.wall_segments --max-period 22`). Up to 12 cells, the sets accept 123 of the 124 segments that
brute force over the light cone accepts, and windows of eight cells accept all of them, so wider windows add little.

## Why nine

Nine is the least run that leaves the first cell known. Over every start of the cells that can reach them, $r$ 1s
leave the windows 0 1 0 and 0 1 1 for $r = 9$, and for $r \le 8$ windows with both values of the first cell; eight
leave 0 1 0, 0 1 1 and 1 0 0 (`python -m computations.wall_segments --after-ones`). So after eight 1s the first 0 of
the column already fails the check, as the kit's `eight_black_not_enough` says of its own argument.

## Relation to the kit

As for [WallSegments](WallSegments.md): the kit's
[`Rule30BlackRuns`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30BlackRuns.lean)
has the wall and the all-long-runs family, and Theorems B and D for runs long compared with the rest of the period;
[`Rule30BlackRunBlocks`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30BlackRunBlocks.lean)
checks eight tails one at a time after 18 or 27 1s. The parity families need a run of only nine and have tails of
every length; the kit's Theorem B reaches $1^a 0^b 1 0 0$ only when $a \ge 9 \lceil (b + 12)/2 \rceil$, and its
Theorem D only when $b \ge 55$. The kit's finite game has no counterpart; [the finite game](FiniteGame.md) here checks
one block per certificate.

## Lean

`Rule30Open.Columns.WallSets`: `widx`, `wmem`, `wimg`, `sstep`, `sstep_sound`, `sstep_lt`, `sknown`, `sval`,
`sknown_val`, `wall3`, `sstate`, `sstate_sound`, `sstate_periodic`, `wall_sets_column`, `wallSet`, `sstate_congr`,
`wall_set_block_column`, `center_wall_set_block`, `segSet`, `srun`, `segSet_known`, `sstate_eq_srun`,
`run_set_column`, `center_run_set`, the zero cycle (`segSet_zeros_168`, `segSet_zeros_34`), `gap_zeros_tail`, the
three families and `wallSet_odd_100`. It builds in a few seconds.
