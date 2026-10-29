---
title: No left half within depth 88 keeps the kit's left-half pattern for 0011 or 0111
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.LeftHalfDriven
headline: [c3_0011_bounded, c3_0111_bounded, c3_0011_small, c3_0111_small, c3G_of_checks, history_eq_reconB]
kit: refines
kit_modules: [Rule30PeriodFourSkeleton, Rule30ZeroBoundaryLanes, Rule30DrivenLeft]
evidence: [computations/held_map.py]
---

# No left half within depth 88 keeps the kit's left-half pattern for 0011 or 0111

The kit reduces least period four of the center column to three open statements about the left half alone, one for
each word ([`Rule30PeriodFourSkeleton.C3`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30PeriodFourSkeleton.lean)).
[LeftHalf0001](LeftHalf0001.md) proves the case of $0001$ in which the half lies within depth 88 at the time from which
it keeps the pattern. This module proves the same case for $0011$ and $0111$. Their effective boundary is not white, so
the kit's lane checker, written for the white boundary, is extended here to a boundary column that enters the
reconstruction at every step. With both modules, every left-half statement of the kit for period four holds for the
halves that lie within depth 88 at that time.

## Statement

A left half $s$ runs as Rule 30 beside the kit's effective boundary $c'_w(k) = w(k) \land w(k + 1)$, black at phase 2
for $0011$ and at phases 1 and 2 for $0111$. Both words have the same pattern $P_w$: column $-1$ is free at the
times $k \equiv 0$, white at $k \equiv 1$ and $2$, and black at $k \equiv 3 \pmod 4$.

1. **The bounded cases** (`c3_0011_bounded`, `c3_0111_bounded`). If column $-1$ keeps $P_w$ from time $K$, the half
   has a black cell at a depth beyond 88 at time $K$.
2. **Small halves** (`c3_0011_small`, `c3_0111_small`). If $s$ is white left of cell $-M$ and $M + K \le 88$, column
   $-1$ does not keep $P_w$ from time $K$.
3. **Every phase** (`c3_0011_depth`, `c3_0111_depth`). For each phase, every half white beyond depth 88, with column
   $-1$ read beside the boundary from that phase, leaves the pattern before time 115.
4. **The checker** (`c3G_of_checks`). For any depth $W$, number of levels $K$, phase, pattern and boundary given as bit
   masks over the phase: if every chunk passes `checkG`, every half white beyond depth $W$ leaves the pattern before
   time $K$.
5. **Sharpness** (`sharp20_0011_0` to `sharp20_0111_3`). At depth 20 the least $K$ that passes is one more than the
   latest first failure over the halves of at most 20 cells, for each word and phase.

## Argument

1. **Reconstruction beside a boundary** (`reconB`, `history_eq_reconB`). Rule 30 is permutive in its left cell, so
   the cell at depth $d + 2$ and time $t$ is the cell at depth $d + 1$ and time $t + 1$, XOR the OR of the cells at
   depths $d + 1$ and $d$ at time $t$. Depth 0 is the boundary column. So column $-1$ and the boundary determine the
   whole half from any time $K$ on; for the white boundary this is the kit's `history_eq_recon`.
2. **Anti-diagonals** (`scanN_ADB`, `levelB`). The cells with depth plus time equal to $k$ form anti-diagonal $k$.
   Anti-diagonal $k + 1$ is the kit's running XOR over anti-diagonals $k$ and $k - 1$, started from the reading at
   time $k$, with the boundary at time $k - 1$ in place of the white wall at depth 0; its last entry is the start's
   cell at depth $k + 1$.
3. **The lanes** (`stepG`, `runG`, `checkG`). As in [LeftHalf0001](LeftHalf0001.md): one free reading in four, a free
   bit while $t + 1 \le W$ and forced by the white start beyond, $2^n$ choices of the first $n$ free readings at once,
   one per bit position of a natural number. The pattern and the boundary are bit masks over the phase: with the
   phase moved by one, so that the free reading falls at phase 1, the pattern reads 1 at phase 0 and 0 at phases 2
   and 3 (`ones = 1`), and the boundary is black at phase 3 for $0011$ (`bnd = 8`) and at phases 2 and 3 for $0111$
   (`bnd = 12`). The boundary is the same in every lane, a number with all bits or no bits set.
4. **Soundness** (`runG_sound`, `c3G_of_checks`). A half that keeps the pattern through time $K - 1$ and is white
   beyond depth $W$ is followed by its own lane, which never dies.
5. **The checks.** At depth 88 with $n = 18$: for each word, 16 chunks per phase, 64 in all, each of $2^{18}$ lanes
   and 115 levels, evaluated by the kernel (`decide +kernel`).
6. **The kit's form.** From time $K$ the boundary and the pattern of the kit, read at times $K + t$, are the masks
   above at phase $(K + 1) \bmod 4$ (`drive_0011`, `drive_0111`, `fits_x011`). The support grows by at most one cell
   per step whatever the boundary (`L_fin`), which gives statement 2.

## The numbers

`python -m computations.held_map 88 --tree c3 --word 0011` and `--word 0111` follow the tree of readings the pattern
allows ([computations/held_map.py](../../computations/held_map.py), `tree_failures`) and find the latest first
failure over the halves of at most 88 cells at steps 114, 113, 112 and 112 for $0011$ and 114, 113, 113 and 112 for
$0111$, by the kit's phase, so 115 levels suffice. At depths 20 and 24 the least number of levels that passes the Lean
check is one more than the search's latest failure for both words in every phase; `sharp20_0011_0` to
`sharp20_0111_3` record depth 20. The module builds in about two and a half minutes with a peak near 1 GB.

## What it covers

With [LeftHalf0001](LeftHalf0001.md), each of the kit's three statements `C3 w` holds for every half that lies within
depth 88 at the time from which it would keep the pattern. `least_period_four_of_C3` needs them for every finite half:
for the single cell the half at that time has as many cells as the time, so no bounded case reaches it. As for
$0001$, the work of a check doubles with every four cells of depth, and the latest failure keeps growing past the
half's length ([the left-half finding](../../findings/columns/left-half-c3.md)).

## Relation to the kit

The checker generalizes the kit's `Rule30ZeroBoundaryLanes` (for its period-two statement `Q01` beside the white
wall) to a boundary column and to a pattern and boundary given by the phase. `scanN`, `mapX`, `yFree`, `pat`, `pack`,
`getD_tail`, `headD_eq`, `getD_testBit` and `scanN_lin` are the kit's; `reconB`, `ADB`, `scanN_ADB` and `levelB`
follow its `recon`, `AD`, `scanN_AD` and `level` with the boundary in place of the white wall. `history_eq_reconB`
uses the kit's `Rule30DrivenLeft.L_left` and `L_col0`. The kit proves no case of `C3`.

## Lean

`Rule30Open.Columns.LeftHalfDriven`: `reconB`, `history_eq_reconB`, `ADB`, `ADB_getD`, `scanN_ADB`, `levelB`,
`KeepsG`, `stepG`, `runG`, `checkG`, `laneB`, `runG_sound`, `c3G_of_checks`, `ChunksG` with `chunksG_one` and
`chunksG_append`, the 128 checks `chunk<word>_<φ>_<c>` with `chunks<word>_<φ>`, `c3_0011_depth`, `c3_0111_depth`,
the sharpness checks, `drive_0011`, `drive_0111`, `fits_x011`, `L_fin`, and the bounded and small cases for both
words. The free-reading indices `freeIdx`, `freeTime` and `freeCount` are those of `LeftHalf0001`.
