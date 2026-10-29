---
title: Against a white right half, no left half within depth 32,755 keeps the center alternating
category: period-two
problems: [1]
status: proved
lean: Rule30Open.PeriodTwo.WhiteRightHalf
headline: [white_right_leaves, psi_empty_gaps, leaves_by_gap, psiBits_spec]
kit: refines
kit_modules: [Rule30PeriodTwoSideways, Rule30ZeroBoundary, Rule30EtherThreeReach]
evidence: [computations/coupled.py]
---

# Against a white right half, no left half within depth 32,755 keeps the center alternating

The kit's open milestone for period two,
[`Rule30PeriodTwoSideways.CQ01Empty`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30PeriodTwoSideways.lean),
asks that no finite configuration whose cells right of the center are white keeps its center alternating
$1, 0, 1, \dots$ from time 0. Exactly one left half, `Psi empty`, does so forever, and a left half that first
differs from it at depth $d$ loses the alternation exactly at time $d$, an identity the kit proves after observing it
numerically for widths up to 300. Here the kernel computes `Psi empty` to depth 32,768 and finds that its black cells
are never 13 or more apart, which settles the milestone for every configuration whose left half lies within depth
32,754.

## Statement

1. `white_right_leaves`. Let $x$ be a row whose cells right of the center are white and whose cells left of
   $-W$ are white, with $W < 32{,}755$. Then the center of its orbit leaves $1, 0, 1, \dots$ by time $W + 13$.
2. `psi_empty_gaps`. For every $W < 32{,}755$ some depth $d$ with $W < d \le W + 13$ is black in `Psi empty`.
3. `leaves_by_gap`. The reduction: whenever `Psi empty` has a black depth in $(W, W + G]$, every row as in statement
   1 leaves the alternation by time $W + G$.
4. `psiBits_spec`. The computed number `psiBits N` has bit $d$ equal to `Psi empty` at depth $d$, for
   $1 \le d \le N$.

## Argument

1. **The one candidate** (the kit). Against the white right half, the right half evolves as the half driven by the
   alternating center, so its column 1 is known, and the center's update fixes column $-1$: black at even times, the
   opposite of column 1 at odd times (`yAt`). Rule 30 is permutive in its left cell, so column $-1$ rebuilds the whole
   left half sideways beside a white wall; the row at time 0 is `Psi empty` (`Psi_unique`). A left half that first
   differs from it at depth $d$ keeps the center alternating through time $d - 1$ and not at time $d$
   (`exact_death_center`).
2. **The reduction** (`first_difference`, `leaves_by_gap`). A row as in statement 1 has center black at time 0 or
   leaves the alternation at once; if black, it is the kit's `glue` of its left half and the white right half. Its
   left half is white beyond $W$, so it differs from `Psi empty` at the first black depth of `Psi empty` beyond $W$ at
   the latest, and the center leaves by then.
3. **Column $-1$ in one pass** (`yLoop`, `yLoop_spec`). The kit's packed driven half `rowN` steps the right half; the
   loop collects column $-1$ at times $0, \dots, N - 1$ as the bits of one number, forcing each step as the kit's
   `centerLoop` does.
4. **Sideways in one pass** (`colN`, `colN_testBit`, `psiLoop`, `psiLoop_spec`). Column $-k$, as a number over time,
   is the shift of column $-(k - 1)$ XOR the OR of columns $-(k - 1)$ and $-(k - 2)$, with the white wall at depth 0:
   the kit's `recon`, one column per step. Bit 0 of column $-k$ is `Psi empty` at depth $k$; it reads column $-1$
   at times below $k$, so depths up to $N$ are exact (`psiBits_spec`).
5. **Gaps** (`runsAnd`, `gapsCheck`, `gaps_of_check`). The AND of the complement of the bits with its shifts by
   $1, \dots, G - 1$ marks the starts of $G$ white depths in a row; it vanishes on depths $1, \dots, W_0$.
6. **The computation.** The kernel checks `yLoop 32768 0 0 0` and `psiLoop` against the literals `yBits` and
   `psiBitsLit` and the gaps for $G = 13$ and $W_0 = 32{,}755$ (`yLoop_eq`, `psiLoop_eq`, `gaps_eq`).

## The numbers

`white_literals` in [computations/coupled.py](../../computations/coupled.py) computes the two literals and agrees with
`psi` there, which rebuilds the row beside the alternating center instead of the white wall. Up to depth 32,768 the
longest white run of `Psi empty` is 12, first at depth 16,529; [the white-right-half
finding](../../findings/period-two/white-right-half.md) follows it to depth $2^{20}$, where the longest run is 20. The
module builds in about 40 seconds with a peak below 2 GB; depth 65,536 would need the computation in chunks.

## What it covers

`CQ01Empty` asks this for every finite left half. The bound here grows with the depth computed, and the white runs
grow like those of a random sequence, so a computation settles bounded cases only. The kit proves `Q01`, a statement
about the left half alone that covers every right half, for starts of width up to 52 (`Rule30ZeroBoundaryWidth52`);
this module covers the white right half only, with left halves up to depth 32,754.

## Lean

`Rule30Open.PeriodTwo.WhiteRightHalf`: `yAt`, `rowN_empty_bit`, `yAt_eq`, `yLoop`, `yLoop_spec`, `colN`,
`colN_testBit`, `psiLoop`, `psiLoop_spec`, `psiBits`, `psiBits_spec`, `runsAnd`, `testBit_runsAnd`, `gapsCheck`,
`gaps_of_check`, `first_difference`, `leaves_by_gap`, the literals `yBits` and `psiBitsLit` with `yLoop_eq`,
`psiLoop_eq` and `gaps_eq`, `psi_empty_gaps` and `white_right_leaves`.
