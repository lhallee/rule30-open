---
title: Every configuration white left of a black cell settles to the single cell's pairs of left diagonals up to a time shift, as long as each white diagonal is followed by a doubling period
category: diagonals
problems: [2]
status: proved
lean: Rule30Open.Diagonals.DrivenSkeleton
headline: [shift_of_black, shift_or_flip_of_white, skeleton_step, skeleton_step_of_flip, base_shift]
kit: new
kit_modules: [Rule30FiniteDiagonals, Rule30Diagonals, Rule30AgedLeftDiagonals]
evidence: [computations/run_slope_routes.py]
---

# Every configuration white left of a black cell settles to the single cell's pairs of left diagonals up to a time shift, as long as each white diagonal is followed by a doubling period

The kit proves that every left diagonal of every configuration white left of some cell is eventually periodic with
period dividing $2^j$, from time $2^j - 1$ (`Rule30FiniteDiagonals.Ld_uniform_period`). This module shows that the
periodic parts themselves do not depend on the configuration: depth by depth, the eventual pair of diagonals
$(D_j, D_{j+1})$ of any such configuration is the single cell's pair read with a time shift. The Lean module proves the
step and the base of the induction; the induction and its one finite check are below.

## Statement

Let $b(i, t)$ be the left diagonals of a configuration $x$ that is white left of $\mathrm{lo}$, $b(i, t) =
\mathrm{cell}_t(\mathrm{lo} - t + i)$ (the kit's `Rule30FiniteDiagonals.Ld`), and $b'$ the same for a second such
configuration. Both obey $b(i+2, t+1) = b(i, t) \oplus (b(i+1, t) \lor b(i+2, t))$ for all $i, t$ (`Ld_diagStep`, which needs no white side). Say
diagonal $i$ of $b$ is diagonal $i$ of $b'$ shifted by $h$ from $T$ if $b(i, t) = b'(i, t + h)$ for $t \ge T$. The step
lemmas below ask the recurrence of $b$ only for diagonal $i + 2$ and only from time $T$ (`DiagStepFrom`), so they also
hold for the left half driven by any center column, whose diagonal $j$ obeys the recurrence from time $j + 1$ on (take
$T \ge i + 2$).

- `shift_of_black`: if diagonals $i$ and $i + 1$ are shifted by $h$ from $T$ and $b(i + 1, r) = 1$ for some $r \ge T$,
  diagonal $i + 2$ is shifted by $h$ from $r + 1$.
- `shift_or_flip_of_white`: if diagonals $i$ and $i + 1$ are shifted by $h$ from $T$ and $b(i + 1, \cdot)$ is white
  from $T$, then from $T$ on $b(i + 2, t)$ is either $b'(i + 2, t + h)$ for every $t$ or its complement for every $t$.
- `skeleton_step`: so either the pair $(i + 1, i + 2)$ is shifted by $h$ from some time, or diagonal $i + 1$ is white
  from $T$ and diagonal $i + 2$ is the complement of the shift.
- `skeleton_step_of_flip`: if moreover $b'(i + 1, \cdot)$ repeats with period $P$ and $b'(i + 2, t + P) = \lnot
  b'(i + 2, t)$ (from a time $T' \le T + h$), the pair $(i + 1, i + 2)$ is shifted by $h$ or $h + P$ from some time.
- `base_shift`: any two configurations white left of a black cell $\mathrm{lo}$ have diagonals 0 and 1 black from
  time 1, so the pair $(0, 1)$ is shifted by 0 from time 1.

## Argument

1. **Reset.** Where $b(i + 1, t) = 1$ the OR is 1 and $b(i + 2, t + 1) = \lnot b(i, t)$. At $r$ both arrays reset to
   the same value, and from then on each step of $b(i + 2)$ reads the same inputs as the step of $b'(i + 2)$ $h$ times
   later, so by induction they agree (`shift_of_black`). With $b' = b$ and $h = P$ this is the reset
   lemma for periods (`D_periodic_of_black` in [LeftMemory](LeftMemory.md); in the kit, `reset_first_period` and
   `reset_inherits` of `Rule30AgedLeftDiagonals`); the comparison of two different arrays is what is new.
2. **Accumulate.** Where $b(i + 1, t) = 0$, $b(i + 2, t + 1) = b(i, t) \oplus b(i + 2, t)$, and the same for $b'$ $h$
   steps later. So $b(i + 2, t) \oplus b'(i + 2, t + h)$ does not change from $T$ on (`shift_or_flip_of_white`).
3. **A flip is a shift.** If $b'(i + 2)$ flips every $P$ steps, its complement at $t + h$ is its value at $t + h + P$,
   and the periodic $b'(i + 1)$ does not see the extra $P$ (`skeleton_step_of_flip`).

**The induction (paper).** Take $b'$ the single cell. By `base_shift` the pair $(0, 1)$ of every configuration white
left of a black cell is shifted from time 1. By `skeleton_step`, the shift passes to the next pair unless diagonal
$i + 1$ is eventually white; in that case [LeftMemory](LeftMemory.md) (`D_period_dichotomy`) says the single cell's
diagonal $i + 2$ either repeats with the period $P$ of diagonal $i$ or flips every $P$ steps, and in the second case
`skeleton_step_of_flip` passes the shift. So the induction reaches depth $J$ as long as every eventually white diagonal
$w < J$ of the single cell is followed by a flip, that is by a doubling period at $w + 1$. The white diagonals of the
single cell below depth 8,000 are 2, 7, 28 and 399, and the periods at 3, 8, 29 and 400 are 2, 4, 8 and 16, twice those
at 1, 6, 27 and 398 (`skeleton` in [run_slope_routes.py](../../computations/run_slope_routes.py), from 24,600 rows;
the depths match Wolfram's 3, 8, 29, 400 quoted in [LeftMemory](LeftMemory.md)). Hence every configuration white left
of a black cell has, at every depth $j < 8{,}000$, the single cell's eventual pair $(D_{j-1}, D_j)$, read with a time
shift. The check is a computation over that depth range. It extends to depth 53,207 and stops there: the white
diagonals below depth 59,000 are 2, 7, 28, 399, 53,207 and 58,286 (`followers`, which reads every diagonal over the
last 128 of 110,000 steps, as in [the records](../../findings/diagonals/left-records.md)), and at 53,207 and 58,286 the
diagonal before the white one has even weight per period (6 and 10 of 16), so the diagonal after it does not flip,
and that diagonal's complement is not one of its rotations. So at depth 53,208 the step leaves two candidate classes,
the single cell's pair and the pair with $D_{53208}$ complemented. Some configuration settles to the second: [SkeletonTree](SkeletonTree.md) realizes it by flipping one cell of the
single cell's row at time 107,310 (`branch_realized`, `branch_not_shift`). So the time-shift statement holds for the
pairs $(D_{j-1}, D_j)$ with $j \le 53{,}207$, on the evidence of that computation, and fails at depth 53,208 for some
configurations.

For the left half driven by an arbitrary center column $c(0) = 1, c(1), \ldots$ (a relaxation: not every such
column is realized by a configuration), diagonal 0 is black from time 0 and diagonal 1 from time 2, so the pair
$(0, 1)$ is shifted by 0 from time 2 (paper; `base_shift` covers only configurations), and the same induction applies
through the step lemmas. Over every such column `driver_pairs` finds exactly one class of eventual pairs up to a time
shift at each depth $j \le 90$, an independent check by enumeration.

## What it means

For runs of the center column, the driven left halves of
[driven left runs](../../findings/diagonals/driven-left-runs.md) differ from the single cell only in their transients:
where the diagonals settle, they are the single cell's, at least down to depth 53,207. A bound on runs that holds over every driver therefore needs
the same input as the single cell's: the settling of the left diagonals
([settled runs](../../findings/diagonals/settled-runs.md)). Where each route stops is in
[driven run slopes](../../negative-results/diagonals/driven-run-slopes.md).
