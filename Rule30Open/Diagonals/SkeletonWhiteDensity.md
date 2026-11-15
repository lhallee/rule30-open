---
title: On every eternal orbit of the left-edge frame, the single cell's shadow included, at least (2J - 4)/5 of the first J left diagonals are white on average over a period; for every row, 3 W + 2 W' >= 2J - 4 over one step, with the constant 4 attained for 2 <= J <= 12 (computed)
category: diagonals
problems: [2]
status: proved
lean: Rule30Open.Diagonals.SkeletonWhiteDensity
headline: [SkeletonWhiteDensity.local_ineq, SkeletonWhiteDensity.two_black_le, SkeletonWhiteDensity.white_step, SkeletonWhiteDensity.orbit_white, SkeletonWhiteDensity.eternal_white]
kit: new
kit_modules: [Rule30FiniteDiagonals]
evidence: [computations/skeleton_white_density.py, tests/test_skeleton_white_density.py]
---

# On every eternal orbit of the left-edge frame, the single cell's shadow included, at least (2J - 4)/5 of the first J left diagonals are white on average over a period; for every row, 3 W + 2 W' >= 2J - 4 over one step, with the constant 4 attained for 2 <= J <= 12 (computed)

In the left-edge frame a row $R$ is read from its frame cell rightward, coordinate $d$ being left diagonal $d$, and
one step of rule 30 is $\mathrm{leftStep}(R)_d = R_{d-2} \oplus (R_{d-1} \lor R_d)$ with $R_{-1} = R_{-2} = 0$
([EternalSkeleton](EternalSkeleton.md)). Let $W_J(R)$ be the number of white cells among diagonals $0, \dots, J-1$.

## Statement

- `local_ineq`: with $\psi(0,0) = 0$, $\psi(0,1) = 1$, $\psi(1,\cdot) = 2$, every $a, b, c$ and
  $y = a \oplus (b \lor c)$ satisfy $2[y = 1] + \psi(b, c) \le 3[a = 0] + \psi(a, b)$. This is the potential of
  [RowWhiteDensity](../Foundations/RowWhiteDensity.md) (`local_ineq`), re-proved here by cases.
- `two_black_le`: for every row $R$ and every $J$, the black cells of $\mathrm{leftStep}(R)$ among diagonals
  $0, \dots, J-1$ number at most $(3 W_J(R) + 4)/2$.
- `white_step`: for every row $R$ and every $J$, $3 W_J(R) + 2 W_J(\mathrm{leftStep}\, R) \ge 2J - 4$.
- `orbit_white`: along any forward orbit $f_0, f_1, \dots$ and any $P$,
  $2JP + 2W_J(f_0) \le 5 \sum_{i < P} W_J(f_i) + 2 W_J(f_P) + 4P$.
- `eternal_white`: on every eternal orbit $(R_t)_{t \in \mathbb{Z}}$, for every $t_0$ and $J$,
  $5 \sum_{i < 2^J} W_J(R_{t_0 + i}) \ge (2J - 4)\, 2^J$. Over the common period $2^J$ of the first $J$ diagonals, at
  least $(2J - 4)/5$ of them are white on average, so the white density of the first $J$ diagonals is at least
  $2/5 - 4/(5J)$.

By `shadow_eternal` the last statement holds for the shadow of the single cell, whose diagonal $d$ is the periodic part
of the single cell's diagonal $d$. It also holds for every eternal orbit, so it does not depend on which branch of
the skeleton tree ([SkeletonTree](SkeletonTree.md)) the orbit follows.

## Argument

1. **Telescoping in depth.** Put the two white cells $R_{-2}, R_{-1}$ in front of $R$ (`pad`), so that
   $\mathrm{leftStep}(R)_d = a \oplus (b \lor c)$ with $(a, b, c) = (R_{d-2}, R_{d-1}, R_d)$. Summing `local_ineq` over
   $d = 0, \dots, n - 1$, the $\psi$ terms telescope (`telescope`):
   $2\,\mathrm{black}_n(\mathrm{leftStep}\,R) + \psi(R_{n-2}, R_{n-1}) \le 3\,(2 + W_{n-2}(R)) + \psi(0, 0)$, with
   $\psi(0,0) = 0$.
2. **The constant.** $W_J(R) = W_{J-2}(R) + [R_{J-2} = 0] + [R_{J-1} = 0]$, and in each of the four cases of
   $(R_{J-2}, R_{J-1})$, $6 - \psi(R_{J-2}, R_{J-1}) \le 3([R_{J-2} = 0] + [R_{J-1} = 0]) + 4$. So
   $2\,\mathrm{black}_J(\mathrm{leftStep}\,R) \le 3W_J(R) + 4$ (`two_black_le`; $J = 0, 1$ directly). With
   $\mathrm{black} + \mathrm{white} = J$ this is `white_step`.
3. **Over time.** Summing `white_step` over $P$ consecutive rows gives `orbit_white`. On an eternal orbit, diagonal
   $d < J$ has period dividing $2^d$, hence $2^J$ (`EternalSkeleton.eternal_periodic_mul`), so $W_J(R_{t_0 + 2^J}) =
   W_J(R_{t_0})$, the boundary terms cancel, and $5 \sum W_J \ge (2J - 4) 2^J$.

## Numbers (computed)

`skeleton_white_density`:

- **The constant 4 is attained.** Over all rows of $J$ diagonals, the least value of
  $3W_J(R) + 2W_J(\mathrm{leftStep}\,R) - 2J$ is $-2$ at $J = 1$ and $-4$ for every $2 \le J \le 12$.
- **The single cell's actual settled words are about half white.** On depths 400 to 53,200, read at period 16, the
  white fraction is 0.5002. Over $3 \le J \le 53{,}201$ the ratio $5W / ((2J - 4)P)$ is at least 1.1667, so the bound
  holds there with room. As $J$ grows, the white fraction tends to about 0.50, against the bound's 2/5.

## What it means

This is an unconditional density statement about the regular left side of the single cell's pattern, and it
concerns **white cells only**. On the shadow of the single cell, at least $2/5 - 4/(5J)$ of the cells of the first $J$
diagonals are white, averaged over a period. It says nothing about black cells there. The step alone forces no
positive density of black cells uniform in the period
([depth register](../../negative-results/diagonals/depth-register-density.md)): windows of up to 8 words that obey
the step can have bounded weight at every period. It also says nothing about the center column, which lies in the
transient.

**Which cells of the single cell's pattern it covers.** `orbit_white` holds for the forward orbit itself with no
settling, so on the first $J$ diagonals of the single cell's own pattern, over any $P$ consecutive steps, the white
cells number at least $((2J - 4)P - 2J)/5$. The two boundary rows cost at most $2J$. This is unconditional, needs no
shadow, and counts the transient cells of those diagonals too. It is a strip of the white-density bound of
[RowWhiteDensity](../Foundations/RowWhiteDensity.md), whose `strip_white` bounds strips at a fixed position; here the
strip moves with the left edge. The per-period form for the shadow applies to the pattern's cells exactly where the pattern equals its shadow:
on diagonal $d$ from time $2^d - 1$ on (`shadow_forward`, proved), or from its onset $T_d$, which
[seed-uniform onsets](../../findings/diagonals/seed-uniform-onsets.md) bounds by $\lceil 3d/2 \rceil + 5$ for
$d \le 76$ and conjectures for every $d$.

## In Lean

`Rule30Open/Diagonals/SkeletonWhiteDensity.lean`, importing `EternalSkeleton` for `leftStep`, `Eternal` and pure
periodicity. The local inequality is checked by `decide` on its eight cases; the rest is induction and `omega`.

## Relation to the kit

The kit has no density statement for white or black cells of the left diagonals. Its
`Rule30AgedLeftDiagonals.Ld_white_witness_after_reset` gives white cells in intervals of left diagonals for every
configuration that is white left of an anchor: white witnesses, not a density. [RowWhiteDensity](../Foundations/RowWhiteDensity.md)'s
`triangle_white` bounds the white cells of the whole triangle, left side included, but not of the left diagonals alone. The potential is
[RowWhiteDensity](../Foundations/RowWhiteDensity.md)'s, applied along the depth instead of along a row, with the frame
supplying the two white cells that start the telescoping.
