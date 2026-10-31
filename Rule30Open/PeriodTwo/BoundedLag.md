---
title: The period-two condition is invisible at a bounded lag
category: period-two
problems: [1]
status: proved
lean: Rule30Open.PeriodTwo.BoundedLag
headline: [held_preimage, pull_back, complete_window, invisible_at_bounded_lag, inK_window_invisible, invisible_at_bounded_lag_rational]
kit: new
kit_modules: [Rule30Jen]
---

# The period-two condition is invisible at a bounded lag

Let $H$ be the held map of [HeldColumn](HeldColumn.md) on bit sequences, `column U t` bit 0 of $H^t(U)$, and $K$ the
set of $U$ whose column reads 1 at every odd time ([ShiftModel](ShiftModel.md)). This module proves that conditions
on the column reads before time $s + m$ say nothing about the cells $j \ge m$ of $H^s(U)$.

## Statement

- `held_preimage`: $H$ is onto, and cell 0 of a preimage can be chosen freely.
- `pull_back`: every $X$ is $H^s(U)$ for some $U$ whose column reads at the times $t < s$ are any prescribed bits.
- `complete_window`: every $Y$ can be changed on its cells below $m$ so that its column reads at the times $t < m$
  are any prescribed bits.
- `invisible_at_bounded_lag`: for every $Y$, $s$, $m$ and every prescription $P$ of the column reads at the times
  $t < s + m$, some $U$ has $H^s(U)_j = Y_j$ for every $j \ge m$ and column reads $P$ at those times.
- `inK_window_invisible`: in particular the reads can all be 1 at the odd times below $s + m$, the condition of $K$
  up to that time.
- `invisible_at_bounded_lag_rational`: when $Y$ is eventually periodic, $U$ can be taken eventually periodic.

## Argument

Column reads are triangular (item 1 of [the shift model](../../findings/period-two/shift-model.md)): bit 0 of
$H^t(X)$ is $x_t$ plus a function of $x_0, \ldots, x_{t-1}$. So choosing $x_0, \ldots, x_{m-1}$ in turn sets the reads
at the times below $m$, with $X$ equal to $Y$ from cell $m$ on. A preimage of $h$ under $H$ is determined by its cell 0
through $u_1 = h_0 \oplus u_0$ and $u_{j+2} = h_{j+1} \oplus (u_{j+1} \lor u_j)$, and its cell 0 is the column read one
step earlier, so pulling $X$ back $s$ steps sets the reads at the times below $s$. For the rational form, the window
changes finitely many cells, and the recursion on pairs of cells over an eventually periodic $h$ repeats, by the
kit's pigeonhole (`Rule30Jen.pigeonhole`) applied to the pairs at five cells spaced by the period.

## What it means

A finite automaton that follows a window of cells at or above $m$, with free cells below, and checks the condition of
$K$ only before time $s + m$, has the same transitions with and without it. Conjecture (R) says that every rational
point of $K$ has an eventually periodic itinerary ([the shift model](../../findings/period-two/shift-model.md)); for
a point whose tail is the ether it needs a bound on the defect, the cells where $H^t(U)$ differs from the ether
([ether fronts](../../negative-results/period-two/ether-front-windows.md)). Such a bound cannot use $K$ through a
window of this kind at a fixed lag. This is a barrier, not progress on (R): it says where the condition of $K$ cannot act.

The kit proves the analogous facts for Rule 30 on the whole line: a right half and column 0 are realized together
exactly once (`Rule30Realization`), and Rule 30 is onto (`Rule30Equivalents.Genericity`). It has nothing on the held
map, so the statements here are new.
