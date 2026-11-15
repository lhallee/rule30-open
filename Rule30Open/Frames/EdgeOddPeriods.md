---
title: The right-edge map's only fixed point is 0, a point that returns after an odd number of steps is fixed, and every periodic point has a power-of-two least period
category: frames
problems: [3]
status: proved
lean: Rule30Open.Frames.EdgeOddPeriods
headline: [Frames.EdgeOddPeriods.fixed_point_eq_zero, Frames.EdgeOddPeriods.fixed_of_odd_period, Frames.EdgeOddPeriods.odd_period_eq_zero, Frames.EdgeOddPeriods.pow_two_period]
kit: refines
kit_modules: [Rule30FrozenRuler, Rule30EdgeStaircases, Rule30Equivalents.TFunctionCycles]
---

# The right-edge map's only fixed point is 0, a point that returns after an odd number of steps is fixed, and every periodic point has a power-of-two least period

In the frame of its right edge, one step of Rule 30 acts on the edge code $c$ of a row by the kit's
`Rule30FrozenRuler.T`, the 2-adic map $\Phi(y) = y \oplus (2y \lor 4y)$: bit $k$ of $\Phi(y)$ is
$y(k) \oplus (y(k-1) \lor y(k-2))$, with bits below 0 white. `Rule30FrozenRuler.iter n` is its $n$-th iterate. The
kit treats the period-two points (`Rule30EdgeStaircases.period_two_iff`) and
[EdgePeriodFour](EdgePeriodFour.md) the period-four points. The kit's `Rule30EdgeStaircases.no_fixed_point` shows that
no code with bit 0 black is fixed; `fixed_point_eq_zero` is the same fact for every code. The kit's equivalents
module `TFunctionCycles` already shows that the cycle length of the edge map modulo $2^n$ is a power of two
(`per_eq_two_pow`, with `iterate_mod_iff_dvd`), which gives `pow_two_period` for codes after a short limit argument
over the levels $n$. This module proves the power-of-two reduction directly on 2-adic codes, without levels, and
the reduction of every odd period to period one (`fixed_of_odd_period`, `odd_period_eq_zero`).

## Statement

- `fixed_point_eq_zero`: if $T c = c$ then every bit of $c$ is white.
- `fixed_of_odd_period`: if $\mathrm{iter}\ L\ c = c$ with $L$ odd, then $T c = c$.
- `odd_period_eq_zero`: if $\mathrm{iter}\ L\ c = c$ with $L$ odd, then every bit of $c$ is white.
- `pow_two_period`: if $\mathrm{iter}\ (2^a q)\ c = c$ with $q$ odd, then $\mathrm{iter}\ 2^a\ c = c$. So the least
  period of every periodic point is a power of two.

So no row that is white right of its edge cell, other than the white row, comes back after an odd number of steps
moved the same number of cells to the right.

## Argument

1. **Fixed points.** Bit $k + 1$ of $T c = c$ reads $c(k+1) \oplus (c(k) \lor c(k-1)) = c(k+1)$ for $k \ge 1$, and
   $c(1) \oplus c(0) = c(1)$ for $k = 0$. Either way $c(k) = 0$. No induction is needed.
2. **A column that flips by a constant** (`col_const_of_odd`). If $f(i+1) = f(i) \oplus g$ for every $i$, then
   $f(2m) = f(0)$ and $f(2m+1) = f(0) \oplus g$. So $f(L) = f(0)$ with $L$ odd forces $g = 0$, and $f$ is constant.
3. **Odd periods.** By strong induction on $k$, each column $i \mapsto \mathrm{iter}\ i\ c\ k$ is constant. Column 0
   never changes. For $k \ge 1$ the inputs of column $k$, columns $k - 1$ and $k - 2$, are constant by induction, so
   column $k$ flips by the constant $g = c(k-1) \lor c(k-2)$ (with $c(-1) = 0$) at every step. It returns at the odd
   time $L$, so by step 2 it is constant. Reading every column at time 1 gives $T c = c$, and step 1 gives $c = 0$.

4. **Powers of two** (`col_period_of_odd`, `pow_two_period`). Let $p = 2^a$. By strong induction on $k$, each
   column $f(i) = \mathrm{iter}\ i\ c\ k$ has period $p$. Its input $g$ (columns $k - 1$ and $k - 2$, or white) has
   period $p$ by induction, and $f(i+1) = f(i) \oplus g(i)$. Then $f(i + p) \oplus f(i)$ does not change with $i$, since
   one step adds $g(i + p) \oplus g(i) = 0$. So $f(i + p) = f(i) \oplus s$ for a constant $s$, and
   $f(pq) = f(0) \oplus s$ for odd $q$. Return at time $pq$ forces $s = 0$. Reading every column at time $p$ gives
   $\mathrm{iter}\ p\ c = c$.

Together with `odd_period_eq_zero` this formalizes all of Lemma 1 of
[the light-return words](../../findings/frames/light-return-words.md). The rest of that entry (the branch state, the
fertility parity, the doubling embedding and the trees) is not formalized.
