---
title: The right-edge map's only fixed point is 0, and a point that returns after an odd number of steps is fixed, so it is 0
category: frames
problems: [1]
status: proved
lean: Rule30Open.Frames.EdgeOddPeriods
headline: [fixed_point_eq_zero, fixed_of_odd_period, odd_period_eq_zero]
kit: refines
kit_modules: [Rule30FrozenRuler, Rule30EdgeStaircases]
---

# The right-edge map's only fixed point is 0, and a point that returns after an odd number of steps is fixed, so it is 0

In the frame of its right edge, one step of Rule 30 acts on the edge code $c$ of a row by the kit's
`Rule30FrozenRuler.T`, the 2-adic map $\Phi(y) = y \oplus (2y \lor 4y)$: bit $k$ of $\Phi(y)$ is
$y(k) \oplus (y(k-1) \lor y(k-2))$, with bits below 0 white. `Rule30FrozenRuler.iter n` is its $n$-th iterate. The
kit treats the period-two points (`Rule30EdgeStaircases.period_two_iff`) and
[EdgePeriodFour](EdgePeriodFour.md) the period-four points. The kit's `Rule30EdgeStaircases.no_fixed_point` shows that
no code with bit 0 black is fixed. `fixed_point_eq_zero` is the same fact for every code, and the reduction of every
odd period to period one is new.

## Statement

- `fixed_point_eq_zero`: if $T c = c$ then every bit of $c$ is white.
- `fixed_of_odd_period`: if $\mathrm{iter}\ L\ c = c$ with $L$ odd, then $T c = c$.
- `odd_period_eq_zero`: if $\mathrm{iter}\ L\ c = c$ with $L$ odd, then every bit of $c$ is white.

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

## What remains on paper

[The light-return words](../../findings/frames/light-return-words.md) state a stronger form: the least period of every
periodic point is a power of two. The proof is the same induction with "constant" replaced by "periodic with period
$2^j$": a column whose inputs have period $2^j$ flips by a fixed parity over each block of $2^j$ steps, so its period
divides $2^{j+1}$. Only the odd case is formalized here. It is what excludes odd periods, and with the power-of-two
statement it gives the same conclusion for every period that is not a power of two.
