---
title: A row white right of some cell that comes back after an odd number of steps, moved as many cells right, is white, and one that comes back after 2^a q steps with q odd already comes back after 2^a
category: frames
problems: [3]
status: proved
lean: Rule30Open.Frames.LightReturnRows
headline: [Frames.LightReturnRows.odd_return_white, Frames.LightReturnRows.pow_two_return, Frames.LightReturnRows.code_evolve]
kit: refines
kit_modules: [Rule30FrozenRuler, Rule30EdgeStaircases]
---

# A row white right of some cell that comes back after an odd number of steps, moved as many cells right, is white, and one that comes back after 2^a q steps with q odd already comes back after 2^a

This module states [EdgeOddPeriods](EdgeOddPeriods.md) for rows. A row *returns at the speed of light after $L$
steps* when $\mathrm{evolve}\ init\ L\ (x + L) = init\ x$ for every cell $x$. That is, the pattern comes back shifted
$L$ cells to the right, the most a right edge can move in $L$ steps.

## Statement

Let $init$ be white right of a cell $r$ ($init\ p = 0$ for $p > r$). The cell $r$ need not be black.

- `code_evolve`: at time $t$ the row is white right of $r + t$, and its code read from $r + t$ (bit $k$ is the cell
  $k$ places left) is $\mathrm{iter}\ t$ of its code read from $r$, where $\mathrm{iter}$ iterates the kit's edge map
  `Rule30FrozenRuler.T`, $\Phi(y) = y \oplus (2y \lor 4y)$.
- `odd_return_white`: if the row returns at the speed of light after an odd number $L$ of steps, it is white.
- `pow_two_return`: if it returns after $2^a q$ steps with $q$ odd, it already returns after $2^a$ steps.

So a nonzero row white right of some cell can return at the speed of light only after a power-of-two number of steps.
The kit's `Rule30EdgeStaircases.period_two_iff` and [EdgePeriodFour](EdgePeriodFour.md) find the rain rows at periods
2 and 4. Rows with black cells arbitrarily far right do return after 12, 15 or 17 steps
([LightLikeEntropy](../RandomRows/LightLikeEntropy.md)), so the white right side is needed.

## Argument

1. **The bridge** (`code_evolve`), by induction on $t$. Cells beyond $r + t + 1$ at time $t + 1$ read only white cells.
   At the edge cell $r + t + 1$ the update reads the cell $r + t$ and two white cells. At $k$ cells left of it, it
   reads the cells $k + 1$, $k$ and $k - 1$ places left of $r + t$. Together these are $T$ on the code. This is the
   kit's `Rule30FrozenRuler.edge_evol` for `evolve`, without its hypothesis that the edge cell is black.
2. **A return is a periodic code.** Read at $r + L$, the row at time $L$ has code $\mathrm{iter}\ L\ c$, where $c$ is
   the code read from $r$. The return makes this code $c$ itself (`iter_code_of_return`).
3. **Odd returns.** `EdgeOddPeriods.odd_period_eq_zero` makes $c$ white. That covers the cells $x \le r$, and the
   cells $x > r$ are white by hypothesis.
4. **Power-of-two part.** `EdgeOddPeriods.pow_two_period` (for codes, the kit's `TFunctionCycles.per_eq_two_pow` gives
   the same power-of-two cycle length modulo every $2^n$) gives $\mathrm{iter}\ 2^a\ c = c$. By the bridge at
   $t = 2^a$, the row at time $2^a$ agrees with $init$ moved $2^a$ cells right at every cell $x + 2^a$ with $x \le r$.
   For $x > r$ both sides are white.
