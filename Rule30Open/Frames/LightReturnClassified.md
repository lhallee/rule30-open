---
title: A row white right of some cell that comes back moved at the speed of light after a number of steps not divisible by 32 is white or a rain row ending at its rightmost black cell
category: frames
problems: [1]
status: proved
lean: Rule30Open.Frames.LightReturnClassified
headline: [white_or_rain_of_return, rain_rows_of_return, rain_of_return_mod, rain_of_return, frozen_T_eq]
kit: refines
kit_modules: [Rule30FrozenRuler, Rule30EdgeStaircases]
---

# A row white right of some cell that comes back moved at the speed of light after a number of steps not divisible by 32 is white or a rain row ending at its rightmost black cell

## Statement

`rain_of_return`: let $init$ be white right of the cell $r$, with $init\ r = 1$. Suppose that for some $a \le 4$ and
odd $q$, $\mathrm{evolve}\ init\ (2^a q)\ (x + 2^a q) = init\ x$ for every cell $x$: the row comes back after
$2^a q$ steps, moved $2^a q$ cells to the right. Then its edge code at $r$ (bit $k$ is the cell $k$ places left of
$r$) is `rainA` $= 1 0 1 0 \ldots$ or `rainB` $= 1 1 0 1 0 \ldots$, the 2-adic numbers $-1/3$ and $1/3$. So the row
is one of the two rain rows ending at $r$. Every return time $L$ not divisible by 32 has this form.

`rain_of_return_mod`: the same with the hypothesis $L \bmod 32 \ne 0$ and
$\mathrm{evolve}\ init\ L\ (x + L) = init\ x$. `factor_of_mod` writes such an $L$ as $2^a q$ with $a \le 4$ and
$q$ odd, by five cases on the residue of $L$.

`rain_rows_of_return`: under the same hypotheses, explicitly, either $init(r - k) = [k \text{ even}]$ for every
$k \ge 0$, or $init(r - k) = [k = 0 \text{ or } k \text{ odd}]$ for every $k \ge 0$.

`white_or_rain_of_return`: without the black edge cell. If $init$ is white right of some cell $r$ and returns after
$L$ steps moved $L$ cells, with $L \bmod 32 \ne 0$, then either $init$ is white, or it has a rightmost black cell
$r'$ (`rightmost_black`) and its code at $r'$ is `rainA` or `rainB`.

`frozen_T_eq`: the kit's edge map `Rule30FrozenRuler.T` equals the map `EdgePeriodFour.T` restated in
[EdgePeriodFour](EdgePeriodFour.md), so the theorems about either one apply to both.

## Argument

1. By [LightReturnRows](LightReturnRows.md) (`pow_two_return`), the row already comes back after $2^a$ steps. By
   `iter_code_of_return`, its code $c$ at $r$ satisfies $\mathrm{iter}\ 2^a\ c = c$.
2. Since $2^a$ divides 16 (`iter_mul_of`, with $2^a \cdot 2^{4-a} = 16$), $\mathrm{iter}\ 16\ c = c$.
3. Bit 0 of $c$ is $init\ r = 1$, so [EdgePeriodSixteen](EdgePeriodSixteen.md) (`period_sixteen_iff`) gives
   $c \in \{\mathrm{rainA}, \mathrm{rainB}\}$, after `frozen_T_eq` rewrites the kit's map as theirs.

4. `rightmost_black`: a row white right of $s$ with a black cell $s - n$ has a rightmost black cell, by induction on
   $n$. If $s$ is black it is that cell; otherwise the row is white right of $s - 1$.

When $a = 0$ the hypothesis of `rain_of_return` is impossible ([LightReturnRows](LightReturnRows.md),
`odd_return_white`), and the theorem holds vacuously. Return times divisible by 32 are open here: they need the
codes of period 32 and beyond, which no module classifies.
