---
title: A checker for the branch tree of the right-edge map is sound for every period, and its kernel evaluation at period 32 classifies the codes of period 32 and the rows that return at the speed of light after a time not divisible by 64
category: frames
problems: [1]
status: proved
lean: Rule30Open.Frames.EdgeTreeCheck
headline: [Frames.EdgeTreeCheck.dead_sound, Frames.EdgeTreeCheck.period_32, Frames.EdgeTreeCheck.rain_of_return_64]
kit: refines
kit_modules: [Rule30FrozenRuler, Rule30EdgeStaircases]
---

# A checker for the branch tree of the right-edge map is sound for every period, and its kernel evaluation at period 32 classifies the codes of period 32 and the rows that return at the speed of light after a time not divisible by 64

For an edge code $c$ (the kit's `Rule30FrozenRuler.T`, the 2-adic map $\Phi(y) = y \oplus (2y \lor 4y)$), column $e$
is $\mathrm{col}\ c\ e\ i$, bit $e$ of $\mathrm{iter}\ i\ c$ ([EdgeTree](EdgeTree.md)). A column of an $L$-periodic
code is read as the list of its first $L$ values (`seg`).

## Statement

- `dead n v w`: a Boolean function. From two consecutive columns $v$, $w$ the next column $x$ obeys
  $x(i+1) = x(i) \oplus (w(i) \lor v(i))$. Its first $L$ values are `integ (x 0) (orW w v)`, and it closes up after
  $L$ steps only if `orW w v` has even parity. `dead` returns true when the parity is odd or both candidates for $x$
  are dead with one less unit of fuel, and false when the fuel is 0.
- `dead_sound`: for every $L$ and every code with $\mathrm{iter}\ L\ c = c$, no pair of consecutive columns
  $(\mathrm{seg}(\mathrm{col}\ c\ e), \mathrm{seg}(\mathrm{col}\ c\ (e+1)))$ is dead, for any fuel.
- `period_32`: if $c(0) = 1$ and $\mathrm{iter}\ 32\ c = c$, then $c$ is `rainA` or `rainB`.
- `rain_of_return_64`: a row white right of a black cell $r$ that returns after $L$ steps moved $L$ cells right, with
  $L \bmod 64 \ne 0$, has the edge code `rainA` or `rainB` at $r$: it is a rain row. This extends
  [LightReturnClassified](LightReturnClassified.md) from $L \bmod 32 \ne 0$.

## Argument

1. **Soundness**, by induction on the fuel. Periodicity makes column $e + 2$ close up: its value at $L$ equals its value
   at 0. By `par_seg`, its value at $L$ is its value at 0 XOR the parity of the input, so the parity is even. By
   `integ_seg`, its first $L$ values are `integ` of its own first value, which is one of the two candidates the
   checker explores. Dead means that candidate is dead with less fuel, which contradicts the induction hypothesis at
   column $e + 1$.
2. **Period 32.** By `EdgeTree.rain_or_branch` a code with bit 0 black is rain or has a branch state at some column
   $j$: column $j$ alternates and column $j + 1$ equals it. Its first 32 values are then the alternating list from
   false or from true (`seg_alt`). The kernel evaluates `dead 16` at both lists of length 32 to true (`decide +kernel`,
   `dead_false` and `dead_true`; the tree has 1,055 nodes and depth 14, per
   [the light-return words](../../findings/frames/light-return-words.md)). That contradicts `dead_sound`.
3. **Rows.** $L \bmod 64 \ne 0$ means $L = 2^a q$ with $q$ odd and $a \le 5$ (`LightReturnClassified.factor_of_mod`
   for $a \le 4$, and $a = 5$ directly). The row returns after $2^a$ steps
   ([LightReturnRows](LightReturnRows.md)), so its code has period dividing 32, and `period_32` applies.

## Limits

Period 64 needs `dead 104` or more at lists of length 64: about 85,887 nodes, roughly 160 times the work of period 32.
At the speed of the period-32 evaluation (seconds) that would take tens of minutes in the kernel, so it was not
attempted. Words as Nat bit masks, which the kernel accelerates, would be the way to try it.
