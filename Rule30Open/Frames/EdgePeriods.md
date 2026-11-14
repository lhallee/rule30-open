---
title: For every period not divisible by 32, the only rows white to the right of their edge cell that come back moved at the speed of light are the white row and the rain rows, which need an even period
category: frames
problems: [3]
status: proved
lean: Rule30Open.Frames.EdgePeriods
headline: [Frames.EdgePeriods.period_iff, Frames.EdgePeriods.T_eq]
kit: refines
kit_modules: [Rule30FrozenRuler, Rule30EdgeStaircases]
---

# For every period not divisible by 32, the only rows white to the right of their edge cell that come back moved at the speed of light are the white row and the rain rows, which need an even period

On the kit's edge map `Rule30FrozenRuler.T` (one step of Rule 30 on the edge code of a row, read leftward from its edge
cell; the 2-adic map $\Phi(y) = y \oplus (2y \lor 4y)$) and its iterate `Rule30FrozenRuler.iter`:

**Theorem** (`period_iff`). Let $c$ be an edge code with $c(0) = 1$, and $L = 2^a q$ with $q$ odd and $a \le 4$.
Then `iter L c = c` if and only if $a \ge 1$ and $c$ is $\mathrm{rainA} = 1010\dots$ ($-1/3$) or $\mathrm{rainB} =
11010\dots$ ($1/3$).

Every $L \ge 1$ not divisible by 32 has this form. So for odd $L$ no edge code with a black edge cell is fixed by
`iter L`, and for even $L$ not divisible by 32 exactly the two rain codes are, which have least period exactly 2 ($T$
swaps them). In terms of rows: a row white to the right of some cell that comes back after $L$ steps moved $L$ cells
to the right, $32 \nmid L$, is white or a translate of a rain row, and the rain rows only for even $L$.

## Argument

- `EdgeOddPeriods.pow_two_period`: `iter (2^a * q) c = c` with $q$ odd gives `iter (2^a) c = c`.
- $a = 0$: $T c = c$ makes $c$ white (`EdgeOddPeriods.fixed_point_eq_zero`), against $c(0) = 1$.
- $a = 1, 2$: `iter 4 c = c`, and `EdgePeriodFour.period_four_iff`.
- $a = 3$: `EdgePeriodEight.period_eight_iff`; $a = 4$: `EdgePeriodSixteen.period_sixteen_iff`.
- `T_eq`: the map restated in `EdgePeriodFour` is the kit's `T` (the definitions agree case by case).
- Conversely $T$ swaps rainA and rainB (`EdgePeriodFour.T_rainA`, `T_rainB`), so `iter 2` fixes them and so does
  `iter (2m)` (`iter_mul_of_period`).

Core Lean only; `#print axioms period_iff` gives `propext` and `Quot.sound`. Periods divisible by 32 and not by 128 are
covered only by the exact computation of [edge periodic points](../../findings/frames/edge-periodic-points.md); the
classification for every period is a conjecture ([the routes](../../negative-results/frames/edge-periodic-classification.md)).
