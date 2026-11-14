---
title: The only rows white to the right of their edge cell that come back after 16 steps moved 16 cells right are the white row and the rain rows
category: frames
problems: [3]
status: proved
lean: Rule30Open.Frames.EdgePeriodSixteen
headline: [period_sixteen_iff, dead_core]
kit: refines
kit_modules: [Rule30EdgeStaircases, Rule30FrozenRuler]
---

# The only rows white to the right of their edge cell that come back after 16 steps moved 16 cells right are the white row and the rain rows

On the definitions of [EdgePeriodFour](EdgePeriodFour.md) (`T`, the edge map $\Phi(y) = y \oplus (2y \lor 4y)$; rainA
$= -1/3$, rainB $= 1/3$):

**Theorem** (`period_sixteen_iff`). For an edge code $c$ with $c(0) = 1$, $T^{16} c = c$ if and only if $c =
\mathrm{rainA}$ or $c = \mathrm{rainB}$.

With the reduction of [edge periodic points](../../findings/frames/edge-periodic-points.md) (item 2: a periodic point's
cycle lengths are powers of two dividing its period, and $\Phi(2y) = 2\Phi(y)$), this gives in Lean-checked form, up to
that paper reduction, the classification for every period $L$ with $32 \nmid L$: a row white to the right of some cell
that comes back after $L$ steps moved $L$ cells right is white or a translate of a rain row.

## Argument

The argument of [EdgePeriodEight](EdgePeriodEight.md) with columns of length 16. Columns from bit 1 on alternate as long
as consecutive ones are complementary (`alt_of_or`); the other choice is the branch state $(P, P)$, two equal
alternating columns, and `dead_core` shows that no five further columns close up around the cycle of 16 steps from it.
After substituting the forced bits the check runs over the phase of $P$ and the first bit of each of the five columns,
64 cases, decided by `decide`. This is the escape depth $T_4 = 4$ of the finding: from $(P, P)$ every walk of $G_{16}$
has at most 4 edges. `#print axioms period_sixteen_iff` gives `propext` and `Quot.sound`.

The same generator would need 15 further columns at period 32 ($T_5 = 14$) and 104 at period 64, so the method stops
being cheap there; the general classification is a conjecture ([the routes](../../negative-results/frames/edge-periodic-classification.md)).
