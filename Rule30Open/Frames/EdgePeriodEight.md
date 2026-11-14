---
title: The only rows white to the right of their edge cell that come back after 8 steps moved 8 cells right are the white row and the rain rows
category: frames
problems: [3]
status: proved
lean: Rule30Open.Frames.EdgePeriodEight
headline: [period_eight_iff, dead_core]
kit: refines
kit_modules: [Rule30EdgeStaircases, Rule30FrozenRuler]
---

# The only rows white to the right of their edge cell that come back after 8 steps moved 8 cells right are the white row and the rain rows

On the definitions of [EdgePeriodFour](EdgePeriodFour.md): `T` is one step of Rule 30 on the edge code of a row read
leftward from its edge cell, the 2-adic map $\Phi(y) = y \oplus (2y \lor 4y)$, and $\mathrm{rainA} = 1010\dots$
($-1/3$), $\mathrm{rainB} = 11010\dots$ ($1/3$).

**Theorem** (`period_eight_iff`). For an edge code $c$ with $c(0) = 1$, $T^8 c = c$ if and only if $c = \mathrm{rainA}$
or $c = \mathrm{rainB}$.

So a row white to the right of some cell that comes back after 8 steps moved 8 cells to the right is white or a
translate of a rain row (shifts of the code and the white row as in [edge periodic
points](../../findings/frames/edge-periodic-points.md), item 2). The kit has period 2
(`Rule30EdgeStaircases.period_two_iff`), EdgePeriodFour period 4, and the finding the computation for every period not
divisible by 128; this module proves period 8 in Lean, hence every period $L$ with $16 \nmid L$ by the reduction of the
finding (a periodic point's cycle lengths are powers of two dividing $L$). The power-of-two step of that reduction is in
Lean as [EdgeOddPeriods](EdgeOddPeriods.md)`.pow_two_period` (period $2^a q$ with $q$ odd gives period $2^a$); the
remaining step, from a period dividing 4 to period 8 and the passage between rows and codes by shifts with
$c(0) = 0$, stays on paper.

## Argument

Write $b_k(i) = T^i c\,(k)$, $i \in \mathbb{Z}/8$, the column of bit $k$ around the cycle; it obeys $b_k(i + 1) = b_k(i)
\oplus (b_{k-1}(i) \lor b_{k-2}(i))$, so a column is fixed by its value at $i = 0$ and the two columns before it.

1. $b_0$ is all black, so $b_1$ alternates (`alt1`).
2. If columns $k$ and $k + 1$ alternate and are complementary, the input of column $k + 2$ is black at every step, so
   column $k + 2$ alternates (`alt_of_or`).
3. If columns $k$ and $k + 1$ alternate and are equal, the branch state $(P, P)$, then the four columns $k + 2, \dots,
   k + 5$ cannot all close up around the cycle (`dead_core`). After substituting the forced bits, the check runs over
   the phase of $P$ and the first bit of each of the four columns, 32 cases, decided by `decide`. This is the escape
   depth $T_3 = 3$ of the finding: from $(P, P)$ every walk of the column graph $G_8$ has at most 3 edges.
4. By induction from bit 1 (`main`) every column from bit 1 on alternates and complements the one before, so $c$ is
   rainA or rainB. Conversely both have period 2, so $T^8$ fixes them.

The module imports only `EdgePeriodFour` and core Lean; `#print axioms period_eight_iff` gives `propext` and
`Quot.sound`.
