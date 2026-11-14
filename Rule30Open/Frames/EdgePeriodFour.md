---
title: The only rows white to the right of their edge cell that come back after 4 steps moved 4 cells right are the white row and the rain rows
category: frames
problems: [3]
status: proved
lean: Rule30Open.Frames.EdgePeriodFour
headline: [period_four_iff, dead_core]
kit: refines
kit_modules: [Rule30EdgeStaircases, Rule30FrozenRuler]
---

# The only rows white to the right of their edge cell that come back after 4 steps moved 4 cells right are the white row and the rain rows

Read a row of Rule 30 that is white to the right of a black cell leftward from that cell: bit $k$ of its edge code $c$
is the cell $k$ places to the left. One step moves the edge cell one place right and acts on the code by $T c(0) =
c(0)$, $T c(1) = c(1) \oplus c(0)$, $T c(k + 2) = c(k + 2) \oplus (c(k + 1) \lor c(k))$, the 2-adic map $\Phi(y) = y
\oplus (2y \lor 4y)$ (the kit's `Rule30FrozenRuler.T`, restated in the module so that it needs only core Lean).

**Theorem** (`period_four_iff`). For an edge code with $c(0) = 1$, $T^4 c = c$ if and only if $c$ is $\mathrm{rainA} =
1010\dots$ (the 2-adic integer $-1/3$) or $\mathrm{rainB} = 11010\dots$ ($1/3$).

So a row with a white right half that comes back after 4 steps moved 4 cells to the right is white or a translate of a
rain row, and the rain rows come back after 2 steps already. The kit has the same statement for $T^2$
(`Rule30EdgeStaircases.period_two_iff`), which this extends to period 4. Modulo 16 every odd code satisfies $T^4 c
\equiv c$ (all 8 odd residues, against 8 of the 16 modulo 32; `tests/test_edge_periodic_points.py`), so the content is in the
higher bits. [Edge periodic points](../../findings/frames/edge-periodic-points.md) extends it by computation to every period not divisible
by 128.

## Argument

Write $b_k(i) = T^i c\,(k)$ for $i \in \mathbb{Z}/4$, the column of bit $k$ around the cycle. The step rule reads
$b_k(i + 1) = b_k(i) \oplus (b_{k-1}(i) \lor b_{k-2}(i))$, so a column exists only if its input $b_{k-1} \lor b_{k-2}$
has an even number of black cells in the four steps, and then it is fixed up to complement.

1. $b_0$ is all black, so $b_1$ flips at every step: column 1 alternates (`alt1`).
2. If columns $k$ and $k + 1$ alternate and are complementary, the input of column $k + 2$ is black at every step, so
   column $k + 2$ alternates (`alt_of_or`, and the case $k = 0$ in `main`).
3. If columns $k$ and $k + 1$ alternate and are equal, say $a, \bar a, a, \bar a$, the input of column $k + 2$ is that
   column, with two black cells, so column $k + 2$ is $x, x \oplus a, \dots$, which takes each value twice in a row;
   then the input $b_{k+2} \lor b_{k+1}$ of column $k + 3$ has three black cells, and no column $k + 3$ closes up
   around the cycle (`dead_core`, a check of the eight values of $a$, $x$ and the start of column $k + 3$;
   `not_equal_alt`).
4. By induction from $k = 1$ (`main`), every column from bit 1 on alternates and is the complement of the one before,
   so $c(k + 1) = \overline{c(k)}$ for $k \ge 1$, and $c$ is rainA or rainB as $c(1)$ is 0 or 1. Conversely $T$ swaps
   the two (`T_rainA`, `T_rainB`).

In the language of the finding, step 3 is the dead branch of the column graph $G_4$: it lasts one level, which is the
escape depth $T_2 = 1$.
