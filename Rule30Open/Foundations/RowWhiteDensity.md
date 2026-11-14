---
title: The single cell's triangle of rows 0 to n - 1 has at least 2(n - 1)(n - 2)/5 white cells, from 2B(s + 1) <= 3W(s) + 6 for consecutive rows, and 2/5 is the most any local count gives
category: foundations
problems: [2]
status: proved
lean: Rule30Open.Foundations.RowWhiteDensity
headline: [two_black_le, row_pair, triangle_white, period_five_shift]
kit: new
kit_modules: [Rule30Jen]
evidence: [computations/row_white_density.py, tests/test_row_white_density.py]
---

# The single cell's triangle of rows 0 to n - 1 has at least 2(n - 1)(n - 2)/5 white cells, from 2B(s + 1) <= 3W(s) + 6 for consecutive rows, and 2/5 is the most any local count gives

Let $B(t)$ and $W(t)$ be the numbers of black and white cells of row $t$ of the single cell on its light-cone row
$-t, \dots, t$, so $B(t) + W(t) = 2t + 1$.

**Theorem.**

1. *(Every row.)* For every row $x$, its image $y$ under Rule 30, every integer $a$ and every $n \ge 0$,
   $$2 \cdot \#\{\text{black cells of } y \text{ on } [a, a + n - 1]\} \le 3 \cdot \#\{\text{white cells of } x \text{ on } [a - 1, a + n - 2]\} + 2.$$
2. *(Consecutive rows of the single cell.)* $2B(s + 1) \le 3W(s) + 6$ for every $s \ge 0$.
3. *(The triangle.)* The rows $0, \dots, n - 1$ ($n^2$ cells) have at least $2(n - 1)(n - 2)/5$ white cells. So the
   white cells have lower density at least $2/5$ in the triangle, and in every pair of consecutive rows $s, s + 1$ one
   of the two is at least $(4s - 3)/(10s + 9)$ white.
4. *(Sharpness.)* The row $(11001)^\infty$ is mapped by Rule 30 to its shift by two cells, so every row of its orbit is
   exactly $2/5$ white and every pair $x, y$ of consecutive rows has $2 B(y) = 3 W(x)$ per period. No inequality
   between the colors of finitely many consecutive rows that holds for every row gives a white density above $2/5$.

All four parts are proved in Lean (`two_black_le`, `row_pair`, `triangle_white`, `period_five_shift` and
`period_five_count`); the per-pair consequence in part 3 is the two-line computation below.

This is a density statement about the single cell's pattern that holds unconditionally, with an explicit constant. It
is about white cells only. The matching statement for black cells is not local: the preimages of a white run include
the all-white word, and no local count gives black cells a positive density (see [black density from row
runs](../../negative-results/structure/black-density-from-row-runs.md), which reduces positive black density in the
triangle to a bound on the black runs of the rows).

## Proof

**The potential.** For a pair of adjacent cells let $\psi(0,0) = 0$, $\psi(0,1) = 1$, $\psi(1,0) = \psi(1,1) = 2$. For
all cells $a, b, c$, writing $[\cdot]$ for the indicator,
$$2\,[a \oplus (b \lor c) = 1] + \psi(b, c) \le 3\,[a = 0] + \psi(a, b).$$
The eight cases: $(a,b,c) = 000$: $0 + 0 \le 3 + 0$; $001$: $2 + 1 \le 3 + 0$; $010$: $2 + 2 \le 3 + 1$; $011$:
$2 + 2 \le 3 + 1$; $100$: $2 + 0 \le 0 + 2$; $101$: $0 + 1 \le 0 + 2$; $110$: $0 + 2 \le 0 + 2$; $111$:
$0 + 2 \le 0 + 2$ (`local_ineq`).

**Part 1.** Apply the inequality with $(a, b, c) = (x_{i-1}, x_i, x_{i+1})$, so that its left term is $2[y_i = 1]$, and
sum over $i = a, \dots, a + n - 1$. The potentials telescope:
$$2 \sum_{i} [y_i = 1] + \psi(x_{a+n-1}, x_{a+n}) \le 3 \sum_{i} [x_{i-1} = 0] + \psi(x_{a-1}, x_a)$$
(`telescope`, by induction on $n$), and $0 \le \psi \le 2$ gives part 1 (`two_black_le`).

**Part 2.** Take $x$ = row $s$, $y$ = row $s + 1$, $a = -(s + 1)$ and $n = 2s + 3$, so the window of $y$ is its whole
light-cone row. Row $s$ is white left of $-s$ (the kit's `cell_eq_false_of_lt`), so $\psi(x_{a-1}, x_a) =
\psi(x_{-s-2}, x_{-s-1}) = 0$, and the window $[-s - 2, s]$ of $x$ is the light-cone row $[-s, s]$ plus two white
cells. So $2B(s + 1) \le 3(W(s) + 2)$ (`row_pair`).

**Part 3.** Write $S(n) = \sum_{s < n} W(s)$. With $B(s + 1) = 2s + 3 - W(s + 1)$, part 2 reads
$2(2s + 3) \le 3W(s) + 2W(s + 1) + 6$. Summing over $s = 0, \dots, n - 2$ and using $\sum_{s \le n-2} (2s + 3) =
n^2 - 1$:
$$2(n^2 - 1) \le 3 S(n - 1) + 2 \bigl(S(n) - W(0)\bigr) + 6(n - 1) \le 5 S(n) + 6(n - 1),$$
so $5 S(n) \ge 2n^2 - 6n + 4 = 2(n - 1)(n - 2)$ (`triangle_white`). For the pair: if row $s$ is less than $\alpha$
white and row $s + 1$ is less than $\alpha$ white, then $W(s) < \alpha(2s + 1)$ and $B(s + 1) > (1 - \alpha)(2s + 3)$,
and part 2 gives $2(1 - \alpha)(2s + 3) < 3\alpha(2s + 1) + 6$, that is $\alpha > (4s - 3)/(10s + 9)$.

**Part 4.** $(11001)^\infty \mapsto (00111)^\infty$, the same row shifted by two cells, cell by cell modulo 5
(`period_five_shift`); each period has two white cells (`period_five_count`). Any inequality valid for every
configuration, with boundary terms bounded independently of the window, holds for this orbit, where every row and
every space-time window of whole periods is exactly $2/5$ white. Part 1 is tight there: $2 \cdot 3 = 3 \cdot 2$ per
period, as it is for the stripe $(100)^\infty \mapsto 1^\infty$.

## Remarks

- The run form of part 1: a black run of $y$ of length $m$ on $[u, v]$ forces $x$ on $[u - 1, v + 1]$ to be one of the
  four words of the stripe $(100)^\infty$ (backward from the right, $x_{i-1} = 1 \oplus (x_i \lor x_{i+1})$ is 1 exactly
  after $00$), and $x$ has at least $\lfloor 2(m + 1)/3 \rfloor$ white cells on $[u - 1, v]$, with equality reached for
  every $m$ (`run_white_bound`, and the test that enumerates the preimages of $1^m$ for $m \le 10$).
- On the single cell, the white fraction of the triangle is $0.5004$ to $0.5196$ at $n = 100, 300, 1000, 2000, 3000$
  against the bound's $0.382$ to $0.399$, and the least slack of part 2 over $s < 3000$ is one cell
  (`python -m computations.row_white_density --n 3000`).
- Rule 90 has a white density tending to 1 in the triangle and Rule 30's black density is not covered here, so part 3
  is consistent with the planner's remark that a black lower bound must use the OR: white cells pay for black cells
  locally, black cells do not pay for white ones.

## Reproduce

    lake build Rule30Open.Foundations.RowWhiteDensity
    python -m computations.row_white_density --n 3000      # the triangle counts to row 3,000, about 2 s
    python -m pytest tests/test_row_white_density.py
