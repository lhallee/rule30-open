---
title: The single cell's triangle of rows 0 to n - 1 has at least 2(n - 1)(n - 2)/5 white cells, from 2B(s + 1) <= 3W(s) + 6 for consecutive rows, and no count valid for every row with bounded boundary terms gives more than 2/5
category: foundations
problems: [2]
status: proved
lean: Rule30Open.Foundations.RowWhiteDensity
headline: [RowWhiteDensity.two_black_le, RowWhiteDensity.row_pair, RowWhiteDensity.triangle_white, RowWhiteDensity.strip_white, RowWhiteDensity.pair_white, RowWhiteDensity.period_five_shift]
kit: new
kit_modules: [Rule30Jen]
evidence: [computations/row_white_density.py, tests/test_row_white_density.py]
---

# The single cell's triangle of rows 0 to n - 1 has at least 2(n - 1)(n - 2)/5 white cells, from 2B(s + 1) <= 3W(s) + 6 for consecutive rows, and no count valid for every row with bounded boundary terms gives more than 2/5

Let $B(t)$ and $W(t)$ be the numbers of black and white cells of row $t$ of the single cell on its light-cone row
$-t, \dots, t$, so $B(t) + W(t) = 2t + 1$.

**Theorem.**

1. *(Every row.)* For every row $x$, its image $y$ under Rule 30, every integer $a$ and every $n \ge 0$,
   $$2 \cdot \#\{\text{black cells of } y \text{ on } [a, a + n - 1]\} \le 3 \cdot \#\{\text{white cells of } x \text{ on } [a - 1, a + n - 2]\} + 2.$$
2. *(Consecutive rows of the single cell.)* $2B(s + 1) \le 3W(s) + 6$ for every $s \ge 0$.
3. *(The triangle.)* The rows $0, \dots, n - 1$ ($n^2$ cells) have at least $2(n - 1)(n - 2)/5$ white cells. So the
   white cells have lower density at least $2/5$ in the triangle, and in every pair of consecutive rows $s, s + 1$ one
   of the two is at least $4s/(10s + 9)$ white.
4. *(Sharpness.)* The row $(11001)^\infty$ is mapped by Rule 30 to its shift by two cells, so every row of its orbit is
   exactly $2/5$ white and every pair $x, y$ of consecutive rows has $2 B(y) = 3 W(x)$ per period. So no inequality
   between the colors of finitely many consecutive rows that holds for every row, with boundary terms bounded
   independently of the window, gives a lower white density above $2/5$. This says nothing about the single cell's
   own density, which is about $1/2$ up to $n = 3000$ (Remarks).

Parts 1 to 3 and the orbit of part 4 are proved in Lean (`two_black_le`, `row_pair`, `triangle_white`,
`period_five_shift` and `period_five_count`). The per-pair consequence in part 3 and the optimality statement in part 4
are consequences on paper, below.

This is a density statement about the single cell's pattern that holds unconditionally, with an explicit constant. It
is about white cells only. The matching statement for black cells is not local: the preimages of a white run include
the all-white word, and no local count gives black cells a positive density (see [black density from row
runs](../../negative-results/structure/black-density-from-row-runs.md), which reduces positive black density in the
triangle to a bound on the black runs of the rows).

## Vertical strips, for every orbit

Write $W_{[a, a+J-1]}(t)$ for the white cells of the strip of columns $a, \dots, a + J - 1$ at time $t$, in any orbit
$x_0, x_1 = F(x_0), \dots$ of Rule 30 (no hypothesis on the initial row), and $W_i(n)$ for the white cells of column $i$
at the times $0, \dots, n - 1$.

5. *(A strip, one step.)* For every row $x$ and every strip of $J$ cells, $2\,B(F(x)) \le 3\,W(x) + 2$ on that strip
   (`strip_ineq`). The constant 2 is the least possible for every $J$ from 1 to 8 (exhaustion over the rows of $J + 2$
   cells, `strip_slack`).
6. *(A strip, summed.)* $3 W_{[a,a+J-1]}(t) + 2 W_{[a,a+J-1]}(t + 1) \ge 2J - 2$ for every $t$, so the strip has at
   least $(2J - 2)n/5$ white cells at the times $0, \dots, n$ (`strip_white`): lower white density at least
   $(2J - 2)/(5J)$, which is $4/15$ for the three columns $-1, 0, 1$ and tends to $2/5$.
7. *(Two adjacent columns.)* If cells $a$ and $a + 1$ are black at time $t$, cell $a + 1$ is white at time $t + 1$
   ($1 \oplus (1 \lor \cdot) = 0$, `pair_rule`). So $W_a(n) + W_{a+1}(n) + W_{a+1}(n + 1) \ge n$ (`pair_white`), that
   is $N_{a+1}(n) \le W_a(n) + W_{a+1}(n + 1)$ with $N$ the black cells of a column, and the two columns have lower
   white density at least $1/4$, better than part 6's $1/5$ at $J = 2$.

Parts 5 to 7 are in Lean. Proof of part 5: the telescoped count of part 1 with $n = J$ moves the white window one cell
left; the two boundary terms are $3[x_{a-1} = 0] + \psi(x_{a-1}, x_a)$ and $3[x_{a+J-1} = 0] + \psi(x_{a+J-1}, x_{a+J})$,
and $3[p = 0] + \psi(p, q)$ lies between 2 and 4 (`edge_bounds`), so they cost at most 2. Part 6 sums part 5 with
$B = J - W$ as in part 3.

For small $J$ there are better bounds. [PairWhiteDensity](PairWhiteDensity.md) proves, for every orbit, that two
adjacent columns have lower white density at least $5/18$ and three adjacent columns at least $1/3$, which is sharp.
These beat part 6 at $J = 3$ ($4/15$) and part 7 ($1/4$). So parts 6 and 7 matter as the general form
$(2J - 2)/(5J)$ for $J \ge 4$ and as a two-column count of a different shape. The pointwise step of part 7 is, for the
single cell, the kit's `Rule30MaskedJen.left_of_black` at $i = a + 1$, which
[ColumnTransfer](../Columns/ColumnTransfer.md) uses as its pointwise step. Its `transfer_right_white`,
$N_{i+1}(n) \le W_{i-1}(n) + W_i(n + 1)$, rearranges to $W_{i-1}(n) + W_i(n + 1) + W_{i+1}(n) \ge n$, a white lower
bound on three columns of the single cell. Part 7 is the transfer for the column offset $a, a + 1$, summed, and it
holds for every orbit.

On the spatially periodic orbits of period at most 12, the least white fraction of a strip is 0 for $J = 1$ (the fixed
point $(01)^\infty$), $1/3$ for $J = 2$ and $J = 3$, and $2/5$ for $J = 4, 5, 6$ (`periodic_strip_min`), so parts 6
and 7 are not sharp for small $J$.

*What this does not give.* Nothing for the center column alone, since the fixed point $(01)^\infty$ has a column that
is black at every time, and nothing for black cells, whose density no count valid for every orbit can bound below.

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
and part 2 gives $2(1 - \alpha)(2s + 3) < 3\alpha(2s + 1) + 6$, that is $4s < \alpha(10s + 9)$. So one of the two rows
is at least $4s/(10s + 9)$ white.

**Part 4.** $(11001)^\infty \mapsto (00111)^\infty$, the same row shifted by two cells, cell by cell modulo 5
(`period_five_shift`); each period has two white cells (`period_five_count`). Any inequality valid for every
configuration, with boundary terms bounded independently of the window, holds for this orbit, where every row and
every space-time window of whole periods is exactly $2/5$ white. Part 1 is tight there: $2 \cdot 3 = 3 \cdot 2$ per
period, as it is for the stripe $(100)^\infty \mapsto 1^\infty$.

## Remarks

- The run form of part 1: a black run of $y$ of length $m$ on $[u, v]$ has four preimages $x$ on $[u - 1, v + 1]$, and
  on $[u - 1, v]$ ($m + 1$ cells) each is a word of the stripe $(100)^\infty$; the cell $x_{v+1}$ is free when
  $x_v = 1$, so one of the four ends in $11$ (backward from the right, $x_{i-1} = 1 \oplus (x_i \lor x_{i+1})$ is 1
  exactly after $00$). So $x$ has at least $\lfloor 2(m + 1)/3 \rfloor$ white cells on $[u - 1, v]$, with equality reached for
  every $m$ (`run_white_bound`, and the test that enumerates the preimages of $1^m$ for $m \le 10$).
- On the single cell, the white fraction of the triangle is $0.480$, $0.495$, $0.498$, $0.499$ and $0.499$ at $n = 100, 300, 1000, 2000, 3000$
  against the bound's $0.388$ to $0.400$; the slack $3W(s) + 6 - 2B(s + 1)$ is 0 at $s = 0, 1, 2$ and at least 1 for $3 \le s < 2999$
  (`python -m computations.row_white_density --n 3000`).
- The asymmetry is the OR. Rule 90 has black density tending to 0 in its triangle ($3^k$ black cells in $4^k$), so a
  lower bound for black cells has to use the OR, and part 1 is the place where Rule 30's OR acts: a black cell $y_i$
  with $x_{i-1}$ black needs $x_i = x_{i+1} = 0$. White cells pay for black cells locally; black cells do not pay
  for white ones.

## Reproduce

    lake build Rule30Open.Foundations.RowWhiteDensity
    python -m computations.row_white_density --n 3000      # the triangle counts and the strips, about 1 min
    python -m pytest tests/test_row_white_density.py
