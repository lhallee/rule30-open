---
title: Black cells of the single cell's triangle number at least 2n^2/(M_n + 3), M_n the longest black run of a row before time n, but no local count bounds M_n, and every count valid for all rows gives black cells density 0
category: structure
problems: [2]
status: negative
kind: dead-end
evidence: [computations/row_white_density.py, tests/test_row_white_density.py]
---

# Black cells of the single cell's triangle number at least 2n^2/(M_n + 3), M_n the longest black run of a row before time n, but no local count bounds M_n, and every count valid for all rows gives black cells density 0

**Question.** [RowWhiteDensity](../../Rule30Open/Foundations/RowWhiteDensity.md) proves that the white cells of the
single cell's triangle (rows $0$ to $n - 1$ on their light-cone rows, $n^2$ cells) number at least
$2(n - 1)(n - 2)/5$, by a count that holds for every row. Does a count of the same kind give the black cells a positive
density, $A(n) \ge \delta n^2$ with $A(n)$ the black cells of the triangle?

**Answer.** Not unconditionally. The white cells of the triangle are covered by white triangles, each started under a
black run of the row above, which gives
$$A(n) \ge \frac{2 n^2}{M_n + 3},$$
with $M_n$ the longest black run of the rows $0, \dots, n - 2$ (proved on paper below; checked to $n = 3000$). So
positive density of black cells follows from bounded black runs in the rows, and density $c / \log n$ from runs of
length $O(\log n)$. No bound on $M_n$ better than the trivial $2n - 1$ is known, the steps where a local argument for
one stop are below, and no count that holds for every row can give black cells a positive density at all.

## The white triangles (proved on paper)

Inside the light cone every maximal white run of row $s$ is bordered by black cells, since the cells $\pm s$ are black.
Let $[u, v]$ be one, of length $k = v - u + 1$.

1. *Preimages of a white run.* Row $s - 1$ on $[u - 1, v + 1]$ is one of $0^{k+2}$, $1^k 0 1$, $1^{k+1} 0$, $1^{k+2}$.
   Read from the right, $x_{i-1} = x_i \lor x_{i+1}$ for $i = v, \dots, u$: from $00$ every cell is 0, from $01$, $10$
   or $11$ every cell further left is 1.
2. *Continuation.* If row $s - 1$ is $0^{k+2}$ there, its maximal white run $[a, b] \supseteq [u - 1, v + 1]$ lies inside
   the cone, so $x_{a-1} = x_{b+1} = 1$; row $s$ is black at $a$ ($1 \oplus (0 \lor 0)$) and at $b$
   ($0 \oplus (0 \lor 1)$) and white on $[a + 1, b - 1]$, so $[u, v] = [a + 1, b - 1]$. Every white run of length at
   least 3 has exactly one continuation, shorter by one cell at each end; runs of length 1 and 2 have none.
3. *Newborn runs.* Otherwise row $s - 1$ is black on $[u - 1, v - 1]$, a black run of length at least $k$, and two
   newborn runs of row $s$ sit under two different black runs of row $s - 1$: in the cases $1^{k+1}0$ and $1^{k+2}$ the
   cell $v + 1$ of row $s$ is black only if $x_{v+1} = x_{v+2} = 0$, and in the case $1^k 0 1$ the run ends at $v - 1$.
4. *Area.* A newborn run of length $k$ starts a chain of runs of lengths $k, k - 2, k - 4, \dots$, a white triangle of
   $T(k) \le (k + 1)^2/4$ cells, and every white cell of the triangle lies in exactly one chain.

So the white cells of rows $< n$ number at most $\sum_{r < n - 1} \sum_R T(|R|)$, over the black runs $R$ of row $r$,
and with $T(m) \le (M + 1)(m + 1)/4 \le (M + 1) m / 2$ this is at most $(M_n + 1) A(n) / 2$. Then
$n^2 \le A(n) (M_n + 3)/2$.

On the single cell, `python -m computations.row_white_density --n 3000` gives $M_n = 15, 24, 25, 27, 29$ at
$n = 100, 300, 1000, 2000, 3000$, so the bound is $A(n) \ge 1{,}111, 6{,}667, 71{,}429, 266{,}667, 562{,}500$ against
$5{,}196, 45{,}477, 501{,}718, 2{,}003{,}370, 4{,}507{,}370$; the sum of $T$ over the runs bounds the white cells at every
$n$ checked, and of the white runs of rows 1 to 599 every one is a continuation (21,890) or newborn (68,849).

## Where it stops

- **Every count valid for all rows gives black density 0.** The all-white word is a preimage of every white run, and the
  all-white row is an orbit. So an inequality between the colors of finitely many consecutive rows that holds for
  every row bounds black cells below by boundary terms only. White cells are different: a black cell of the image over
  a black cell needs two white cells to its right, which is the whole content of
  [RowWhiteDensity](../../Rule30Open/Foundations/RowWhiteDensity.md). A positive density of black cells has to use the
  seed, for example through the edges $\pm t$ being black, which only gives $A(n) \ge 2n - 1$.
- **The rows above a long black run are not contradictory at any finite depth.** A black run of length $m$ in row $s$
  forces row $s - 1$ to the stripe $(100)^\infty$ on $m + 2$ cells (the four preimages of $1^m$), row $s - 2$ to
  $(110)^\infty$, and further up rows that are, away from the right end of the window, spatially periodic words
  determined by two cells per row at the right (the backward step $x_{i-1} = y_i \oplus (x_i \lor x_{i+1})$ is
  deterministic leftward). Rule 30 is onto, so every finite word has preimages of every depth, and no window of bounded
  depth above the run is inconsistent. A contradiction can only come from row 0.
- **Charging the white triangle to the rows above it fails.** Over the run, a white run of length $L$ in the row $h$
  above would leave the white triangle below it, of width $L - 2h$ at row $s$, inside the black run; so those rows have
  white runs of length at most $2h + 1$ and black density at least about $1/(2h + 2)$. Summed over $h \le m/2$ this gives
  about $(m/2) \ln m$ black cells above the run against the $T(m - 1) \approx m^2/4$ white cells of the triangle below
  it (heuristic count: the windows of different runs also overlap). A discharging rule that sends each white cell of a
  triangle to the black cells above its run with bounded load therefore needs the black runs of the rows bounded.

## What would close it

A bound $M_n = O(1)$ gives positive black density in the triangle, and $M_n = o(n)$ gives $A(n)/n \to \infty$ faster
than the trivial $2n - 1$. The row runs here are horizontal; the kit's linear bounds are for the runs of the center column, a vertical
statement, and they do not transfer.
