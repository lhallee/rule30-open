---
title: Every partial row that fixes the center cell fixes the leftmost cone cell, t - 1 cells suffice for t ≥ 9, and t - 1 is the least for 9 ≤ t ≤ 15 by computation
category: complexity
problems: [3]
status: proved
lean: Rule30Open.Complexity.MinCertificate
headline: [constOn_fixes_left, screening_even_free, stripe_center, stripe_constOn, stripeRow_isSome]
kit: new
kit_modules: [Rule30ZeroBoundaryStripe]
evidence: [computations/min_certificate.py, tests/test_min_certificate.py]
---

# Every partial row that fixes the center cell fixes the leftmost cone cell, t - 1 cells suffice for t ≥ 9, and t - 1 is the least for 9 ≤ t ≤ 15 by computation

Write $c_t(x)$ for the center cell after $t$ steps of Rule 30 from a row $x$, a Boolean function of the $2t + 1$ cells
$x_{-t}, \dots, x_t$ of its cone. A *subcube* is a partial row: each cell is fixed to 0, fixed to 1, or free, and the
subcube is the set of rows that agree with it on the fixed cells. Let $m(t)$ be the least number of fixed cone cells of
a subcube on which $c_t$ is constant. Equivalently, $m(t)$ is the length of the shortest prime implicant of $c_t$ or of
its complement, or, over all rows, the smallest certificate of the best row. In decision-tree terms, a leaf of a tree
for $c_t$ is reached on a subcube on which $c_t$ is constant, so every leaf of every tree for $c_t$ has depth at least
$m(t)$, and a tree that reads a least subcube first has a leaf at depth exactly $m(t)$. [QueryDepth](QueryDepth.md)
bounds the deepest leaf ($2t$ or $2t + 1$); this entry is about the shallowest.

## Statement

1. **The leftmost cell is always fixed** (`constOn_fixes_left`). If $c_t$ is constant on a subcube, the subcube fixes
   $x_{-t}$. In Lean a subcube is a partial row `ρ : Int → Option Bool` with the rows `fillRow ρ x` of
   [QueryDepth](QueryDepth.md), and `CenterConstOn ρ t` says that every two of them have the same center.
2. **Screening with $x_{-1}$ free** (`screening_even_free`). If $x_{-j} = 1$ exactly for the even $j$ with
   $2 \le j \le t$, and $t \ge 9$, then $c_t = 1$ for every value of $x_{-1}, x_0, \dots, x_t$.
3. **$t - 1$ cells suffice for $t \ge 9$** (`stripe_center`, `stripe_constOn`, `stripeRow_isSome`). For $t \ge 9$, fix
   $x_{-t} = v$ and $x_{-j} = [j \text{ even}]$ for $2 \le j \le t - 1$, and leave $x_{-1}, \dots, x_t$ free. On this
   subcube, `stripeRow t v`, which fixes exactly the $t - 1$ cells $-t, \dots, -2$, the center is constant: it is 1
   exactly when $v = [t \text{ even}]$. So $m(t) \le t - 1$ for every $t \ge 9$.
4. **The least size, computed.** The exact values for $t \le 15$, with the number of subcubes of least size:

   | $t$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
   |---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
   | $m(t)$ | 2 | 3 | 4 | 5 | 5 | 6 | 7 | 8 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
   | least subcubes | 4 | 6 | 22 | 58 | 4 | 4 | 4 | 82 | 2 | 2 | 2 | 16 | 14 | 46 | 72 |

   So $m(t) = t - 1$ for $9 \le t \le 15$, and $m(t) = t + 1$ for $t \le 4$, $m(t) = t$ for $5 \le t \le 8$. For
   $t = 9, 10, 11$ the two least subcubes are the stripes of item 3. At $t = 12$ and $13$ there are others, with free
   cells inside the fixed stretch; for example at $t = 12$ the partial row
   $x_{-12} \dots x_{-1} = 1\,{*}\,0101010101$ (an odd stretch from the wall at $-1$, with $x_{-11}$ free), and at
   $t = 13$ the partial row $x_{-13} \dots x_0 = 01010101010{*}{*}0$, with every other cell free (`least_subcubes`
   lists them all).
5. **Controls.** For Rule 90 the same computation gives $m(t) = 2^{s(t)}$ for $t \le 10$, with $s(t)$ the number of 1s in
   the binary digits of $t$ (2 at $t = 1, 2, 4, 8$), and for Rule 150 it gives 3, 3, 5, 3, 9, 5, 11, 3, 9, 9 for
   $t = 1, \dots, 10$. Both rules make $c_t$ the parity of a set of cells, which is constant on a subcube only when
   the subcube fixes all of them, so these are the sizes of those sets.

## Proof

**Item 1.** By `flip_center` of [ConeScreening](ConeScreening.md), flipping $x_{-t}$ flips $c_t$ on every row
(`center_flip_setAt` of QueryDepth). If the subcube left $x_{-t}$ free, the two rows that agree with it, are white
elsewhere and differ only at $x_{-t}$ would both lie in it (`fillRow_setAt_none`), with different centers.

**Item 2.** Translate the row by one cell: $y_i = x_{i-1}$ has $y_{-j} = [j \text{ odd}]$ for $1 \le j \le t - 1$, and
$y_0 = x_{-1}$ is free; $c_t(x)$ is the cell $b(t) = y(t, 1)$. ConeScreening's stripe lemma keeps $y(s, -1)$ black for
$s < t - 1$, and the pair $p(s) = (a(s), b(s)) = (y(s, 0), y(s, 1))$ beside it moves by $a' = \lnot(a \lor b)$,
$b' = a \oplus (b \lor e)$, with $e$ the next cell. The base values $c_9 = c_{10} = 1$ hold for both colors of
$x_{-1}$ and every right half: for $x_{-1} = 0$ by ConeScreening's `screening_even`, and for $x_{-1} = 1$ by `decide`
over the $2^{10}$ and $2^{11}$ right halves (`ebase9_one_all`, `ebase10_one_all`). This settles $t = 9, 10$. Let
$t \ge 11$; then $b(9) = b(10) = 1$, and $p(s) \ne (0, 0)$ for $8 \le s \le t - 1$: at $s = 8$, the pair $(0, 0)$
gives $a(9) = 1$, $b(9) = e(8)$, so $e(8) = 1$ and $b(10) = 1 \oplus (1 \lor e(9)) = 0$, a contradiction; at $s = 9, 10$ it
contradicts $b(s) = 1$; and for $s \ge 11$ ConeScreening's `pair_back` carries a pair $(0, 0)$ at $s$ back to $s - 2$.
Finally $b(t) = a(t-1) \oplus (b(t-1) \lor e(t-1))$ is 0 only if $p(t-2)$ or $p(t-1)$ is $(0, 0)$, so $b(t) = 1$. This
is the even-pattern argument of ConeScreening with the base moved from times 8, 9 to times 9, 10, which is why the
bound starts at 9: at $t = 8$ the center still depends on the right half when $x_{-1} = 1$.

**Item 3.** Set $x_{-t}$ to $[t \text{ even}]$; item 2 makes the center 1. By `center_decomp`,
$c_t = x_{-t} \oplus g$ with $g$ free of $x_{-t}$, so the center is $1 \oplus x_{-t} \oplus [t \text{ even}]$ on
the whole subcube.

**Item 4.** The code (`computations/min_certificate.py`) reads the cells from the right, $x_t$ first. After the cells
$x_t, \dots, x_{t-r+1}$ have each been fixed or left free, it keeps the function of the remaining cells that is 1 where
every completion inside the partial subcube makes $c_t = 1$: fixing the next cell to $b$ keeps its half $b$, and
leaving it free keeps the AND of the two halves. Two partial subcubes with the same function have the same
completions, so the pass keeps one cost for each function, the least, and the number of partial subcubes at that cost.
It runs on $c_t$ and on its complement and covers all $3^{2t+1}$ subcubes. The functions reached are few when the
cells are read from the right, the order that [cone screening](../../findings/complexity/cone-screening.md) found to
have the fewest subfunctions. For $t \ge 12$ the
pass runs on $g$, the table with $x_{-t} = 0$, which item 1 allows: the least subcubes of $c_t$ are the two values of
$x_{-t}$ times the least subcubes on which $g$ is constant. The values for $t \le 8$, with their counts, agree with the
dynamic program over all $3^{2t+1}$ subcubes of `query_certificates.subcube_constant`; for $t \le 11$ and $t = 14$ the
pass on the whole table and on $g$ agree; and the test checks $t \le 3$ against a listing of every partial row.

## What it means

For $t \ge 9$ the cone of the center can be fixed by $t - 1$ of its $2t + 1$ cells, all of them in the left half, and on
the range computed ($9 \le t \le 15$) it cannot be fixed by fewer. Rule 90 needs only 2 cells at every power of two. This is a statement about rows
given as input. It is not about $c(n)$ as a function of the digits of $n$, and it says nothing about the single black
cell, where every cell is known. It is also not the least *forward certificate* of
[restricted models](../../negative-results/complexity/restricted-models.md), which is a set of spacetime cells of the
single-seed diagram from which the rule derives $c(n)$; here the cells are those of one arbitrary row.

**Beyond 15.** $m(t) = t - 1$ does not hold for every $t \ge 9$: $m(16) = 13$ by computation, and
$m(t) \le t - 2\lfloor t/9 \rfloor + 2$ for every $t \ge 9$, so $m(t) \le t - 2$ for $t \ge 18$, in Lean, because the
stripe absorbs two cells beside its black end every nine steps ([StripeGrowth](StripeGrowth.md)). The routing lemma
fails at $t = 12$ ([routing lemma](../../negative-results/complexity/min-certificate-routing.md)), and an all-$t$ lower
bound is open ([certificate lower bounds](../../negative-results/complexity/certificate-lower-routes.md)).

The kit has no statement about prime implicants, subcubes or the least certificate of a function of the cone (its
core Lean, its equivalent forms, including `QueryComplexity` and `AlgebraicDegree`, and its main branch were
searched). It has the stripe as a fixed point in its zero-boundary setting (`Rule30ZeroBoundaryStripe`), which this
module does not use; items 1 to 3 are new, as stated for an arbitrary row.

## Reproduce

```bash
python -m computations.min_certificate --max-t 15 --controls-t 10 --routing-t 14 --stripe-t 16 --dp-t 8
```

The least sizes take about four minutes, most of it at $t = 15$, which needs about 3 GB; `--max-t 14` takes under a
minute and 1 GB. The routing table of the negative result takes about four minutes more. The stripe is also evaluated
over every completion for $9 \le t \le 16$. The test `tests/test_min_certificate.py` runs in a fraction of a second.
