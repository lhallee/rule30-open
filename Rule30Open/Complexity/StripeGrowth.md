---
title: The stripe grows by two cells every nine steps, so t - 2k fixed cells make the center constant for t ≥ 9(k + 1), and the least certificate is below t - 1 for every t ≥ 18, and at t = 16, 17 by computation
category: complexity
problems: [3]
status: proved
lean: Rule30Open.Complexity.StripeGrowth
headline: [stripe_grow, stripe_far, far_stripe_center, farStripe_constOn, farStripeRow_isSome]
kit: refines
kit_modules: [Rule30ZeroBoundaryStripe]
evidence: [computations/certificate_lower.py, tests/test_certificate_lower.py]
---

# The stripe grows by two cells every nine steps, so t - 2k fixed cells make the center constant for t ≥ 9(k + 1), and the least certificate is below t - 1 for every t ≥ 18, and at t = 16, 17 by computation

Write $c_t(x)$ for the center cell after $t$ steps of Rule 30 from a row $x$, a Boolean function of the cone cells
$x_{-t}, \dots, x_t$, and $m(t)$ for the least number of fixed cells of a subcube (a partial row) on which $c_t$ is
constant. [MinCertificate](MinCertificate.md) proves $m(t) \le t - 1$ for $t \ge 9$, with the stripe on the
$t - 1$ cells $x_{-t}, \dots, x_{-2}$, and computes $m(t) = t - 1$ for $9 \le t \le 15$. This entry shows that the
stripe can stop short of the center: the alternating stretch absorbs the cells beside its black end, two cells every
nine steps, so $m(t)$ falls below $t - 1$ and its slope is at most $7/9$.

The *odd stripe* with wall at $w$ is the stretch with $x_{w - d} = 1$ exactly for even $d \ge 0$: black at the wall,
alternating to the left. In ConeScreening's terms it is the odd pattern, $x_{-j} = [j \text{ odd}]$, translated so
that its black end is at $w$.

## Statement

1. **The stripe grows** (`stripe_grow`, `stripe_grow_shift`). If $x_{-j} = [j \text{ odd}]$ for $1 \le j \le L$ with
   $L \ge 10$, then after nine steps the cells $-1, \dots, -(L - 9)$ still alternate, cell $0$ is white and cell $1$
   is black, for every value of the cells $0, 1, 2, \dots$. So the row after nine steps carries the odd stripe with
   wall at $1$, on $L - 7$ cells.
2. **The far cell** (`stripe_far`). If $x_{-j} = [j \text{ odd}]$ for $1 \le j \le t - 2k$ and $t \ge 9(k + 1)$, the
   cell $2k$ after $t$ steps is white, for every value of the other cells.
3. **The center** (`far_stripe_center`, `farStripe_constOn`, `farStripeRow_isSome`). For $t \ge 9(k + 1)$, fix
   $x_{-t} = v$ and $x_{-i} = [i \text{ odd}]$ for $2k + 1 \le i \le t - 1$, and leave the cells $x_{-2k}, \dots, x_t$
   free. On this subcube, `farStripeRow t k v`, which fixes exactly the $t - 2k$ cells $-t, \dots, -(2k + 1)$, the
   center is $v \oplus [t \text{ odd}]$. Hence
   $$m(t) \le t - 2k \text{ for } t \ge 9(k + 1), \qquad m(t) \le t - 2\lfloor t/9 \rfloor + 2 \text{ for } t \ge 9,$$
   so $m(t) \le t - 2$ for every $t \ge 18$ and $\limsup m(t)/t \le 7/9$.
4. **Computed** (`certificate_lower.right_free_least`, `no_small_subcube`, `far_stripe_values`).
   - At $t = 16$ the least subcubes that leave $x_1, \dots, x_{16}$ free have 13 fixed cells, and there are four: the
     two values of $x_{-16}$ times $x_{-11} \dots x_0 = 010101010101$ (the odd stripe with wall at $0$, with the
     four cells $x_{-15}, \dots, x_{-12}$ free) or $x_{-15} = 0$, $x_{-11} \dots x_{-1} = 10101010101$ (wall at $-1$,
     with $x_{-14}, x_{-13}, x_{-12}$ free). `subcube_values` runs every completion of each ($2^{20}$ rows) and finds
     one center value. The capped search over all subcubes (`no_small_subcube` with cap 11) finds none with 12 fixed
     cells or fewer, so $m(16) = 13 = t - 3$.
   - At $t = 17$ the least subcubes that leave $x_2, \dots, x_{17}$ free have 14 fixed cells, for example
     $x_{-17} = 0$, $x_{-16} = 1$ and the odd stripe $x_{-12} \dots x_{-1} = 010101010101$ with wall at $-1$, the three
     cells between free. So $m(17) \le 14 = t - 3$.
   - At $t = 18$ the least subcubes that leave $x_3, \dots, x_{18}$ free have 15 fixed cells, one for each value of
     $x_{-18}$: $x_{-17} \dots x_{-4} = 01010101010101$, the stripe with its black end at $-4$, every other cell free.
     So $m(18) \le 15 = t - 3$, one below the bound $t - 2$ of item 3. `subcube_values` confirms each listed subcube
     at $t = 17$ and $18$ over every completion.
   - The far stripe of item 3 with $k = 1$ (16 fixed cells at $t = 18$) is constant over all $2^{21}$ completions at
     $t = 18$ and all $2^{22}$ at $t = 19$, and takes both values at $t = 16$ and $17$: the threshold $t \ge 9(k + 1)$
     is sharp for $k = 1$.

## Proof

**Item 1.** The cells $-1, \dots, -(L - 9)$ still alternate after nine steps by ConeScreening's `stripe`: a black
cell between two whites and a white cell between two blacks keep their color, and the stretch loses one cell per step
on its left. ConeScreening's `screening_odd` at $t = 9$ and $t = 10$ (it needs the stripe on $-1, \dots, -t$, so
$L \ge 10$) gives that cell $0$ is white after 9 and after 10 steps, whatever lies right of the wall. Cell $0$ after
10 steps is $x(9, -1) \oplus (x(9, 0) \lor x(9, 1)) = 1 \oplus (0 \lor x(9, 1))$, and it is 0, so $x(9, 1) = 1$.
Translated by two cells, the row after nine steps has $y_{-1} = x(9, 1) = 1$, $y_{-2} = x(9, 0) = 0$, and
$y_{-j} = x(9, -(j - 2)) = [j - 2 \text{ odd}] = [j \text{ odd}]$ for $3 \le j \le L - 7$.

**Item 2.** Induction on $k$. For $k = 0$ it is `screening_odd`. For $k + 1$, the stripe has $L = t - 2k - 2 \ge 10$
cells; by item 1 the row after nine steps, translated by two cells, carries the stripe on $L - 7 = (t - 9) - 2k$ cells,
and $t - 9 \ge 9(k + 1)$. The induction hypothesis at time $t - 9$ makes its cell $2k$ white, which is the cell
$2k + 2$ of the original row after $t$ steps (`evo_add`, `evo_translate`).

**Item 3.** Set $x_{-t}$ to $[t \text{ odd}]$ and translate the row by $2k$ cells: the stripe then covers
$-1, \dots, -(t - 2k)$, and item 2 makes the cell $2k$ of the translated row, the center of the original one, white.
By `center_decomp`, $c_t = x_{-t} \oplus g$ with $g$ free of $x_{-t}$, which gives the center for both values of
$x_{-t}$.

**Item 4.** `screened_functions` builds, for the cells $x_{-t+1}, \dots, x_r$ (with $x_{-t}$ white), the function
that is 1 where $c_t = 1$ for every value of $x_{r+1}, \dots, x_t$, and the one where $c_t = 0$ for every such value.
It bit-slices the rows on the lowest cells and fixes the rightmost cells in an outer loop, keeping the AND and the OR
of the chunks, so the table of $c_t$ is never stored. The least subcubes of those two functions come from the
breadth-first pass of MinCertificate. The test checks the pass against a listing of every partial row at $t = 5$.

## What it means

The conjecture of [MinCertificate](MinCertificate.md) that $m(t) = t - 1$ for every $t \ge 9$ is false: it fails at
$t = 16$ and $17$ by computation and at every $t \ge 18$ by the Lean theorem. With $k = 0$ the far stripe is
ConeScreening's odd pattern on all $t$ cells of the left half; each step of $k$ removes the two cells at the black end,
which the stripe absorbs again within nine steps, whatever the free cells are. The values 9 and 10 of ConeScreening's
base checks set the rate, two cells per nine steps. A sample is faster: with a stripe of 90 cells and 20,000 random
right halves (`absorption_times`, a heuristic, not a proof), the cells $2i, 2i + 1$ right of the wall took one value
in every sample from the times 9, 18, 27, 35, 44, 52, 57, 65 for $i = 0, \dots, 7$, so the true slope of $m(t)$ may be
below $7/9$; only the rate $2/9$ is proved. The least subcubes at $t = 16, 17, 18$ are stripes of this kind, cut short
at the black end, with a few free cells at the cone's left edge at $t = 16$ and $17$. For comparison, Rule 90 has
$m(2^j) = 2$. A linear lower bound for Rule 30, if one holds, has to sit at or below
$t - 2\lfloor t/9 \rfloor + 2 \le 7t/9 + 34/9$
([routes to a lower bound](../../negative-results/complexity/certificate-lower-routes.md)).

This is a statement about rows given as input, like MinCertificate. It says nothing about the single black cell's
column, where every cell is known.

The kit proves the same absorption in its zero-boundary left half (`Rule30ZeroBoundaryStripe.front_advance`: a row
that agrees with the stripe from an odd depth $m \ge 13$ on agrees with it from $m - 2$ on within 9 steps, a kernel
check over $2^{12}$ contents, and `stripe_absorb`). Here it is stated for arbitrary rows, a finite stripe inside the
cone and a fixed time 9, derived from ConeScreening's `screening_odd`; the bound on the least certificate is new (the
kit's core Lean, its equivalent forms and its main branch were searched for certificates, prime implicants and
subcubes of the cone).

## Reproduce

```bash
python -m computations.certificate_lower --comb-t 1 --monomial-t 1 --window-t 1 --check-t 16 --cap 11 --split 8 \
    --free 16:1,17:1,18:2 --stripe 16:1,17:1,18:1,19:1 --absorption
```

The capped search over all subcubes at $t = 16$ (with `--split 8`, which keeps it under 4 GB) takes about 14 minutes
and 3.6 GB. The least subcubes with the right cells free take about 1.5 minutes at $t = 16$, 6 minutes at $t = 17$
and 27 minutes at $t = 18$, each under 1 GB. The
far stripe at $t = 19$ ($2^{22}$ completions) and the sampled absorption times take a few seconds. The test
`tests/test_certificate_lower.py` checks the growth step over all $2^{11}$ values of the cells it sees, the far stripe
at $t = 18$ on 2,000 sampled rows, and the searches on small cases against listings of partial rows.
