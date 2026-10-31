---
title: An alternating left half fixes the center cell whatever the right half is, so the left half of the cone is not incompressible
category: complexity
problems: [3]
status: paper
formalization: partial
evidence: [computations/cone_screening.py, tests/test_cone_screening.py]
---

# An alternating left half fixes the center cell whatever the right half is, so the left half of the cone is not incompressible

Write $c_t$ for the cell at time $t$ under column $0$, as a Boolean function of the $2t + 1$ cells $x_{-t}, \dots, x_t$ of
row $0$ (its *cone*), with the rule's update $x_j' = x_{j-1} \oplus (x_j \lor x_{j+1})$. Call $x_{-t}, \dots, x_{-1}$ the
left half and $x_0, \dots, x_t$ the right half. The *even pattern* is the left half with $x_{-j} = 1$ exactly for even $j$
($1 \le j \le t$), so $x_{-1} = 0$ and $x_{-2} = 1$; the *odd pattern* has $x_{-j} = 1$ exactly for odd $j$.

## Statement

1. **Screening.** For the even pattern, $c_t = 1$ for every right half and every $t \ge 8$. For the odd pattern,
   $c_t = 0$ for every right half and every $t \ge 9$. Both thresholds are sharp: at $t = 7$ (even) and $t = 8$ (odd) the
   center still depends on the right half.
2. **The left half is not incompressible.** $c_t = x_{-t} \oplus g(x_{-t+1}, \dots, x_t)$ for a function $g$. Hence the
   even pattern and the odd pattern with $x_{-t}$ flipped induce the same function of the right half (the constant 1),
   and the odd pattern and the even pattern with $x_{-t}$ flipped induce the constant 0. So for every $t \ge 9$ the
   $2^t$ settings of the left half induce at most $2^t - 2$ distinct functions of the right half.
3. **Counts, exhausted.** Let $N_{\mathrm{L}}(t, k)$ be the number of distinct subfunctions of $c_t$ after the $k$
   leftmost cone cells are fixed, and $N_{\mathrm{R}}(t, k)$ the same after the $k$ rightmost cells are fixed (cone
   cells $x_{-t}, \dots, x_t$, so $k = t$ fixes the whole left half in the first case).
   - $N_{\mathrm{L}}(t, t) = 2^t$ for $t \le 8$, $506$ for $t = 9$ and $1010$ for $t = 10$ (the bound of item 2 is $510$
     and $1022$); $N_{\mathrm{L}}(t, k) = 2^k$ for $k \le t - 1$ and $t \le 10$.
   - At $t = 10$: $N_{\mathrm{R}}(10, k) = 2, 2, 4, 5, 9, 12, 20, 26, 42, 54, 85, 108, 167, 209, 318$ for $k = 1, \dots, 15$.

   | $t = 10$, $k$ | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 |
   |---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
   | $N_{\mathrm{L}}(10, k)$ | 1750 | 1778 | 824 | 280 | 100 | 40 | 16 | 8 | 4 | 4 |
   | $N_{\mathrm{R}}(10, k)$ for $k \ge 16$ | | | | | | 309 | 64 | 8 | 4 | 2 |

   Summed over the levels $k = 1, \dots, 20$ at $t = 10$, the counts are $6836$ for the order that reads the left cells
   first and $1450$ for the order that reads the right cells first; the largest single count is $1778$ against $318$.
   At $t = 9$ the sums are $2972$ and $780$.
4. **What this is not.** No lower bound for any variable order, circuit or machine follows, and nothing here bears on
   the single-seed center column of the prize (that is one row, and these statements are about all rows). The count
   $506$ is still more than $2^8$, so the one-way communication cost of sending the left half to the right half, which
   is the base-2 logarithm of the number of distinct subfunctions rounded up, is still $t$ bits at $t = 9$ and $10$. What
   fails is the proof pattern that makes all $2^t$ left halves pairwise distinguishable.

## Proof

**The stripe stays.** Let the wall $w$ be $-1$ for the odd pattern and $-2$ for the even pattern: the rightmost cell of
the alternating stretch, which is black, with cells $w - k$ black for even $k$ and white for odd $k$. One step leaves
the stretch as it is, whatever lies to the right of the wall:
$x_w' = x_{w-1} \oplus (x_w \lor x_{w+1}) = 0 \oplus 1 = 1$; for even $k \ge 2$, $x_{w-k}' = x_{w-k-1} \oplus
(1 \lor x_{w-k+1}) = 0 \oplus 1 = 1$; for odd $k$, $x_{w-k}' = 1 \oplus (0 \lor 1) = 0$. A cell of the cone at time $s$
reads only cells of the cone at time $s - 1$, so the stretch stays, from the cone's left edge to the wall, for all
$s \le t$. The kit has this fixed point in its zero-boundary setting
([`Rule30ZeroBoundaryStripe.stripe_confined`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30ZeroBoundaryStripe.lean):
a row equal to the stripe from an odd depth on keeps that tail) and the masking step in
`equivalents/Rule30Equivalents/FrozenBoundaryPeriodTwo.lean` (`zbl_of_alternating`: at a black wall the `or` is already
black, so what lies to the right is masked). Neither statement is the one used here, which is checked directly above.

**The pair beside the wall.** Let $a(s) = x(s, w + 1)$, $b(s) = x(s, w + 2)$ and $e(s) = x(s, w + 3)$, the cells of row
$s$. Since the wall is black at every time,
$$a(s+1) = \mathrm{NOR}(a(s), b(s)), \qquad b(s+1) = a(s) \oplus (b(s) \lor e(s)).$$
Write $p(s) = (a(s), b(s))$.

*Lemma A.* If $p(s) = (0, 0)$ with $s \ge 2$, then $a(s-1) = 1$ and $p(s-2) = (0, 0)$. Proof: $a(s) = 0$ gives
$a(s-1) \lor b(s-1) = 1$. If $a(s-1) = 0$, then $b(s-1) = 1$ and $b(s) = 0 \oplus 1 = 1$, a contradiction. So
$a(s-1) = 1$, and $a(s-1) = \mathrm{NOR}(a(s-2), b(s-2)) = 1$ gives $p(s-2) = (0, 0)$.

*Lemma B.* If $b(s) = 0$ with $s \ge 1$, then $p(s) = (0, 0)$ or $p(s-1) = (0, 0)$. Proof: if $a(s-1) = 1$, then
$a(s) = 0$, so $p(s) = (0, 0)$. If $a(s-1) = 0$, then $b(s) = b(s-1) \lor e(s-1) = 0$ gives $b(s-1) = 0$, so
$p(s-1) = (0, 0)$.

**Odd pattern.** Here $w = -1$, $a(s) = x(s, 0)$ and $c_t = a(t) = [\,p(t-1) = (0, 0)\,]$. An exhaustive computation over
all right halves gives $c_9 = c_{10} = 0$, so $p(8)$ and $p(9)$ are not $(0, 0)$ for any right half. By Lemma A a pair
$(0, 0)$ at a time $s \ge 10$ gives one at $s - 2$, and by induction at $8$ or $9$. So no $p(s)$ with $s \ge 8$ is
$(0, 0)$, and $c_t = 0$ for $t \ge 9$. Both base values depend only on the cone of $c_9$ or $c_{10}$, whose left half is the same pattern, and hold for every
right half, so they hold in the cone of every longer $c_t$.

**Even pattern.** Here $w = -2$, $b(s) = x(s, 0)$ and $c_t = b(t)$. The stretch left of the wall has $t - 1$ cells, so
inside the cone the wall is black only for $s \le t - 2$, and the pair recursion holds for $s \le t - 2$. Exhaustively,
$c_8 = c_9 = 1$ for all right halves, which settles $t = 8, 9$. Let $t \ge 10$. Then $b(8) = b(9) = 1$, so
$p(8), p(9) \ne (0, 0)$. Suppose $p(7) = (0, 0)$. Then $p(8) = (1, e(7))$, and $b(8) = 1$ forces $e(7) = 1$, so
$p(9) = (\mathrm{NOR}(1, 1),\ 1 \oplus (1 \lor e(8))) = (0, 0)$, contradicting $b(9) = 1$. So $p(7), p(8) \ne (0, 0)$,
and Lemma A gives $p(s) \ne (0, 0)$ for $7 \le s \le t - 1$. Finally $b(t) = a(t-1) \oplus (b(t-1) \lor e(t-1))$, which
holds whatever the wall does. If $b(t) = 0$, either $a(t-1) = 1$, and then $a(t-1) = \mathrm{NOR}(a(t-2), b(t-2))$ (the
wall is black at $t - 2$) gives $p(t-2) = (0, 0)$, or $a(t-1) = 0$ and $b(t-1) = 0$, so $p(t-1) = (0, 0)$. Both are
excluded, so $c_t = 1$.

**Item 2.** The leftmost cone cell at time $s$, $L_s = x(s, -t + s)$, satisfies $L_{s+1} = L_s \oplus h_s$ with
$h_s = x(s, -t+s+1) \lor x(s, -t+s+2)$, and $h_s$ depends only on $x_{-t+1}, \dots, x_t$ (the cone of a cell at
$-t+s+1$ at time $s$ starts at $-t+1$). So $c_t = L_t = x_{-t} \oplus \bigoplus_s h_s$. Flipping $x_{-t}$ therefore flips
$c_t$ for every setting of the other cells. For $t \ge 9$ the left words $E$ (even), $O$ (odd), $E'$ and $O'$ (each with
$x_{-t}$ flipped) are four distinct words, $E$ and $O'$ give the constant 1 and $O$ and $E'$ the constant 0, so the $2^t$
words give at most $2^t - 2$ functions.

**Counts.** The truth table of $c_t$ over all $2^{2t+1}$ cone settings is computed by bit-sliced evolution; the number of
distinct subfunctions is the number of distinct rows (or columns) of its reshape. The test checks the table against
a plain cell-by-cell run for $t = 3, 4$, the counts at $t = 9$ against a set of byte strings, and the pair lemmas and
the induction of this section against every initial pair and every sequence $e(0), \dots, e(12)$.

## Relation to the other complexity entries

The entries on [the space ladder](space-ladder.md), [the space thresholds](space-thresholds.md) and
[one-tape crossing sequences](../../negative-results/complexity/one-tape-crossing.md), and the code of
`computations/obdd_orders.py`, treat $c(n)$ as a function of the binary digits of $n$. This entry treats the center
cell as a function of the cells of a row, which is the function that a time-$t$ evaluation computes and a different
object: the single black cell is one input to it. A variable order for the row has a natural reading, left to right or
right to left, which the digits of $n$ do not have.

The counts above are the quantities that an ordered-decision-diagram or one-way-communication bound would use, and
they show that reading the row from the right is far cheaper at $t \le 10$ than reading it from the left (sums 1450
and 6836). No lower bound follows. A bound that counts distinguishable left halves cannot reach $2^t$, by item 2, and the counts
stay above $2^{t-1}$ for $t \le 10$.

## Reproduce

```bash
python -m computations.cone_screening --max-t 18       # both patterns for t = 1 .. 18, and the pair lemmas (1 s)
python -m computations.cone_screening --counts 10      # subfunction counts for t = 1 .. 10 (3 s)
```

The test `tests/test_cone_screening.py` runs in under a second. The screening of item 1, the
decomposition and the four words of item 2 are proved in Lean for an arbitrary row
([ConeScreening](../../Rule30Open/Complexity/ConeScreening.md)), with the base values checked by `decide` over every
right half; the sharpness of the thresholds, the count $2^t - 2$ that follows from the four words, and the counts of
item 3 are computed only.
