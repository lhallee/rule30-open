---
title: The center never depends on all three rightmost cone cells at one row, so its certificate complexity is at most 2t
category: complexity
problems: [3]
status: proved
lean: Rule30Open.Complexity.RightCorner
headline: [right_corner, right_corner_certificate, corner_white, strip_one, strip_two, strip_three]
kit: new
kit_modules: [Rule30Equivalents.QueryComplexity]
evidence: [computations/query_certificates.py, tests/test_query_certificates.py]
---

# The center never depends on all three rightmost cone cells at one row, so its certificate complexity is at most 2t

Write $c_t(x)$ for the center cell after $t$ steps of Rule 30 from a row $x$, a Boolean function of the $2t + 1$ cells
$x_{-t}, \dots, x_t$ of its cone. The function is *sensitive* to cell $i$ at the row $x$ when flipping $x_i$ flips
$c_t(x)$. A *certificate* for $x$ is a set of cells whose values at $x$ fix $c_t$: every row that agrees with $x$ there
has the center of $x$. The *certificate complexity* $C(c_t)$ is the largest, over rows, of the smallest certificate.

Every decision tree for $c_t$ reads at least $C(c_t)$ cells on some row, and $C(c_t)$ is at least the sensitivity
$s(c_t)$, the most cells to which one row is sensitive. These are the standard ways to bound the depth of a decision
tree from below. [QueryDepth](QueryDepth.md) shows that every tree reads at least $2t$ cells, and all $2t + 1$ for
$t \le 17$; whether all $2t + 1$ are needed for every $t$ is open. This entry shows that certificates cannot settle it.

This is a statement about an arbitrary input row. It bounds a lower-bound method for decision trees and does not bound
the cost of the single black cell's column, the row of the prize, where a tree reads nothing.

## Statement

1. **The right corner** (`right_corner`). For $t \ge 2$ and every row $x$, $c_t$ is insensitive at $x$ to at least one
   of the cells $t - 2$, $t - 1$, $t$.
2. **Certificates of $2t$ cells** (`right_corner_certificate`). For $t \ge 2$ and every row $x$ there is a cell
   $i \in \{t - 2, t - 1, t\}$ such that every row agreeing with $x$ on the other $2t$ cells of the cone has the center
   of $x$. So $s(c_t) \le C(c_t) \le 2t$.
3. **Computed values** (`computations/query_certificates.py`).

| $t$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| $2t + 1$ | 3 | 5 | 7 | 9 | 11 | 13 | 15 | 17 | 19 | 21 | 23 | 25 |
| $s(c_t)$ | 3 | 4 | 6 | 7 | 10 | 10 | 13 | 14 | 16 | 18 | 21 | 21 |
| $C(c_t)$ | 3 | 4 | 6 | 7 | 10 | 11 | 13 | | | | | |

$C(c_t)$ is computed for $t \le 7$. It falls below $2t$ at $t = 4, 6, 7$, so for those $t$ certificates give less
than the bound $2t$ of QueryDepth. At $t = 1$ the two rows with $x_0 = x_1 = 0$ are sensitive to all three cells,
which is why item 1 needs $t \ge 2$.

## Proof

Work in the frame that moves left one cell per step. For a row $x$ and an anchor $a$ write
$R_k(s) = $ the cell $a - s - k$ after $s$ steps (`rdiag`). One step of the rule reads
$R_k(s + 1) = R_{k+2}(s) \oplus (R_{k+1}(s) \lor R_k(s))$ (`rdiag_succ`): diagonal $k$ is driven by the two diagonals
to its left. So two rows that agree on every diagonal $k \ge m$ at one time agree on them at every later time
(`agree_add`), and a row flipped at cell $a - k$ agrees with the original on the diagonals $k + 1, k + 2, \dots$ at
time 0 (`agree_flip`). Take $a = t$; the center is $R_0(t)$ (`rdiag_center`), and the cells $t, t - 1, t - 2$ are
$R_0(0), R_1(0), R_2(0)$. Fix a row $x$ that is sensitive to all three, with $t \ge 2$; write $R_k$ for its diagonals
and $R'_k$ for those of a flipped row.

**Step 1: a flip of cell $t$ needs a white second diagonal** (`corner_white`). The flip of $R_0(0)$ stays on diagonal
0. If $R_1(s) = 1$ for some $s < t$, then $R_0(s + 1) = R_2(s) \oplus 1$ on both rows, the rows agree on every
diagonal from time $s + 1$ on, and the center does not flip. So $R_1(s) = 0$ for every $s < t$. Two consequences:
$R_0(s + 1) = R_2(s) \oplus R_0(s)$ for $s < t$, and $R_3(s) = R_2(s)$ for $s + 1 < t$ (from $R_1(s + 1) = 0$). At
time 0 and 1 they give $x_{t-1} = 0$ and $x_{t-3} = x_{t-2}$, and $R_0(1) = x_{t-2} \oplus x_t$.

**Step 2: three strips.** Let $z$ be another row, and let $x$ have $R_1(s) = 0$ for $s < T$.

- `strip_one`: if $z$ agrees with $x$ on the diagonals $k \ge 1$ from time $s_0$, the difference
  $R'_0 \oplus R_0$ is the same at time $T$ as at $s_0$, since both rows then follow $R_0 \gets R_2 \oplus R_0$.
- `strip_two`: if $z$ agrees with $x$ on the diagonals $k \ge 2$ from time $s_0 < T$ and $R'_1(s_0) = 1$, then
  $R'_0(T) \oplus R_0(T) = \lnot R_0(s_0)$. While $R'_1 = 1$, the rule gives $R'_1(s + 1) = \lnot R_2(s)$ (using
  $R_3 = R_2$) and $R'_0(s + 1) = \lnot R_2(s)$, while $R_0$ does not change as long as $R_2 = 0$. Once $R'_1$ turns
  white it stays white, and the difference is carried. The invariant (`strip_two_inv`) is: the difference after time
  $s_0$ is $\lnot R_0(s_0)$, and $R_0(s) = R_0(s_0)$ while $R'_1(s) = 1$.
- `strip_three`: if $z$ agrees with $x$ on the diagonals $k \ge 3$ from time 1, with $R'_2(1) = \lnot R_2(1)$,
  $R'_1(1) = 1$ and $R_0(1) = 0$, then $R'_0(T) = R_0(T)$ for $T \ge 2$. The invariant (`ThreeState`, `three_step`):
  either the rows agree on every diagonal, or $R'_2 = \lnot R_2$, $R'_1 = 1$, $R_0 = 0$ and $R'_0 = 0$ (from time 2).
  The second state persists while $R_2 = 0$ and turns into the first as soon as $R_2 = 1$.

**Step 3: the two flips** (`right_corner`). Let $z_1, z_2$ be $x$ flipped at $t - 1$ and at $t - 2$. Both agree with
$x$ on the diagonals $k \ge 2$, respectively $k \ge 3$, from time 1 on. From the cells at time 1 (`rdiag_one`):
$R'_1(1) = \lnot x_{t-2}$ for $z_1$, $R'_1(1) = 1$ for $z_2$, and $z_2$ has $R'_2(1) = R_2(1)$ when $x_{t-2} = 1$
and $R'_2(1) = \lnot R_2(1)$ when $x_{t-2} = 0$.

- If $x_{t-2} = 1$: $z_1$ agrees with $x$ on the diagonals $k \ge 1$ at time 1 and differs on diagonal 0 by
  $x_t$ complemented, so `strip_one` makes it sensitive only when $x_t = 0$. `strip_two` for $z_2$ gives the difference
  $\lnot R_0(1) = x_t$, so it is sensitive only when $x_t = 1$. Both cannot hold.
- If $x_{t-2} = 0$: `strip_two` for $z_1$ gives the difference $\lnot R_0(1) = \lnot x_t$, so $x_t = 0$. Then
  $R_0(1) = 0$ and `strip_three` applies to $z_2$: the center does not flip.

**Item 2.** Take the cell $i$ that item 1 gives. A row $y$ that agrees with $x$ on the cone except possibly at $i$
agrees on the whole cone with $x$ or with $x$ flipped at $i$, and both have the center of $x$ (`evo_local`).

**Item 3.** The code takes the sensitivity of every row from the truth table of $c_t$, and $C(c_t)$ from a pass over
the $3^{2t+1}$ subcubes: a subcube on which $c_t$ is constant certifies each of its rows with its fixed cells, and each
row takes the smallest. The test checks both against plain enumeration over rows run with `step` and over all cell
sets for $t \le 3$.

## What it means

A decision-tree lower bound of $2t + 1$ for every $t$ cannot come from sensitivity, block sensitivity or certificate
complexity, all of which are at most $2t$, and already below $2t$ at $t = 4, 6, 7$. What does reach $2t + 1$ for
$t \le 17$ in QueryDepth is the top real coefficient, and at $t = 14$, where it vanishes, the coefficients of
restrictions that follow the answers given so far.
[Query-depth routes](../../negative-results/complexity/query-depth-routes.md) records where the other routes to
$2t + 1$ stop.

The kit has no sensitivity or certificate statements for $c_t$; its `QueryComplexity` bounds the depth by the GF(2)
degree. The left edge is the opposite of the right corner: the center flips with $x_{-t}$ on every row
([ConeScreening](ConeScreening.md), `flip_center`).

## Reproduce

```bash
python -m computations.query_certificates --max-s 12 --max-c 7 --max-fixed 5
```

It takes about 30 seconds.
