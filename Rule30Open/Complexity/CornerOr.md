---
title: The center sees the two rightmost cells of its cone only through their OR, so an adversary must answer the first of them white, and depth 2t + 1 reduces to a function of 2t - 1 cells
category: complexity
problems: [3]
status: proved
lean: Rule30Open.Complexity.CornerOr
headline: [center_corner_or, center_flip_beside_black, center_flip_corner_of_black, corner_tree_lift]
kit: refines
kit_modules: [Rule30Equivalents.AlgebraicDegree, Rule30Equivalents.QueryComplexity]
evidence: [computations/query_adversary.py, computations/query_adversary_sums.c, tests/test_query_adversary.py]
---

# The center sees the two rightmost cells of its cone only through their OR, so an adversary must answer the first of them white, and depth 2t + 1 reduces to a function of 2t - 1 cells

Write $c_t(x)$ for the center cell after $t$ steps of Rule 30 from a row $x$, a Boolean function of the $2t + 1$ cells
$x_{-t}, \dots, x_t$ of its cone, and $D(f)$ for the least depth of a decision tree that computes $f$.
[QueryDepth](QueryDepth.md) proves $D(c_t) = D(g_t) + 1$, with $g_t$ the center with $x_{-t}$ white, and so
$D(c_t) \ge 2t$ for $t \ge 2$; whether $D(c_t) = 2t + 1$ for every $t$ is open. This entry settles the right corner of
the cone, where [RightCorner](RightCorner.md) and the [query-depth routes](../../negative-results/complexity/query-depth-routes.md)
place the difficulty.

This is a query model for an arbitrary input row. It does not bound the cost of the single black cell's column, the
row of the prize, where a tree reads nothing.

## Statement

1. **The OR of the corner** (Lean, every $t \ge 1$). $c_t(x) = c_t(x')$, where $x'$ is $x$ with $x'_{t-1} = 0$ and
   $x'_t = x_{t-1} \lor x_t$ (`center_corner_or`). It comes from two shields:
   - `center_flip_beside_black`: if $x_t = 1$, flipping $x_{t-1}$ does not change $c_t$ (every $t$).
   - `center_flip_corner_of_black`: if $x_{t-1} = 1$, flipping $x_t$ does not change $c_t$ ($t \ge 1$).
2. **The corner restrictions** (paper, from item 1, every $t \ge 1$). Write $\mu(f) = \sum_x (-1)^{|x|} f(x)$ over
   the rows of the free cells of $f$, the top coefficient of the real polynomial of $f$ up to sign. Fixing $x_t$ or
   $x_{t-1}$ black gives $\mu = 0$, and fixing it white gives $\mu = \pm\mu(c_t)$. So the certificates of
   QueryDepth have level 1 only when they have level 0: a $t$ with $\mu(c_t) = 0$ needs level 2 or more, as $t = 14$
   does.
3. **The forced answer** (paper, every $t \ge 1$). Let $H_t$ be $c_t$ with $x_{t-1}$ white, a function of the other
   $2t$ cells. An adversary that makes a tree read all $2t + 1$ cells must answer the first query of $x_{t-1}$ or $x_t$
   with white, and $D(c_t) = 2t + 1$ if and only if $D(H_t) = 2t$. The bound $D(c_t) \le D(H_t) + 1$ is in Lean
   (`corner_tree_lift`).
4. **The reduction** (paper, every $t \ge 2$). Let $G_t$ be $c_t$ with $x_{-t}$ and $x_{t-1}$ white, a function of
   the $2t - 1$ cells $x_{-t+1}, \dots, x_{t-2}, x_t$. Then $D(c_t) = 2t + 1$ if and only if every tree for $G_t$ reads
   all its $2t - 1$ cells on some row. The GF(2) degree of $G_t$ is $2t - 2$, and $x_{-t+2} \cdots x_{t-2} x_t$,
   the product of every cell but $x_{-t+1}$, is a monomial of $G_t$ of that degree. Also $\mu(G_t) = \pm\mu(c_t)/2$.
5. **Computed** (`computations/query_adversary.py`). $\mu(c_t) \ne 0$ for $18 \le t \le 21$, so with QueryDepth
   $D(c_t) = 2t + 1$ for every $t \le 21$:

| $t$ | 18 | 19 | 20 | 21 |
|---|---|---|---|---|
| $\mu(c_t)$ | −756 | 336 | −232 | −3104 |

## Proof

**Item 1.** Work in the frame of [RightCorner](RightCorner.md): with the anchor $a = t$, write
$R_k(s)$ for the cell $t - s - k$ after $s$ steps (`rdiag`). One step reads
$R_k(s + 1) = R_{k+2}(s) \oplus (R_{k+1}(s) \lor R_k(s))$, and the center is $R_0(t)$.

*A black corner shields the cell beside it.* Let $x_t = 1$ and let $z$ be $x$ flipped at $t - 1$. At time 0 the two
rows agree on the diagonals $k \ge 2$ and on $R_0$, which is black. The invariant (`CornerKeep`) is: the rows agree on
the diagonals $k \ge 2$ and on $R_0$, and they agree on $R_1$ unless $R_0$ of $x$ is black. It holds at time 0, and one
step keeps it (`corner_keep_succ`):

- The diagonals $k \ge 2$ are driven by diagonals $k \ge 2$, so they keep agreeing.
- If the rows agree on $R_1$ they agree on everything from then on. Otherwise $R_0 = 1$ on both, so
  $R_0(s + 1) = \lnot R_2(s)$ on both.
- In that case, if $R_2(s) = 1$, then $R_1(s + 1) = R_3(s) \oplus 1$ on both rows, and they agree on $R_1$ again. If
  $R_2(s) = 0$, then $R_0(s + 1) = 0 \oplus (R_1(s) \lor 1) = 1$, black again.

At time $t$ the rows agree on $R_0(t)$, the center (`center_flip_beside_black`).

*A black cell beside the corner shields the corner.* If $x_{t-1} = R_1(0) = 1$ and $x$ is flipped at $t$, then
$R_0(1) = R_2(0) \oplus 1$ on both rows, which agree from time 1 on (`center_flip_corner_of_black`, from
`corner_white`).

*The OR.* If $x_{t-1} = 0$, the row $x'$ is $x$. If $x_{t-1} = 1$, setting $x_t$ black does not move the center (the
second shield), and then flipping $x_{t-1}$ to white does not move it either (the first shield); the result is $x'$.

**Item 2.** Fix $x_t = 1$. By item 1 the restricted function does not depend on $x_{t-1}$, so the rows of the sum
pair off by flipping $x_{t-1}$, with opposite signs and equal values, and $\mu = 0$. Splitting the sum of $c_t$ by the
value of $x_t$ gives $\mu(c_t) = \mu(c_t|_{x_t = 0}) - \mu(c_t|_{x_t = 1})$, so $\mu(c_t|_{x_t = 0}) = \mu(c_t)$.
The same holds for $x_{t-1}$, with the second shield. A certificate of level 1 asks, for every cell, a value whose
restriction has a nonzero top coefficient. At $x_t$ that value must be white, and the coefficient is then
$\pm\mu(c_t)$. The computation (`corner_restrictions`) agrees for $t \le 20$, in the convention of $g_t$.

**Item 3.** *The white answer is forced.* If the adversary answers $x_t = 1$, the function left does not depend on
$x_{t-1}$ (item 1), so a tree reads the other $2t - 1$ cells and stops. The same holds for $x_{t-1} = 1$ with $x_t$.

*If $D(H_t) = 2t$ then $D(c_t) = 2t + 1$.* Every tree for $H_t$ has a branch that reads all $2t$ cells, so there is
an adversary for $H_t$: a rule that answers each query so that, until every cell has been read, two rows that agree
with the answers have different values of $H_t$ (this is the minimax of the finite game of reading and answering).
Answer the queries of a tree for $c_t$ as follows. A cell other than $t - 1$ and $t$ gets the answer of the
adversary for $H_t$. The first query of $x_{t-1}$ or $x_t$ gets white. The second gets the answer of the adversary for
$H_t$ at the cell $t$. Suppose the tree stops before reading all $2t + 1$ cells. Then the adversary for $H_t$ has not
been asked some cell, a cell other than $t - 1$ and $t$ or else the cell $t$, so there are rows $y$ and $y'$ that agree
with its answers and have $H_t(y) \ne H_t(y')$. Extend $y$ to a row $x$ for $c_t$ that agrees with the answers given:
take its cells other than $t - 1$ and $t$ from $y$, and give the corner cells values with $x_{t-1} \lor x_t = y_t$ (a
corner cell that was answered is white or carries the answer for the cell $t$; a corner cell that was not read is free).
By item 1, $c_t(x) = H_t(y)$. Doing the same with $y'$ gives a row $x'$ with $c_t(x') = H_t(y') \ne c_t(x)$, and both
rows agree with every answer, so the tree cannot have stopped.

*Conversely* `corner_tree_lift` gives $D(c_t) \le D(H_t) + 1$: read $x_{t-1}$; on white, run a tree for $H_t$; on
black, $c_t(x) = H_t(x \text{ with } x_t := 1)$ by item 1, so run the same tree with the cell $t$ fixed black. So
$D(c_t) = 2t + 1$ forces $D(H_t) \ge 2t$, and $H_t$ has $2t$ cells.

**Item 4.** $H_t$ flips with $x_{-t}$ on every row, since $c_t$ does ([ConeScreening](ConeScreening.md),
`flip_center`) and $-t \ne t - 1$ for $t \ge 1$. So `tree_drop_of_flip` of QueryDepth, with the lift of
`center_tree_lift`, gives $D(H_t) = D(G_t) + 1$, and item 3 turns $D(H_t) = 2t$ into $D(G_t) = 2t - 1$.

The GF(2) degree: write $c_t$ with $x_{-t}$ white as $G(y, x_{t-1} \lor x_t)$, with
$G(y, u) = G_t(y, u)$ by item 1, and expand $x_{t-1} \lor x_t = x_{t-1} + x_t + x_{t-1} x_t$. A monomial of $G$ without
$u$ has no corner cell, and a monomial $m u$ of $G$ gives $m x_{t-1} x_t$ and two shorter ones. The kit's top monomial
$x_{-t+2} \cdots x_t$ of $c_t$ has coefficient 1 (`AlgebraicDegree.coef_center_top`, $t \ge 2$), so $G_t$ has the
monomial $x_{-t+2} \cdots x_{t-2} u$, of degree $2t - 2$. A monomial of $G_t$ on all $2t - 1$ of its cells would give
the monomial $x_{-t+1} \cdots x_t$ of degree $2t$ in $c_t$, against the kit's degree $2t - 1$
(`isGreatest_card_coef_center`). The real coefficient: summing over the pair $(x_{t-1}, x_t)$ with signs,
$1 \cdot G(y, 0) - 2 G(y, 1) + G(y, 1) = G(y, 0) - G(y, 1)$, so $\mu$ of $c_t$ with $x_{-t}$ white is $\pm\mu(G_t)$,
and $\mu(c_t) = 2\mu(c_t|_{x_{-t} = 0})$ up to sign since $c_t = x_{-t} \oplus g_t$.

**Item 5.** `query_adversary_sums.c` sums $(-1)^{|y|} g_t(y)$ over the $2^{2t}$ rows of $g_t$: the 9 rightmost cells
fill the 512 lanes of a vector, the others are walked in Gray code order with the leftmost cell flipping most often, and
a flip of the cell $x_{-t+m}$ recomputes only the $m + 1$ cells of each row of the cone that it reaches. The test
checks it against `query_depth.subcube_sums` with and without fixed cells, and the values for $t \le 17$ are those of
QueryDepth. $t = 20$ takes about three minutes on three threads and $t = 21$ about fifteen; each step of $t$
multiplies the time by about four.

## What it means

The right corner costs what an OR of two cells costs, and the adversary has no choice there. The question
$D(c_t) = 2t + 1$ for every $t$ is the same as asking that $G_t$, a function of $2t - 1$ cells of GF(2) degree
$2t - 2$, needs all its cells. Its monomial of degree $2t - 2$ above misses only the cell $u = x_{-t+1}$. The adversary
that answers each cell so that the GF(2) coefficient of the product of the free cells other than $u$ stays 1, and
answers $u$ white, forces every cell as soon as the tree reads $u$ before the last query (the function left then has
full GF(2) degree). Against a tree that reads $u$ last it guarantees nothing: its answers then keep only the value 1 of
the function left at $u = 0$, and that function may take the value 1 at $u = 1$ too. The real top coefficient covers
that case at every $t \le 21$ except $t = 14$, where QueryDepth's certificate of level 2 does.
[Adversary routes](../../negative-results/complexity/query-adversary-routes.md) records where the other routes stop.

The kit's `deriv_evol_right` says that the derivative along $x_t$ is 1 exactly when the diagonal left of the right edge
is white, which contains the second shield. The first shield, and the OR form with its consequences for the query
model, are not in the kit.

## Reproduce

```bash
python -m computations.query_adversary --max-t 21 --threads 3
```

The corner sums and the certificates take about five minutes on three threads for $t \le 20$, and $t = 21$ adds about
twenty.
