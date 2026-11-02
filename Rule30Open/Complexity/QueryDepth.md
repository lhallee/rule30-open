---
title: A decision tree for the center cell from an arbitrary row spends exactly one query on the leftmost cell, so with the kit's degree bound it reads at least 2t cells; computation gives all 2t + 1 for t ≤ 17
category: complexity
problems: [3]
status: proved
lean: Rule30Open.Complexity.QueryDepth
headline: [depth_restrict_succ_le, eval_restrict, tree_drop_of_flip, center_tree_drop, center_tree_lift]
kit: refines
kit_modules: [Rule30Equivalents.QueryComplexity, Rule30Equivalents.AlgebraicDegree]
evidence: [computations/query_depth.py, tests/test_query_depth.py]
---

# A decision tree for the center cell from an arbitrary row spends exactly one query on the leftmost cell, so with the kit's degree bound it reads at least 2t cells; computation gives all 2t + 1 for t ≤ 17

Write $c_t(x)$ for the center cell after $t$ steps of Rule 30 from a row $x$, a Boolean function of the $2t + 1$ cells
$x_{-t}, \dots, x_t$ of its cone. A *decision tree* reads cells one at a time, each choice depending on the answers so
far, and then answers. Its *depth* is the largest number of cells it reads on one branch. Write $D(f)$ for the least
depth of a tree that computes $f$. The kit's equivalent forms prove $2t - 1 \le D(c_t) \le 2t + 1$ for $t \ge 2$
(`QueryComplexity.le_depth_of_eval_eq`, `exists_depth_eq`). This entry narrows that range to $\{2t, 2t + 1\}$ for every
$t \ge 2$, and settles it at $2t + 1$ for $t \le 17$ by computation.

## Statement

Write $g_t(x) = c_t(x \text{ with } x_{-t} := 0)$, a function of the $2t$ cells $x_{-t+1}, \dots, x_t$.

1. **One query for the leftmost cell, exactly** (Lean). $D(c_t) = D(g_t) + 1$ for every $t$. In detail:
   - `depth_restrict_succ_le`, `tree_drop_of_flip`: if a function $f$ flips with a cell $u$ on every row, then every
     tree $T$ for $f$ gives a tree for $f$ with $u$ held white whose depth is at most $\operatorname{depth} T - 1$.
     The tree is `T.restrict (whiteAt u)`: at each query of $u$ it follows the white branch and drops the query
     (`eval_restrict`).
   - `center_tree_drop`: the case $f = c_t$, $u = -t$, by `flip_center` of
     [ConeScreening](ConeScreening.md). `center_tree_lift` is the converse: read $x_{-t}$, then run a tree for $g_t$
     and answer its value or its complement, since $c_t = x_{-t} \oplus g_t$ (`center_decomp`).
2. **Depth at least $2t$** (item 1 and the kit). For $t \ge 2$, every tree that computes $c_t$ on every row has
   depth at least $2t$.
3. **Depth $2t + 1$ on a finite range** (computed). For $1 \le t \le 17$, $D(c_t) = 2t + 1$: every tree reads the
   whole cone on some row.
4. **Control** (proved on paper, computed for $t \le 6$). For Rule 90, $D(c_t) = 2^{s(t)}$, with $s(t)$ the number
   of 1s in the binary digits of $t$. So the tree for $t = 2^k$ reads two cells.

## Proof

**Item 1.** Let $\rho$ be a partial row with $\rho(u) = 0$. Call a row $x$ a fit for $\rho$ when it agrees with $\rho$
on every fixed cell other than $u$. Restricting a tree to $\rho$ keeps the queries of free cells, fixes each such cell
on its two branches, and follows the fixed branch at a fixed cell. Suppose the tree flips with $u$ on every fit. Then
the depth drops by at least one, by induction on the tree.

- A leaf does not flip on the fit that copies $\rho$ and is white elsewhere, so the hypothesis rules leaves out.
- At a query of a fixed cell, $u$ included, the restriction is that of a subtree, whose depth is at most the depth
  of the subtree (`depth_restrict_le`), one less than the depth of the tree.
- At a query of a free cell $i \ne u$, a fit for $\rho$ with $x_i = b$ runs into the subtree of $b$, and setting $u$
  does not change $x_i$. So each subtree flips with $u$ on the fits for $\rho$ with $i := b$, and the induction gives
  both drops.

**Item 2.** Let $T$ compute $c_t$, and let $T'$ be the tree of item 1 for $g_t$, with
$\operatorname{depth} T' \le \operatorname{depth} T - 1$. Write $M = \{-t + 2, \dots, t\}$, of size $2t - 1$. The
coefficient of $\prod_{i \in M} x_i$ in the GF(2) polynomial of $c_t$ is 1 (`AlgebraicDegree.coef_center_top`). Holding
the cell $-t \notin M$ white does not change it (`QueryComplexity.coef_update_false`), so it is also 1 for $g_t$. A tree
of depth $d$ computes a polynomial of degree at most $d$ (`QueryComplexity.coef_eval_eq_zero`). So
$\operatorname{depth} T' \ge 2t - 1$ and $\operatorname{depth} T \ge 2t$. The kit's argument stops at $2t - 1$ because
the monomial $M$ avoids the two leftmost cells. Item 1 recovers one of them: the cell $-t$ is read on every branch and
contributes nothing to $M$.

The kit's `QueryComplexity.DecisionTree ℤ` and `evol` are the same objects as `QTree` and `evo` here: the trees have
the same constructors, `eval` and `depth`, and `evo x t p = evol x t p` follows by induction on `t` with `rfl` at each
step. The two are not linked in Lean, because the kit's equivalent forms need Mathlib and this repository builds
only the kit's core. So item 2 is a combination, on paper, of two Lean proofs.

**Item 3.** A tree of depth $d$ is a real polynomial of degree at most $d$: a sum over its 1-leaves of products of at
most $d$ factors $x_i$ or $1 - x_i$. In the real multilinear polynomial of $f$ on $n$ variables, the coefficient of
$x_1 \cdots x_n$ is $\pm\mu(f)$, with $\mu(f) = \sum_x (-1)^{|x|} f(x)$. So $\mu(c_t) \ne 0$ forces
$D(c_t) = 2t + 1$. Since $c_t = x_{-t} \oplus g_t$, $\mu(c_t) = 2\mu(g_t)$, and the code sums over the $2^{2t}$ rows of
$g_t$ on bit-sliced words:

| $t$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| $\mu(c_t)$ | −2 | −4 | −4 | −4 | −4 | 8 | −4 | −20 | 16 | 12 | −16 | 116 | 12 | 0 | 96 | −280 | 132 |

At $t = 14$ the top coefficient is 0, so the depth needs a second step. The least depth satisfies
$D(f) = 1 + \min_k \max_b D(f|_{x_k = b})$. So if every cell $k$ has a value $b$ for which $f|_{x_k = b}$ needs all its
cells, then $f$ needs all of them. For $g_{14}$, 26 of the 28 cells have such a $b$ with $\mu(g_{14}|_{x_k = b}) \ne 0$.
The other two are the rightmost cells, $x_{13}$ and $x_{14}$, and each of them has a $b$ for which every further cell
has such a fixing in turn. This is a certificate of level 2 in the code. So $g_{14}$ needs 28 queries and $c_{14}$
needs 29. The exact depths from the dynamic program over the $3^{2t+1}$ subcubes agree for $t \le 6$.

**Item 4.** Rule 90 is linear: $c_t = \bigoplus_i \binom{t}{i} x_{-t + 2i} \pmod 2$. By Lucas' theorem it is the
parity of $2^{s(t)}$ cells, and a parity of $m$ cells needs $m$ queries.

## What it means

For a row given as input, no algorithm that reads cells one at a time and adapts can skip a cell of the light cone of
the center at $t \le 17$, and none can skip more than one at any $t$. This separates Rule 30 from the linear Rule 90,
which reads $2^{s(t)}$ cells, two at every $t = 2^k$. The spacetime bounds of [restricted
models](../../negative-results/complexity/restricted-models.md) were met by Rule 90 too, and this one is not.

It is not a lower bound for Problem 3. The bound is linear in $t$ and the obvious algorithm meets it. It concerns
arbitrary rows, and for the single black cell, the prize's row, a tree reads nothing: every cell is known. The kit says
the same of its own bound. The pull request #72 of the kit bounds the head span of a machine that reads the digits of
$n$, a different model ([kit pull requests](../../literature/kit-pull-requests.md)).

**Open.** $D(c_t) = 2t + 1$ for every $t$. The GF(2) degree cannot show it. The only monomial of degree $2t - 1$
is $M$, so after an adversary fixes a cell other than $x_{-t+1}$ the remaining function has GF(2) degree below its
number of cells, and a certificate must use the real coefficients. Those change sign without a pattern and vanish at
$t = 14$. [CornerOr](CornerOr.md) extends the computation to $t \le 22$ and reduces the open case to one
function $G_t$ of $2t - 1$ cells needing all its cells.

## Reproduce

```bash
python -m computations.query_depth --exact 6 --max-t 17
```

It takes about twelve minutes, eight of them at $t = 17$; `--max-t 13` takes seconds. The test
`tests/test_query_depth.py` checks the subcube program against a plain recursion over partial rows, the bit-sliced
sums against direct sums over the truth table with and without fixed cells, Rule 30's depth $2t + 1$ and Rule 90's
$2^{s(t)}$ for $t \le 4$, and the certificates for $t \le 6$.
