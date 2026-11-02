---
title: Self-similar restrictions, restricted top coefficients and congruences do not prove that the center needs its whole cone for every t
category: complexity
problems: [3]
status: negative
kind: dead-end
evidence: [computations/query_adversary.py, computations/query_adversary_sums.c, tests/test_query_adversary.py]
---

# Self-similar restrictions, restricted top coefficients and congruences do not prove that the center needs its whole cone for every t

**Question.** Write $c_t$ for the center after $t$ steps of Rule 30 as a function of the $2t + 1$ cells
$x_{-t}, \dots, x_t$ of an arbitrary row, $D(f)$ for the least depth of a decision tree for $f$, and
$\mu(f) = \sum_x (-1)^{|x|} f(x)$ for the top coefficient of the real polynomial of $f$, up to sign.
[QueryDepth](../../Rule30Open/Complexity/QueryDepth.md) proves $D(c_t) \ge 2t$; [CornerOr](../../Rule30Open/Complexity/CornerOr.md)
proves that $D(c_t) = 2t + 1$ if and only if $G_t$, the center with $x_{-t}$ and $x_{t-1}$ white, needs all its
$2t - 1$ cells, and computation gives $D(c_t) = 2t + 1$ for $t \le 22$. Can one of three routes prove it for every
$t$: (i) an induction through one step of the rule, carried by a restriction of $c_{t+1}$ that is a copy of $c_t$;
(ii) a fixed pattern of restrictions whose top coefficients are nonzero for every $t$; (iii) a congruence for $\mu$?

This is a question about the query model for an arbitrary row. Its answer, either way, does not bound the cost of the
single black cell's column, the row of the prize, where a tree reads nothing.

**Outcome.** Each route stops at a step named below. The stop of route (iii) and the corner part of route (ii) are
proved for every $t$; the rest is computed on the ranges given. The earlier routes (sensitivity, certificates, fixed
answers, lifting of general functions) are in [query-depth routes](query-depth-routes.md).

## (i) A copy of $c_t$ inside $c_{t+1}$

An induction would fix two of the $2t + 3$ cells of $c_{t+1}$ so that the rest is $c_t$ with its cells permuted and
negated, and then handle the two fixed cells by an adversary, as QueryDepth handles $x_{-t}$ and CornerOr the corner.

**Where it stops (computed, $t \le 5$).** `restriction_isomorphisms` takes each of the $4\binom{2t+3}{2}$ restrictions
of $c_{t+1}$ to two fixed cells and searches for a permutation of cells, negations of cells and a negation of the value
that turn it into $c_t$ (a backtracking search on the weights of pairs of cells, checked on the whole table). For
$t = 1$ ten of the 40 restrictions are copies of $c_1$. For $t = 2, 3, 4, 5$ none of the 84, 144, 220, 312 is. The
number of restrictions that need all their $2t + 1$ cells is 25, 49, 78, 117, 251 for $t = 1, \dots, 5$, by the exact
depths of `query_depth.exact_depth`.

The steps that do carry over are of one cell: $x_{-t}$ enters by XOR and the corner pair by OR. `pair_gates` lists the
pairs of cells through which a function factors by a gate of two inputs (the four cofactors at the pair are at most
two distinct functions). For $3 \le t \le 7$ the only such pair of $c_t$ is $(x_{t-1}, x_t)$, an OR, and $G_t$ has none,
so the corner step of CornerOr does not repeat inside $G_t$. (At $t = 2$, $c_2$ also has the XOR pair $(x_{-1}, x_0)$.)

## (ii) Restrictions with a nonzero top coefficient

A certificate of level $L$ (QueryDepth) asks, for every cell, a value whose restriction has a certificate of level
$L - 1$, and level 0 is $\mu \ne 0$, the Rivest-Vuillemin criterion: an odd-weight and even-weight count of 1-rows
that differ. A proof for every $t$ would need a rule that names these values and a reason why the coefficients they
give are nonzero.

**Where it stops (proved at the corner, computed elsewhere).**

- *The corner gives nothing beyond $\mu(c_t)$* (CornerOr, item 2, every $t$). Fixing $x_t$ or $x_{t-1}$ black gives
  $\mu = 0$ and white gives $\pm\mu(c_t)$, and the white answer is forced. So level 1 exists only where level 0 does,
  and a $t$ with $\mu(c_t) = 0$ needs level 2 at least; $t = 14$ is such a $t$.
- *Away from the corner, no rule is uniform.* With $g_t$ the center with $x_{-t}$ white and $R[k, b]$ the coefficient
  of $g_t$ with cell $k$ also fixed to $b$ (`kernel_sums`), the computation for $5 \le t \le 20$ gives:
  - both fixings of a cell vanish only at the two corner cells at $t = 14$;
  - fixing white vanishes at $x_{-1}, x_0$ ($t = 6$), $x_4$ ($t = 8$), $x_1$ ($t = 10$ and $t = 11$), $x_{-1}$
    ($t = 12$) and the corner at $t = 14$;
  - fixing black vanishes at the corner at every $t$ and at sporadic cells besides, for instance $x_{-1}, x_6$ at
    $t = 13$ and $x_9$ at $t = 20$.
  So neither the all-white nor the all-black answer gives level 1 at every cell, and the cells where they fail move
  with $t$.
- *The only coefficient with a reason is the second cell.* For $t \ge 3$, fixing $x_{-t+1}$ either way gives an odd coefficient, since
  the only GF(2) monomial of degree $2t - 1$ avoids it (`AlgebraicDegree.eq_Icc_of_coef_ne_zero` of the kit). Every
  other cell's restricted coefficient is even, because the restriction has GF(2) degree below its number of cells, and
  nothing found decides when it is 0. A fixed pattern with a nonzero coefficient for every $t$ would give only
  $D(c_t) \ge 2t + 1 - (\text{its number of fixed cells})$, which is $2t$ for one cell, the known bound.
- *Both corner cells white.* The coefficient of $g_t$ with $x_{t-1} = x_t = 0$, which appears in the certificates of
  level 2 below the forced white answer, is 0 at $t = 2, 3, 6$ and nonzero at the other $t \le 20$, $-394$ at
  $t = 14$ (`main`, last column).

## (iii) Congruences for $\mu$

**Where it stops (proved).** $\mu(c_{14}) = 0$, and 0 is divisible by every modulus, so no congruence can show
$\mu(c_t) \ne 0$ for every $t$. A congruence could only serve for restricted functions, and there it reduces to the
GF(2) normal form beyond its top degree:

$\mu(g_t) \equiv 2P_t \pmod 4$, where $P_t$ is the number of unordered pairs of monomials of the GF(2) normal form of
$g_t$ whose union is all $2t$ cells. Proof: $\mu(g) = |g^{-1}(1)| - 2\,|(g \land \pi)^{-1}(1)|$ with $\pi$ the parity
of the cells. By inclusion and exclusion for XOR, $|g^{-1}(1)| = \sum_{A} (-2)^{|A| - 1} 2^{n - |\cup A|}$ over the
nonempty sets $A$ of monomials, which mod 4 is $2M + 2P$, with $M$ the number of monomials of degree $n - 1$, since $g$
has no monomial of degree $n = 2t$. And the parity of $|(g \land \pi)^{-1}(1)|$ is the GF(2) top coefficient of
$g \cdot \sum_i x_i$, which is $M$ mod 2, so $2\,|(g \land \pi)^{-1}(1)| \equiv 2M \pmod 4$ and the two terms in $M$
cancel. (For $t \ge 3$ the kit gives $M = 1$.)
`covering_pairs` checks the congruence for $t \le 10$ ($P_t$ = 7, 27, 187, 651, 6484, 51121, 560655, 4146014,
39161255 for $t = 2, \dots, 10$).

The residues $\mu(g_t)/2 \bmod 2$ for $2 \le t \le 21$ are 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0,
with no pattern in the binary digits of $t$ ($t = 8$ gives 1 and $t = 16$ gives 0). The parity of $P_t$ is a count of
covering pairs in a normal form with millions of monomials, and nothing found makes it computable without the form.

## What it means

The left cell and the corner pair are settled for every $t$: the center flips with $x_{-t}$ on every row, and sees
$x_{t-1}, x_t$ through an OR. For $3 \le t \le 7$ no other pair of cells enters through a gate of two inputs. What is
left is $G_t$, of $2t - 1$ cells and GF(2) degree $2t - 2$, and the case where a tree keeps the cell $x_{-t+1}$ for
last. Every tool tried for that case reads a real coefficient, of $c_t$ or of its restrictions, and on the computed
range those coefficients follow no pattern: they change sign, $\mu(c_t)$ vanishes at $t = 14$, and their residues mod 4
are counts of covering pairs in the normal form. As a heuristic, a proof for every $t$ would need an adversary whose
answers follow the dynamics of the rule over many steps rather than a coefficient.
[Evasiveness routes](query-evasive-routes.md) follows the case of $x_{-t+1}$ last through the derivative along that
cell, and the right corner one step further in, and records where those routes stop.

## Reproduce

```bash
python -m computations.query_adversary --routes 5 --pairs 10 --max-t 20 --threads 1   # about 20 minutes
```
