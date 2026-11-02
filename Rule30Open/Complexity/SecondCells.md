---
title: The derivative of the center along the second cell of its cone is the parity of a diagonal, and the right corner repeats one step in as an AND
category: complexity
problems: [3]
status: proved
lean: Rule30Open.Complexity.SecondCells
headline: [center_flip_second, second_derivative_flip, center_step_corner, center_second_shield, center_second_and]
kit: refines
kit_modules: [Rule30Equivalents.AlgebraicDegree, Rule30Equivalents.QueryComplexity]
evidence: [computations/query_evasive.py, computations/query_evasive_sums.c, tests/test_query_evasive.py]
---

# The derivative of the center along the second cell of its cone is the parity of a diagonal, and the right corner repeats one step in as an AND

Write $c_t(x)$ for the center cell after $t$ steps of Rule 30 from a row $x$, a Boolean function of the $2t + 1$ cells
$x_{-t}, \dots, x_t$ of its cone, and $D(f)$ for the least depth of a decision tree that computes $f$.
[QueryDepth](QueryDepth.md) and [CornerOr](CornerOr.md) settle the two outer cells of each side: the center flips with
$x_{-t}$ on every row, and sees $x_{t-1}, x_t$ only through their OR. So $D(c_t) = 2t + 1$ if and only if every tree for
$G_t$, the center with $x_{-t}$ and $x_{t-1}$ white, reads all its $2t - 1$ cells on some row; the open case is a tree
that reads $u = x_{-t+1}$ last. This entry proves what the next cell on each side contributes.

This is a query model for an arbitrary input row. It does not bound the cost of the single black cell's column, the
row of the prize, where a tree reads nothing.

## Statement

Write $x^{(s)}_j$ for the cell $j$ after $s$ steps.

1. **The derivative along the second cell** (Lean, every $t$, every row). Flipping $x_{-t+1}$ changes the center by
   $$\partial_u c_t(x) = t + \sum_{s=0}^{t-1} x^{(s)}_{-t+2+s} \pmod 2$$
   (`center_flip_second`, with `diagPar`). The cells $x^{(s)}_{-t+2+s}$ are the diagonal two cells inside the left edge
   of the cone, and the left edge of the cone of the cell $x^{(t-1)}_1$. The general form `flip_second_cell` holds for
   a flip of any cell $a$ and the cell $a - 1 + s$ after $s$ steps.
2. **Its dependence on the third cell** (Lean, every $t$). Flipping $x_{-t+2}$ changes $\partial_u c_t$ by
   $t \bmod 2$ on every row (`second_derivative_flip`, from `diagPar_flip`): for odd $t$ the derivative flips with
   $x_{-t+2}$ on every row, and for even $t$ it does not depend on $x_{-t+2}$.
3. **One step, then the next corner** (Lean, $t = n + 2 \ge 2$). With $y$ the row after one step,
   $c_t(x) = c_{t-1}(y')$, where $y'$ is $y$ with $y'_{t-2} = 0$ and $y'_{t-1} = y_{t-2} \lor y_{t-1}$
   (`center_step_corner`).
4. **The second corner** (Lean, $t = n + 2$). Let $x_{t-1} = 0$.
   - `center_second_shield`: if $x_{t-3} \ne x_{t-2}$, flipping $x_t$ does not change the center.
   - `center_second_and`: if $x_{t-3} = 1$, the center equals the center of the row with $x_{t-2}$ set to
     $x_{t-2} \land x_t$ and $x_t$ set to 1: it sees $x_{t-2}, x_t$ only through their AND.
5. **Consequences for $G_t$** (paper, from items 1 to 4). Let $Q_t = \partial_u G_t$, a function of the other $2t - 2$
   cells of $G_t$, and $Q'_t$ the same with $L = x_{-t+2}$ white, a function of the $2t - 3$ cells
   $x_{-t+3}, \dots, x_{t-2}, x_t$.
   - $Q_t = (t \bmod 2)\,L \oplus Q'_t$, so for odd $t$ a tree reads $L$ on every branch of $Q_t$ and
     $D(Q_t) = D(Q'_t) + 1$, and for even $t$ $Q_t$ ignores $L$.
   - $Q'_t = (t \bmod 2) \oplus G_{t-1} \oplus W_t$, with $G_{t-1}$ read on the cells shifted one to the right and
     $W_t = \sum_{s=1}^{t-2} x^{(s)}_{-t+2+s}$ a function of $x_{-t+3}, \dots, x_{t-2}$ that does not see $x_t$.
   - $G_t$ sees $x_t$ only through $(x_{t-3} \oplus x_{t-2}) \lor (x_{t-2} \oplus x_t)$, which is 0 exactly when
     the three cells agree.
6. **Computed** (`computations/query_evasive.py`). The top real coefficient $\mu(Q'_t) = \sum_y (-1)^{|y|} Q'_t(y)$:

| $t$ | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| $\mu(Q'_t)$ | 0 | −2 | 2 | −2 | −10 | −6 | 6 | 4 | 10 | −52 | 50 | 6 | −46 | −96 | 38 | −418 | 98 | 224 | 818 |

So $Q'_t$ needs all its $2t - 3$ cells for $4 \le t \le 21$ by the Rivest-Vuillemin criterion, and for $t = 3$ by the
exact depth; the exact depths agree for $t \le 8$.

## Proof

**Item 1.** Flip $x_a$ and follow the difference. Since $x^{(s+1)}_j = x^{(s)}_{j-1} \oplus (x^{(s)}_j \lor
x^{(s)}_{j+1})$, the cell $a + s$ flips at every time (left permutivity, `front_xor` of
[ConeScreening](ConeScreening.md)), and the cells right of $a + s$ do not change (`evo_local`). Write $\delta_s$ for
the change of the cell $a - 1 + s$; $\delta_0 = 0$. One step gives the cell $a + s$ from the cells $a - 1 + s$ (changed
by $\delta_s$), $a + s$ (flipped) and $a + s + 1$ (unchanged, call it $e_s$):
$\delta_{s+1} = \delta_s \oplus (\lnot b \lor e_s) \oplus (b \lor e_s) = \delta_s \oplus \lnot e_s$, whatever
$b = x^{(s)}_{a+s}$ is. So $\delta_s = \sum_{r < s} (1 \oplus x^{(r)}_{a+1+r})$ (`flip_second_cell`). With $a = -t + 1$
and $s = t$ the cell $a - 1 + s$ is the center, and $a + 1 + r = -t + 2 + r$ (`center_flip_second`). The kit's
`AlgebraicDegree.deriv_evol_diag_succ` is the step $\delta_s \mapsto \delta_{s+1}$, stated for the derivative in its
Mathlib-based equivalent forms; it uses it to bound the GF(2) degree.

**Item 2.** The cell $x^{(r)}_{-t+2+r}$ is the front cell of a flip of $x_{-t+2}$, so it flips with it on every row
(`front_xor`). The sum of item 1 has $t$ terms, so it flips $t$ times (`diagPar_flip`, by induction on the number of
terms, with `odd_succ`).

**Item 3.** $t$ steps from $x$ are $t - 1$ steps from $y$ (`evo_succ_left`), and CornerOr's `center_corner_or` at
$t - 1$ applies to $y$.

**Item 4.** Item 3 reads the center from the cells $y_j$, $j \le t - 3$, and the OR $y_{t-2} \lor y_{t-1}$. With
$x_{t-1} = 0$, $y_{t-2} = x_{t-3} \oplus x_{t-2}$ and $y_{t-1} = x_{t-2} \oplus x_t$, and $y_j$ for $j \le t - 3$
reads only cells left of $t - 1$ (`coneStep_agree`). Two rows with the same OR and the same $y_j$ for $j < t - 2$ have
the same center (`center_of_step_agree`).

- If $x_{t-3} \ne x_{t-2}$ the OR is 1 whatever $x_t$ is, and a flip of $x_t$ changes no $y_j$ with $j \le t - 2$.
- If $x_{t-3} = 1$ then $y_{t-3} = \lnot x_{t-4}$ does not read $x_{t-2}$, and the OR is
  $\lnot x_{t-2} \lor (x_{t-2} \oplus x_t) = \lnot(x_{t-2} \land x_t)$, the same for the row with $x_{t-2}$ set to the
  AND and $x_t$ to 1.

**Item 5.** Item 1 holds on every row, in particular with $x_{-t}$ and $x_{t-1}$ white, and the sum does not read
$x_{-t}$ or $u$. Item 2 is the first claim, with QueryDepth's `tree_drop_of_flip` and `center_tree_lift`'s argument
for the depth. In the sum, the term $s = 0$ is $L$; the term $s = t - 1$ is the cell $x^{(t-1)}_1$, the center of the
cone $x_{-t+2}, \dots, x_t$, which with its leftmost cell $L$ and its corner cell $x_{t-1}$ white is $G_{t-1}$ shifted
one cell right; the terms $1 \le s \le t - 2$ have cones $x_{-t+2}, \dots, x_{-t+2+2s}$, left of $x_{t-1}$. The third
claim is item 4 read through item 3. The code checks the first two claims on the truth tables for $t \le 9$
(`derivative_profile`, `previous_level_split`) and the third for $t \le 12$ (`second_corner_holds`).

**Item 6.** `query_evasive_sums.c` sums $(-1)^{|y|} Q'_t(y)$ over the $2^{2t-3}$ rows: it runs the cone of the cell
$x^{(t-1)}_1$ with $L$ and $x_{t-1}$ white, 512 rows to a vector, walks the other cells in Gray code order and
recomputes only the forward cone of the flipped cell, and adds the left edge of the cone at the times $1, \dots, t - 1$.
The test checks it against the truth table of $Q_t$ at $t = 7$ and $t = 8$, at $t = 8$ with the Gray-code walk over
five and over three cells, and the table against the diagonal parity, computed independently on the cone of
$x^{(t-1)}_1$, for $t \le 6$, and the formula of item 1 against plain runs of the rule on every row for $t \le 3$.
One thread takes about four minutes at $t = 21$; each step of $t$ multiplies the time by about four.

## What it means

For the open case of CornerOr, a tree that reads $u$ last, the adversary needs the row it builds on the other
$2t - 2$ cells to end with $Q_t = 1$. Items 1, 2 and 5 identify $Q_t$: a parity of $t$ cells along one diagonal, a copy
of $G_{t-1}$ plus nested centers. For odd $t$ an adversary that makes every tree read all of $Q_t$'s cells wins that
case, and item 6 with the exact depth at $t = 3$ gives one for every odd $t \le 21$; for even $t$, $Q_t$ ignores $L$
and does not suffice. On the right, the corner step of CornerOr repeats once, as an AND, but only after $x_{t-3}$ is
answered black.
[Evasiveness routes](../../negative-results/complexity/query-evasive-routes.md) records why neither fact closes
$D(c_t) = 2t + 1$ for every $t$: the adversaries for the two orders of reading $u$ do not combine, and the merged
function after the second corner has no further gate.

The kit has the one-step form of item 1 (`AlgebraicDegree.deriv_evol_diag_succ`), which it sums only at the level
of GF(2) coefficients (`coef_deriv_evol_eq_zero`), and the derivative along the right end of the cone
(`deriv_evol_right`). The summed form in this repository's frame, item 2, and the second corner are not in the kit's
core Lean or its equivalent forms.

## Reproduce

```bash
python -m computations.query_evasive --max-t 9 --structure 12 --sums 21 --threads 1
```

It takes about ten minutes; `--max-t 7 --structure 7 --sums 12` takes seconds.
