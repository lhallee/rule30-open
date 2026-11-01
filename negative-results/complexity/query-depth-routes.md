---
title: Sensitivity, certificates, fixed answers and one-step lifting do not show that the center needs its whole cone
category: complexity
problems: [3]
status: negative
kind: barrier
evidence: [computations/query_certificates.py, tests/test_query_certificates.py, computations/query_depth.py]
---

# Sensitivity, certificates, fixed answers and one-step lifting do not show that the center needs its whole cone

**Question.** Write $c_t$ for the center after $t$ steps of Rule 30 as a function of the $2t + 1$ cells
$x_{-t}, \dots, x_t$ of an arbitrary row, and $D(c_t)$ for the least depth of a decision tree that computes it.
[QueryDepth](../../Rule30Open/Complexity/QueryDepth.md) proves $D(c_t) \ge 2t$ for $t \ge 2$ and computes
$D(c_t) = 2t + 1$ for $t \le 17$. Can $D(c_t) = 2t + 1$ be proved for every $t$ by an adversary argument: an answering
strategy that keeps $c_t$ non-constant on the unread cells until all $2t + 1$ are read? Three routes were tried.

This is a question about an arbitrary input row. Its answer, either way, does not bound the cost of the single black
cell's column, the row of the prize, where a tree reads nothing.

**Outcome.** Each route stops at a step named below. Two of the stops are proved: certificate complexity is at
most $2t$ for every $t$ (in Lean), and an exhaustive computation over the functions of 3 cells shows that the reduction
through one step of the rule fails for general functions. The others are computed on the ranges given.

## 1. Sensitivity and certificate complexity

$D(f) \ge C(f) \ge \mathrm{bs}(f) \ge s(f)$, with $C$ the certificate complexity, bs the block sensitivity and $s$ the
sensitivity. A row at which $c_t$ is sensitive to all $2t + 1$ cells would give $D(c_t) = 2t + 1$ at once.

**Where it stops (proved).** [RightCorner](../../Rule30Open/Complexity/RightCorner.md): for $t \ge 2$ no row is
sensitive to all three cells $t - 2, t - 1, t$, so every row has a certificate of $2t$ cells and
$s(c_t) \le \mathrm{bs}(c_t) \le C(c_t) \le 2t$. The computed values are lower still: $C(c_t) = 7, 11, 13$ at
$t = 4, 6, 7$, below the bound $2t$ that QueryDepth already proves, and $s(c_t) = 21$ at $t = 12$ against $25$ cells.

## 2. Adversaries with fixed answers, and induction through one step

**Fixed answers.** Suppose an adversary answers each cell of a set $Z$ with a value fixed in advance. A tree can read
the cells outside $Z$ first and then all of $Z$ but one cell $j$, any $j$ it likes; the adversary wins only if the row
it has built is sensitive to $j$. So the row is sensitive to every cell of $Z$, and $|Z| \le s(c_t)$: an adversary has
to vary its answer, with the history of the game, at $2t + 1 - s(c_t)$ cells at least (3 at $t = 10$, 4 at $t = 12$).

Computed (`fixed_answer_cells`, $t \le 5$, by the game over all $3^{2t+1}$ partial rows): a fixed answer at the single
cell $x_{-t}$ always works, with either value, and at the two rightmost cells $x_{t-1}$ and $x_t$ no fixed answer
works for $2 \le t \le 5$. An adversary fixed everywhere except $x_{t-1}$ and $x_t$ needs a row sensitive to all of
$x_{-t}, \dots, x_{t-2}$; such rows exist for $t \le 5$ (8, 24, 12, 8, 6 of them) and none exists for
$6 \le t \le 12$ (`sensitivity_profile`). So for $6 \le t \le 12$ the answers must depend on the history at some cell
left of $x_{t-1}$ as well: the answers cannot be those of one fixed row at every cell but the two rightmost.

**Induction through one step.** One step of the rule maps the $2t + 1$ cells onto the $2t - 1$ cells of the next
cone, $y_j = x_{j-1} \oplus (x_j \lor x_{j+1})$, and $c_t = c_{t-1}(y)$. An induction on $t$ would follow from a
reduction that turns every tree for $F(y(x))$ into a tree for $F$ two levels shallower, for every $F$ that needs all
its cells. No such reduction exists for general $F$ (`lift_failures`): of the 194 functions of 3 cells that need 3
queries, 24 become functions of 5 cells that need fewer than 5 after one step. The reduction would have to use
properties of $c_{t-1}$ beyond needing all its cells, and none was found.

## 3. The top real coefficient

A tree of depth $d$ computes a real polynomial of degree at most $d$, so a nonzero coefficient of
$x_{-t} \cdots x_t$, which is $\pm\mu(c_t)$ with $\mu(f) = \sum_x (-1)^{|x|} f(x)$, forces depth $2t + 1$.

**Where it stops (computed).** $\mu(c_{14}) = 0$ (QueryDepth, `computations/query_depth.py`). QueryDepth closes $t = 14$
with certificates of level 2: restrictions of one or two cells with nonzero top coefficient. The values of $\mu(c_t)$
for $t \le 17$ change sign with no pattern in the table there, and no closed form for them or for the coefficients of
the restricted functions is known, so this route gives a finite range of $t$ only. The GF(2) degree, the kit's route,
stops at $2t - 1$ because the only monomial of that degree avoids the two leftmost cells; QueryDepth's lift through the
leftmost cell recovers one of them and no more.

## What it means

The three standard lower-bound tools that do not adapt to the answers (sensitivity, block sensitivity, certificates)
are capped at $2t$ for every $t$, the bound already proved. A proof of $2t + 1$ for every $t$ needs an adversary whose
answers depend on the history at several cells, or a reason why a real coefficient of some restriction is nonzero for
every $t$. The right edge is where the difficulty sits: the left edge is a cell the center flips with on every row,
while no row makes the center depend on all of the three rightmost cells.

## Reproduce

```bash
python -m computations.query_certificates --max-s 12 --max-c 7 --max-fixed 5   # about 30 seconds
python -m computations.query_depth --exact 6 --max-t 17                         # mu(c_t), about twelve minutes
```
