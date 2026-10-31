---
title: Rows of radius up to 26 keep an alternating center from time 0 for at most 36 steps, with no law like the constant center's radius plus 2
category: period-two
problems: [1]
status: computed
formalization: wanted
evidence: [computations/alternating_horizon.py]
---

# Rows of radius up to 26 keep an alternating center from time 0 for at most 36 steps, with no law like the constant center's radius plus 2

Condrey (2026) proves that a nonzero row with support in $[-w, w]$ keeps its center constant for at most $w + 2$ steps
from time 0, and Adler (2026) formalizes the bound in Lean. The same count for the alternating center, over every row
with support in $[-A, A]$, is not $A + 2$ and shows no law: it is $36$ at every $A$ from 19 to 26, with a white run of the
forced left half behind each value. The three steps of Condrey's proof carry over one, uniqueness, and lose the other
two. This restates the open problem; it proves nothing about it.

## Result

Let $c$ be the center word (`0`, `1`, `10`), $R$ a right half, and $\Psi_c(R)$ the one left half that keeps the center on
$c$ forever against $R$ (Condrey's Lemma 1, from left permutivity, the kit's `Rule30ZeroBoundary.pivot`; for
$1, 0, 1, \dots$ the kit's `Psi_unique`, [the white right half](white-right-half.md)). A left half of width $M$
that agrees with $\Psi_c(R)$ on its first $M$ cells keeps the center on $c$ at the times $0, \dots, d - 1$, where $d$ is
the first black depth of $\Psi_c(R)$ beyond $M$, and no left half of width $M$ does better (for $1, 0, 1, \dots$ the
kit's `truncation_death`; for the other words the same argument from left permutivity). So the longest run over the rows with support in $[-A, A]$ is the maximum of $d$ over the
$2^A$ right halves and the phases of $c$. `computations/alternating_horizon.py` computes it for all of them at once.

1. **Condrey's bound, reproduced.** For $c = 0$ the longest run is $A + 1$ for even $A$ and $A + 2$ for odd $A$, reached
   by $2^A - 1$ rows; for $c = 1$ it is $A + 2$ for even $A$ and $A + 1$ for odd $A$, by $2^A$ rows; for $A \le 14$ (the
   test checks $A \le 8$, and runs against stepping every row of radius at most 4). Condrey's closed forms for $\Psi_0(R)$ and
   $\Psi_1(R)$ agree with the computed $\Psi$ for every $R$ of at most 9 cells to depth 12.
2. **The alternating center, $c = 1, 0, 1, \dots$ or $0, 1, 0, \dots$.** The longest run over rows with support in
   $[-A, A]$, counted from time 0, is

   | $A$ | 1 to 4 | 5 | 6, 7 | 8 | 9 to 13 | 14 | 15 | 16 to 18 | 19 to 26 |
   |---|---|---|---|---|---|---|---|---|---|
   | longest run | 7 | 9 | 10 | 15 | 17 | 20 | 22 | 26 | 36 |

   It is a step function that jumps when a right half with a long white run in $\Psi$ enters. The value 36 at
   $A = 19$ is the right half $R = 58$, black in columns 2, 4, 5 and 6, with the first 19 cells of $\Psi(R)$ as its left
   half: a row with support in $[-19, 6]$ whose center follows $1, 0, 1, \dots$ for 36 steps (stepped as a whole row
   here). In the other phase the best left half for $R = 58$ runs 20 steps. The extra over the radius is at least 3 and at most 17 (at $A = 19$), and 10 at $A = 26$, where no right half of
   at most 26 cells exceeds 36. Every $A$ has longest run at least $A + 1$ (truncate $\Psi$ at width $A$; Condrey's
   Section 5 gives $H(2, w) \ge w$), and no upper bound in $A$ is known: one for every $A$ is the finite-configuration
   period-two statement (below).
3. **Tails.** Over all 4,096 right halves of at most 12 cells, $\Psi$ computed to depth 1,500 is eventually periodic with
   a period of at most 200 for every right half when $c = 0$ (the stripe, or the zero row for $R = 0$) and $c = 1$ (the
   stripe), and for 110 of them when $c = 1, 0, 1, \dots$ and 118 when $c = 0, 1, 0, \dots$, with period 7, 14 or 28 (7 is
   the ether; the others were not identified). The other 3,986 and 3,978 right halves show no period.
4. **The decision-diagram width of $\Psi$ grows to depth 20 in the column order.** For a cell of $\Psi_c(R)$ at a fixed depth, count the distinct functions of
   the remaining cells of $R$ left after the first $k$ cells are fixed, at the widest $k$ (the width of its decision
   diagram in the order of the columns). For $c = 0$ it is 2 at every depth to 20. For $c = 1$ it is 1, since $\Psi_1$ does not
   depend on $R$ (Condrey's Theorem 3). For $c = 1, 0, 1, \dots$ it is, at the even depths 2 to 20,
   $2, 3, 5, 6, 9, 16, 25, 40, 69, 105$ (heuristic: growing by a factor of about 1.6 every two depths) and, at the odd depths 1 to 19, $1, 2, 2, 4, 3, 4, 12, 27, 27, 45$.

## What the first step gives and the others do not

- **Carries over: uniqueness** (Condrey's Lemma 1). For any center word the left half is determined by the right half.
- **Fails: an explicit forced left half.** For $c = 0$ the column beside the center satisfies $x_{-1}(t) = x_1(t)$, and
  column 1 is an OR latch, so the odd cells of $\Psi_0(R)$ are the prefix OR of $R$, and the even cells mark the first
  1 of $R$ when it lies in an even column, so beyond $R$ it is the stripe. For $c = 1$ the OR in the
  center's update is 1 and $\Psi_1$ does not depend on $R$. Beside an alternating $c$ the center sees $x_1$ only at the
  times $t$ with $c(t) = 0$ (odd $t$ for $1, 0, 1, \dots$; even $t$ for $0, 1, 0, \dots$), and at the times with
  $c(t) = 1$, $x_1(t + 1) = \lnot(x_1(t) \lor x_2(t))$, so column 1 is not a latch. $\Psi(R)$ is the constrained row
  $\Theta$ whose free bits are the complement of `u R` (the kit's `Psi_free`). Its cells are the forced bits of
  [the shift model](shift-model.md) composed with $R \mapsto$ `u R`; item 4 measures the composite.
- **Fails: a nonzero fixed tail.** Every $\Psi_0(R)$ with $R$ nonzero, and every $\Psi_1(R)$, ends in the stripe, which
  has infinitely many 1s (Condrey's Theorems 2 and 3, Corollaries 4 and 5). $\Psi_c(R)$ for the alternating $c$ ends in a periodic tail for 2 to 3 percent of the
  right halves of at most 12 cells (an infinite left half, not a finite row) and otherwise shows no period.
- **No weaker horizon statement.** Suppose every nonzero row with support in $[-A, A]$ kept its center alternating for at
  most $f(A)$ steps from time 0, for some finite $f(A)$ at every $A$. A row that alternates from time $T$ on becomes, at
  time $T$, a nonzero row of support radius $A + T$ that alternates from time 0 forever, against $f(A + T)$. So a
  finite $f$ for every $A$ is the finite-configuration period-two statement (the kit's CQ01, with
  `CQ01_iff_no_finite_alternating` and `CQ01_iff_Psi`), and an explicit $f$ is no easier than it; the kit's
  `alternates_long` shows that $f$ is unbounded in $A$. What the table
  adds is the range: the finite horizon is known for every row with support in $[-A, A]$ up to $A = 26$, and
  [the 120-cell finding](alternating-within-120.md) bounds it for left halves of up to 120 cells.

## Reproduce

```bash
python -m computations.alternating_horizon table --max-radius 14 --words 0 1       # seconds
python -m computations.alternating_horizon table --max-radius 26 --words 10        # about 9 min
python -m computations.alternating_horizon profile --cells 20 --depth 20 --words 0 10   # about 5 min
python -m computations.alternating_horizon tails --cells 12 --depth 1500           # about 2 min
```

`tests/test_alternating_horizon.py` checks the NumPy bit slices against the big-integer $\Psi$ of
[coupled.py](../../computations/coupled.py), Condrey's closed forms, every run against stepping whole rows (right halves
of 4 and 5 cells, left widths 4 and 3), the table for $c = 0, 1$ against Condrey's $A + 1$, $A + 2$ and the counts
$2^A - 1$ and $2^A$, and for $c = 1, 0, 1, \dots$ at $A = 5$ and $6$ against stepping every row, and a decision-diagram
width against grouping truth tables.
