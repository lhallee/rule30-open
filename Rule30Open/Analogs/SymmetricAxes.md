---
title: Under Rules 90 and 150 a column is eventually periodic exactly at a mirror axis
category: analogs
problems: [1]
status: proved
lean: Rule30Open.Analogs.SymmetricAxes
headline: [iter90_column_periodic_iff, iter150_column_periodic_iff, linear_column_periodic_iff, at_most_one_periodic_column, run90_column_periodic_iff, run150_column_periodic_iff, run210_column_periodic_iff]
kit: refines
kit_modules: [Rule30Realization, Rule30Jen, Rule30DividedDifference]
---

# Under Rules 90 and 150 a column is eventually periodic exactly at a mirror axis

Rules 90 and 150 share with Rule 30 every property that Jen's argument uses, and the kit shows that their single-cell
center columns are eventually constant. This module says exactly where their eventually periodic columns come from:
for every finite row, the eventually periodic columns are the cells about which the row is mirror-symmetric. So the
kit's barrier has a single cause, the symmetry of the seed, and a nonzero finite row has at most one eventually
periodic column.

## Statement

Let $L_b$ be the rule $x'_i = x_{i-1} \oplus (b \land x_i) \oplus x_{i+1}$ over $\mathbb{F}_2$: Rule 90 for $b = 0$,
Rule 150 for $b = 1$. Let $y$ be a row that is 0 outside $[-N, N]$ and $p$ a cell.

- `iter90_column_periodic_iff`, `iter150_column_periodic_iff` (both from `linear_column_periodic_iff`): the column
  $t \mapsto (L_b^t y)(p)$ is eventually periodic if and only if $y(p + m) = y(p - m)$ for every $m$.
- `at_most_one_periodic_column`: if two different columns of $y$ are eventually periodic, then $y = 0$.
- `run90_column_periodic_iff`, `run150_column_periodic_iff`, `run210_column_periodic_iff`: from the single cell, the
  column $p$ of Rule 90, Rule 150 or Rule 210 (the kit's `run`) is eventually periodic if and only if $p = 0$.

"Eventually periodic" is the kit's `EventuallyPeriodic`: some $T$ and $P > 0$ with $u(t + P) = u(t)$ for $t \ge T$.

## Argument

1. **Linearity and symmetries** (`iterLin_xor`, `iterLin_shift`, `iterLin_mirror`). $L_b$ commutes with xor of rows,
   with translations and with the mirror $x \mapsto c - x$. Translating, take $p = 0$.
2. **If** (`symm_axis_column`). A row symmetric about 0 stays symmetric, so the two neighbors of the axis agree and the
   axis reads $u(t + 1) = b \land u(t)$: 0 from time 1 under Rule 90, constant under Rule 150.
3. **The skew part** (`symPart_xor_skewPart`, `skewPart_periodic`). Write $y = S \oplus A$, with $S$ the left half of
   $y$ mirrored onto the right, symmetric about 0, and $A(m) = y(m) \oplus y(-m)$ for $m \ge 1$, $A = 0$ elsewhere.
   The column of $S$ is eventually periodic by step 2, so by linearity the column of $y$ is eventually periodic if and
   only if the column of $A$ is, and $y$ is symmetric if and only if $A = 0$. It remains to show: a row $A$ on the
   cells $1, \dots, N$ whose column 0 is eventually periodic is 0.
4. **Two steps are one step on each sublattice** (`stepLin_twice`, `iterLin_double`). Over $\mathbb{F}_2$,
   $(z^{-1} + b + z)^2 = z^{-2} + b + z^2$, so $L_b^{2r}$ read at the cells $2x + i$ is $L_b^r$ of the sublattice
   $z \mapsto y(2z + i)$. Hence the even times of column 0 are the column 0 of the even sublattice $A(2z)$, and the odd
   times are the column 0 of $B(z) = (L_b A)(2z)$ (`periodic_even_times`, `periodic_odd_times`). Both are eventually
   periodic when the column of $A$ is.
5. **Descent on the width** (`skew_descent`). The even sublattice lives on $1, \dots, \lfloor N/2 \rfloor$; by
   induction it is 0. Then $B(z) = A(2z - 1) \oplus A(2z + 1)$, which is 0 for $z < 0$, so the skew part of $B$ is $B$
   on $z \ge 1$ and lives on $1, \dots, \lfloor (N + 1)/2 \rfloor$. By step 3 its column is eventually periodic, and
   for $N \ge 2$ it is narrower than $A$, so by induction $A(2z - 1) = A(2z + 1)$ for every $z \ge 1$. Every odd cell of
   $A$ then equals one beyond $N$, which is 0. For $N = 1$ the width does not drop: $A$ is the single cell at 1.
6. **The single cell next to the axis** (`single_one_even`, `single_one_odd`, `halving_not_periodic`,
   `single_one_not_periodic`). Its column $u$ has $u(2r) = 0$, since its even sublattice is empty, and
   $u(2r + 1) = u(r) \oplus c(r)$, since one step of it on the even sublattice is the pair of cells 0 and 1; here $c$
   is the axis column of the single cell at 0, which is $1, 0, 0, \dots$ under Rule 90 and $1, 1, 1, \dots$ under
   Rule 150. No such $u$ is eventually periodic, by descent on the period $P$:
   - $P = 2Q + 1$ odd: the even times, where $u$ is 0, go to the odd times, so $u(r + Q) \oplus c(r + Q) = 0$ for all
     large $r$, that is, $u$ agrees with $c$ from some time on. But under Rule 150 $u$ is 0 at the even times, where
     $c$ is 1, and under Rule 90 $u$ is 1 at the times $1, 3, 7, 15, \dots$, where $c$ is 0.
   - $P = 2Q$ even: $u(2r + 1 + 2Q) = u(2r + 1)$ gives $u(r + Q) = u(r)$ for large $r$, since $c$ is constant from
     time 1, so $u$ has the smaller period $Q$.
7. **At most one axis** (`two_axes_zero`, `at_most_one_periodic_column`). A row symmetric about $p < q$ satisfies
   $y(x) = y(x + 2(q - p))$, so a finite one is 0.
8. **The single cell** (`run90_eq`, `run150_eq`, `single_symm_iff`). The kit's `run g90` and `run g150` are $L_0$ and
   $L_1$ from the single cell, which is symmetric about $p$ only for $p = 0$. Rule 210 draws Rule 90's pattern from the
   single cell (the kit's `run210_eq`).

The explicit columns of step 6, which follow from its recursion by induction: under Rule 90, $u(t) = 1$ exactly when
$t + 1$ is a power of 2 (Lucas' theorem gives $u(t) = \binom{t}{(t-1)/2} \bmod 2$); under Rule 150, $u(t)$ is the
parity of the number of trailing 1s of $t$ in binary, $v_2(t + 1) \bmod 2$, a form of the period-doubling sequence.
The proof does not need these forms.

The counts agree with the controls of [the search for columns that repeat from time
0](../../negative-results/columns/periodic-from-start.md). Rows of at most 12 cells symmetric about a cell number
$\sum_{h=0}^{5} (12 - 2h)\, 2^h = 240$, each with one axis, and Rule 150 keeps 240 rows. Under Rule 90 the axis
column is $y(p), 0, 0, \dots$, which repeats from time 0 only when $y(p) = 0$, and those rows number
$\sum_{h=1}^{5} (12 - 2h)\, 2^{h-1} = 114$, the rows Rule 90 keeps. The theorem accounts for every column that is
eventually periodic; that no other column passed the search's finite test is an observation of that search.

## In Lean

`stepLin b` and `iterLin b` are the rule and its orbit, with `iter90_eq` and `iter150_eq` identifying them with Rule
90 (`iter90`, defined here) and the repository's `iter150` from [Rule150Descent](Rule150Descent.md), whose
`step150_twice` and `iter150_double` are the case $b = 1$ of `stepLin_twice` and `iterLin_double`. `symPart` and
`skewPart` are the two parts of step 3. `skew_descent` is steps 5 and 6, by induction on a bound for $N$, and
`halving_not_periodic` is the descent on the period, stated for any pair of sequences $u, c$ with the properties of
step 6. A finite row is one that is 0 outside $[-N, N]$, `∀ x, N < x.natAbs → y x = false`.

## Relation to the kit and the literature

The characterization, the "only if" direction through the symmetry of the row, and its proof by descent are not in the
kit. Two of its consequences also follow from Jen's argument, which needs only a rule that is permutive in its left
cell and a left edge that moves one cell per step, both true for Rules 90 and 150 from every nonzero finite row: at
most one column is eventually periodic (`at_most_one_periodic_column`; for Rule 30 the kit's
`Rule30Jen.between_periodic` and `Rule30FiniteConfigs.jen`, and Kopra (2023), Theorem 3.5, for a class that contains
Rule 90, in [the literature](../../literature/columns.md#traces)), and, with the kit's `barrier` and
`run_not_adjacent`, the single-cell corollaries. A Lean library of Palamarchuk (2026) claims the Rule 90 case at cell 1
([the literature](../../literature/columns.md)). Jen (1988) studies the temporal sequences of linear rules over finite
fields; its text was not read here, so novelty is claimed against the kit and this repository only. The kit's
[`Rule30Realization`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Realization.lean)
proves that the single cell's center column is eventually constant under Rules 90, 150 and 210 (`center90`,
`center150`, `center210`, `barrier`), and that Jen's adjacent-column theorem holds for them (`run_not_adjacent`);
`run90_column_periodic_iff`, `run150_column_periodic_iff` and `run210_column_periodic_iff` add that the center is their
only eventually periodic column. `EventuallyPeriodic` and `common_period` come from
[`Rule30Jen`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Jen.lean).
The "if" direction appears in the kit for one case: in
[`Rule30DividedDifference`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30DividedDifference.lean),
`add_reflect` and `add_center` show that under Rule 150 a row symmetric about cell 1 with cell 1 white keeps column 1
white. The "only if" direction and the characterization are not in the kit; its equivalent forms
(`CenterFormulas`) write Rule 30 as Rule 150 plus $x_p x_{p+1}$ with Rule 150's Green's function and say nothing about
which columns of Rule 150 are periodic.

For Rule 30 the theorem has no counterpart: Rule 30 is not mirror-symmetric (its mirror image is Rule 86), and step 4
fails, since the term $x \land x_{+1}$ does not cancel over two steps, as in [Rule150Descent](Rule150Descent.md).
