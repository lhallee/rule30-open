---
title: For 001 the left half only has to fail for free bits whose runs of 0s have length at least 2 and runs of 1s at least 3
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ConstrainedLeft001
headline: [not_eventually_001_of_C3r, center_not_eventually_001_of_C3r, c3r_of_c3s]
kit: refines
kit_modules: [Rule30EtherThreeSkeleton, Rule30EtherThreeLeft, Rule30DrivenLeft]
evidence: [computations/constrained_left.py]
---

# For 001 the left half only has to fail for free bits whose runs of 0s have length at least 2 and runs of 1s at least 3

The kit reduces a center column that repeats $001$ to an open statement about the left half alone,
`Rule30EtherThree.C3s001`. This module proves that a weaker statement, `C3r001`, suffices: the left half has to fail
only for free bits that the right half can produce, and by [ThreeRuns](ThreeRuns.md) those have runs of 0s of length
at least 2 and runs of 1s of length at least 3. `C3r001` is open.

## Statement

Let $L_k(p)$ be cell $p < 0$ at time $k$ of a left half $s$ run as Rule 30 with column 0 held white (the kit's
`L (fun _ => false) s`). Column $-1$ *keeps the pattern* $(0, *, 1)$ from time $K$ if for every $k \ge K$ it is white
when $k \equiv 0$ and black when $k \equiv 2 \pmod 3$ (the kit's `fits3 colPattern001s`). Its *free bits* are
$f_i = L_{3i+1}(-1)$.

- `C3r001`: no finitely supported $s$ keeps the pattern from some time on with the complements $\lnot f_i$ free of
  $010$, $101$ and $1001$ from some index on (the kit's form of the words is `ThreeRuns.NoShortRuns`). Equivalently, the
  free bits have no run of 0s of length 1 and no run of 1s of length 1 or 2 from some index on.
- `c3r_of_c3s`: $\texttt{C3s001} \Rightarrow \texttt{C3r001}$.
- `not_eventually_001_of_C3r`: if `C3r001` holds, no time $T$ has `cell t 0 = wordAt3 w001 (t - T)` for all $t \ge T$.
- `center_not_eventually_001_of_C3r`: the same with `Rule30Prize.center`.

## Argument

1. **The left half** (the kit's `cell_eq_L_effective`). From time $T$ on, the cells left of the center are the left
   half run from the row at time $T$ beside the effective boundary $c(T + k) \land c(T + k + 1)$, which is white when
   the center repeats $001$ from $T$. The row at time $T$ has a leftmost black cell, so the half is finitely supported.
2. **The pattern** (the kit's `col_m1_001_skeleton`). Column $-1$ is eventually white at phase 0 and black at phase 2,
   and at phase 1 it is the complement of column 1 (`col_m1_001`).
3. **The free bits** (`ThreeRuns.three_runs_evolve`). For every row whose center repeats $001$ from $T$, column 1 at
   the times $T + 3i + 1$ avoids $010$, $101$ and $1001$ from $i = 14$ on. By step 2 these values are the complements
   of the free bits $f_i$.
4. So the half of step 1 keeps the pattern from $T' - T$ and has constrained free bits from index 14, which `C3r001`
   forbids. The official form follows from `evolve_single_eq_cell` and `evolve_single_center`.

## What the constraint buys

Without the constraint, the free bits of a half that keeps the pattern are arbitrary: the halves of at most $M$ cells
that keep it through step $M - 1$ are $2^{M/3}$ per phase, one for each word of free bits. With it they are as many as
the words with the run lengths above, about $2^{0.2042 M}$: the entropy of those words is $\log_2 \lambda = 0.6126$ bits
per free bit, for $1/\lambda$ the root in $(0, 1)$ of $x^5 = (1 - x)^2$. [The constrained left
halves](../../negative-results/columns/constrained-left-halves.md) runs the search with and without the constraint;
the constraint does not change the kind of the statement, which still asks that a finite half avoid a set of
sequences of positive entropy.

## Relation to the kit

The kit's `C3s001` and `not_eventually_001_of_C3s` are the unconstrained statement and its reduction; the proof here
follows `not_eventually_001_of_C3s` and adds step 3. The kit's `Q001` asks less of the pattern (column $-1$ black at
phase 2 only), and notes that `C3s001` is weaker than the eventual form of `Q001`; so the eventual form of `Q001`
implies `C3s001`, which implies `C3r001`.
