---
title: In every Rule 30 orbit three adjacent columns are at least 1/3 white, sharp at the fixed point (10)^infinity, and two adjacent columns at least 5/18 white; the sharp two-column constant lies in [5/18, 1/3] (1/3 attained by a period-12 orbit, computed)
category: foundations
problems: [2]
status: proved
lean: Rule30Open.Foundations.PairWhiteDensity
headline: [triple_white, alt_triple, pair_white, pair_step]
kit: new
kit_modules: [Rule30Jen]
evidence: [computations/strip_cycle_mean.py, tests/test_strip_cycle_mean.py, computations/row_white_density.py]
---

# In every Rule 30 orbit three adjacent columns are at least 1/3 white, sharp at the fixed point (10)^infinity, and two adjacent columns at least 5/18 white; the sharp two-column constant lies in [5/18, 1/3] (1/3 attained by a period-12 orbit, computed)

Let $x_0, x_1, \dots$ be any orbit of Rule 30, from any initial row, and fix adjacent columns.

**Theorem.**

1. *(Three columns, sharp.)* The columns $a, a + 1, a + 2$ have at least $n - 1$ white cells at the times
   $0, \dots, n - 1$ (`triple_white`). So their lower white density is at least $1/3$. The bound is attained: $(10)^\infty$
   is a fixed point (`alt_fixed`), and its columns $0, 1, 2$ read black, white, black at every time, exactly $n$ white
   cells in $3n$ (`alt_triple`).
2. *(Two columns.)* The columns $a, a + 1$ have $W$ white cells at the times $0, \dots, n - 1$ with $18 W \ge 10n - 18$
   (`pair_white`). So their lower white density is at least $5/18$.

Both are in Lean. The sharp constant for two columns is open: it lies between $5/18$ (part 2) and $1/3$ (computed).
No spatially periodic orbit of period at most 12 has two adjacent columns below $1/3$
(`row_white_density.periodic_strip_min`), and the minimizing cycle that the method below finds for $5/18$ does not
come from an orbit whose columns repeat with period 9 (`strip_cycle_mean.extends_right`).

*Relation to RowWhiteDensity and ColumnTransfer.* [RowWhiteDensity](RowWhiteDensity.md) proves with the same
telescoping in time that every strip of $J$ adjacent columns is at least $(2J - 2)/(5J)$ white (`strip_white`, $4/15$
at $J = 3$) and that two adjacent columns satisfy $W_a(n) + W_{a+1}(n) + W_{a+1}(n + 1) \ge n$ (its own `pair_white`,
in a different namespace, which gives white density at least $1/4$ for the pair). Part 1 improves $4/15$ to the sharp
$1/3$ and part 2 improves $1/4$ to $5/18$; RowWhiteDensity's bounds remain the general form for $J \ge 4$ and a
two-column count of a different shape. The triple potential $\varphi$ is new here, and the two-column potential $\psi$
comes from the cycle-mean graph below. The same fixed point, read as $(01)^\infty$, appears in RowWhiteDensity.
[ColumnTransfer](../Columns/ColumnTransfer.md) bounds black counts of a column by white counts of its neighbors; its
`transfer_right_white` rearranges to the same three-term count as RowWhiteDensity's `pair_white`, not to the
bounds here.

*Meaning.* A pair or triple of columns containing the center column has white density at least $5/18$ or $1/3$ in every
orbit, so in the single cell's orbit. The center column alone has no such bound from any argument valid for every
orbit, since $(10)^\infty$ has a column that is black at every time. Nothing here bounds black cells below.

## Proof

Both parts telescope in time on a fixed strip. The cells outside the strip, at every step, are free.

**Part 1.** Let $\varphi(q, r) = 0$ if $q = r = 0$ and $1$ otherwise. For all cells $p, q, r, s$,
$$\varphi\bigl(p \oplus (q \lor r),\ q \oplus (r \lor s)\bigr) + 1 \le \varphi(q, r) + [p = 0] + [q = 0] + [r = 0]$$
(`triple_step`, 16 cases). If $q$ or $r$ is white the right side is at least 2 and the left at most 2. If $q = r = 1$
the right side is $1 + [p = 0]$, and the next cells are $\neg p$ and $0$, so the left side is $2$ when $p = 0$ and $1$ when
$p = 1$. Apply it with $(p, q, r, s)$ the cells $a, \dots, a + 3$ at time $t$: the next cells $a + 1, a + 2$ are the two
arguments on the left. Summing over $t < n$ gives $n + \varphi_n \le \varphi_0 + W$, so $W \ge n - 1$
(`triple_aux`).

**Part 2.** The same with the five cells $a + 1, \dots, a + 5$ as the potential's argument, a table $\psi$ with values in
$[0, 18]$ (`tab`, `psi5`):
$$\psi(\text{next } a + 1, \dots, a + 5) + 10 \le \psi(\text{now}) + 18\,([x_a = 0] + [x_{a+1} = 0])$$
for every value of the cells $a, \dots, a + 6$ (`pair_step`, 128 cases by `decide`). Summing over $t < n$ gives
$10 n \le 18 + 18 W$.

**How the potentials are found.** The minimum cycle mean of the graph whose states are the strip and $k$ columns to its
right, and whose edges are the steps for every value of the two cells beside them, bounds the white density of the strip
in every orbit. Every orbit's columns follow a path of the graph, and the potential that Bellman-Ford gives at that mean
is a certificate as above. The cell left of the strip is truly free, by left permutivity. The cell right of it is
free in the graph but constrained in an orbit, so the mean only bounds the density from below.

| Strip | $k = 0$ | $1$ | $2$ | $3$ | $4$ | $5$ to $7$ | $8$ |
|---|---:|---:|---:|---:|---:|---:|---:|
| two columns | 1/4 | 1/4 | 1/4 | 1/4 | 5/18 | 5/18 | 5/18 |
| three columns | 1/3 | 1/3 | 1/3 | 1/3 | 1/3 | 1/3 | |

(`python -m computations.strip_cycle_mean`, about 10 s; the test checks the Lean table against the 128 cases and the
Bellman-Ford potential.) For three columns the bound is already sharp with $k = 0$. For two columns it stops at $5/18$
to $k = 8$, and its minimizing cycle at $k = 4$ (9 steps, 5 white cells in 18) does not extend to the right with
period 9. No window up to $k = 8$ closes the gap to $1/3$ (computed); this suggests (heuristic) that closing it needs
a model that constrains the right input.

## Reproduce

    lake build Rule30Open.Foundations.PairWhiteDensity
    python -m computations.strip_cycle_mean
    python -m pytest tests/test_strip_cycle_mean.py
