---
title: No two adjacent columns are eventually periodic
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.AdjacentColumns
headline: [adjacent_columns, no_constant_column, center_not_eventually_constant]
kit: independent
kit_modules: [Rule30Jen, Rule30Prize]
---

# No two adjacent columns are eventually periodic

In the orbit of any row with a leftmost 1, two neighboring columns are never both eventually periodic. This is Jen's
theorem in its adjacent form, and most exclusions in this repository end by reducing to it. A short consequence is
the period-1 case of Prize Problem 1: no column, the center included, is eventually constant.

## Statement

Take a row that is 1 at $m$ and 0 left of $m$, a column $k$, a time $T$ and a period $P > 0$.

- `adjacent_columns`: columns $k$ and $k + 1$ do not both satisfy $a_{t+P} = a_t$ for all $t \ge T$.
- `no_constant_column`: no column is constant from some time on.
- `center_not_eventually_constant`: there are no $T$ and $b$ with `Rule30Prize.center t = b` for all $t \ge T$.

## Argument

1. **Periodicity spreads left** (`periodic_left`). By left permutivity,
   $a_t(k-1) = a_{t+1}(k) \oplus \bigl(a_t(k) \lor a_t(k+1)\bigr)$. If columns $k$ and $k + 1$ repeat with period $P$
   from $T$, the right side does, so column $k - 1$ repeats too, from the same $T$. By induction, every column left of
   $k$ repeats with period $P$ from $T$.
2. **The left edge breaks it** (`adjacent_columns`). The leftmost 1 is at $m - t$ at time $t$. Pick a column $x$ left
   of $m - T$, far enough left and in the residue class mod $P$ that makes $m - x = T + qP$ for some $q \ge 1$. At time
   $T$ cell $x$ is 0, since it lies left of the leftmost 1. At time $T + qP$ the edge is exactly at $x$, so the cell is
   1. But step 1 makes column $x$ periodic from $T$, so it reads the same at $T$ and $T + qP$.
3. **A constant column has a constant neighbor** (`no_constant_column`). Suppose column $k$ is $b$ from $T$ on. If
   $b = 1$, every $a_t(k-1)$ is $\lnot a_{t+1}(k) = 0$, so column $k - 1$ is constant too. If $b = 0$, the update of
   cell $k + 1$ is $a_{t+1}(k+1) = 0 \oplus \bigl(a_{t}(k+1) \lor a_t(k+2)\bigr)$, so column $k + 1$ never falls from
   1 to 0: it is an OR latch, which switches on at most once and is then constant. Either way two adjacent columns are
   eventually constant, hence eventually periodic with period 1, against step 2.
4. The single cell is a row with its leftmost 1 at 0, and the center column is column 0. The official form follows
   through `evolve_single_center` ([Official.md](../Foundations/Official.md)).

## In Lean

`periodic_left` is step 1, proved for the pair $(k - n, k - n + 1)$ by induction on $n$. `periodic_iterate` carries
the value at $T$ to $T + qP$. `adjacent_columns` chooses $n$ by arithmetic modulo $P$. `single_not_constant` is the
single-cell form for every column.

## Relation to the kit

The kit proves Jen's theorem for the single cell (`Rule30Jen.not_adjacent`, in
[`Rule30Jen`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/7d665044b904117af9e82328aeb90a30692b2b85/lean/Ruliology/CellularAutomata/Rule30Jen.lean))
and that its center column is not eventually constant (`Rule30Prize.center_not_eventually_constant`). These proofs
are independent and hold in the orbit of every row with a leftmost 1, at every column. The theorem goes back to Jen;
Kopra (2023, Theorem 3.5) credits it to Jen (1990, Proposition 3), and the kit cites E. Jen, *Global properties of
cellular automata*, J. Stat. Phys. 43 (1986) 219 to 242.
