---
title: The kicked form of the left half
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.KickedForm
headline: [left_kicked_zero, left_kicked_succ, left_kicked_check, period_two_golden]
kit: refines
kit_modules: [Rule30MaskedJen, Rule30PeriodTwo]
---

# The kicked form of the left half

Whatever a column reads, the cells left of it evolve by one fixed map, Rule 30 beside a column held at 0, except that
the cell next to the column is flipped when the column reads 1 at two consecutive steps. So every eventual period of
a column becomes the same question about one map with periodic kicks, plus one parity check at each 1 of the period.
The identity holds in the orbit of every row.

## Statement

Write $c_t = a_t(k)$ for column $k$ and $u_j(t)$ for the cell $j + 1$ places left of it at time $t$. Let `held` be
Rule 30 left of a column held at 0: $\mathrm{held}(u)_0 = u_1 \oplus u_0$ and
$\mathrm{held}(u)_j = u_{j+1} \oplus (u_j \lor u_{j-1})$ for $j \ge 1$.

- `left_kicked_zero`: $u_0(t+1) = \mathrm{held}(u(t))_0 \oplus (c_t \land c_{t+1})$.
- `left_kicked_succ`: $u_j(t+1) = \mathrm{held}(u(t))_j$ for every $j \ge 1$.
- `left_kicked_check`: if $c_t = 1$, then $u_0(t) = \lnot c_{t+1}$.
- `period_two_golden`: if the column reads $0, 1, 0, 1$ at times $t, \dots, t + 3$ and $u_0(t) = 0$, then
  $u_0(t+2) = 1$.

## Argument

1. **The kick.** The real update of the cell next to the column is $u_0(t+1) = u_1 \oplus (u_0 \lor c_t)$, while
   `held` gives $u_1 \oplus u_0$. They differ exactly when $c_t = 1$ and $u_0 = 0$. When $c_t = 1$, the cell left of
   a 1 is the opposite of the column's next value, $u_0 = \lnot c_{t+1}$, so they differ exactly when
   $c_t = c_{t+1} = 1$. Cells further left never read the column, so they follow `held` exactly.
2. **The check** is the same fact read the other way: at a 1 of the column the cell next to it is determined by the
   column's next value.
3. **The cell right of the column adds checks at its 0s.** If $a_t(k+1) = 1$, the OR in its update is 1, so
   $a_{t+1}(k+1) = \lnot c_t$ (`right_latch`). If $c_t = 0$, the column's own update is
   $c_{t+1} = u_0(t) \oplus a_t(k+1)$, so the next value of the column shows the cell right of it (`right_shown`).
4. **The golden condition** (`period_two_golden`). With $c_t = 0$, $c_{t+1} = 1$ and $u_0(t) = 0$, step 3 gives
   $a_t(k+1) = 1$; the latch gives $a_{t+1}(k+1) = \lnot c_t = 1$ and then $a_{t+2}(k+1) = \lnot c_{t+1} = 0$. At
   time $t + 2$ the column reads 0 again, so $c_{t+3} = u_0(t+2) \oplus 0$, and $c_{t+3} = 1$ forces
   $u_0(t+2) = 1$. Beside an alternating column, the cell left of it never reads 0 at two consecutive 0s of the
   column.

For a column that repeats a block $w$, the left half follows `held` with a kick wherever $w$ has two consecutive 1s,
and it must pass the check at each 1 of $w$. For $w = 01$ there are no kicks at all, which is the reduction of
[HeldColumn.md](../PeriodTwo/HeldColumn.md).

## In Lean

`held` is defined in `Rule30Open.PeriodTwo.HeldColumn`. Each statement is a case analysis on four
cells after rewriting with the definition of `evolve`.

## Relation to the kit

For the single cell's center column the kit has the same identity as `Rule30MaskedJen.effective_step` in
[`Rule30MaskedJen`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30MaskedJen.lean):
the left half sees the center only through $c_t \land c_{t+1}$. The golden condition is the kit's
`Rule30PeriodTwo.golden`
([`Rule30PeriodTwo`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30PeriodTwo.lean)).
This module extends both to every column of every row.
