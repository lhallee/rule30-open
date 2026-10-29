---
title: The cells left of a column count down its runs of 1s
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.RunCountdown
headline: [run_countdown, run_bound, no_ones_column, center_not_eventually_ones]
kit: refines
kit_modules: [Rule30CenterRuns]
---

# The cells left of a column count down its runs of 1s

When a column is about to read 1 for exactly $b + 1$ steps, the cells left of it already know: they read
$0\,1\,0\,1\,\dots$ outward from the column on exactly their $b$ nearest cells. The identity holds in the orbit of
every row, at every column. With a leftmost 1 it bounds every run of 1s by the column's distance to the left edge, and
it shows that no column reads 1 forever without going through Jen's theorem.

## Statement

Write $u_j$ for the cell $j + 1$ places left of column $k$, and let $B$ be the half $0\,1\,0\,1\,\dots$, that is
$B_j = 1$ exactly when $j$ is odd.

- `run_countdown`: if column $k$ reads 1 at times $s, \dots, s + b$ and 0 at $s + b + 1$, then at time $s$ the half
  $u$ agrees with $B$ at $j < b$ and differs at $j = b$.
- `run_bound`: in the orbit of a row whose leftmost 1 is at $m$, let $d = k - (m - s)$ be the distance from the
  column to the leftmost 1 at time $s$. A run of odd length $b + 1$ starting at $s$ has $b + 1 \le d$, and one of even
  length has $b + 1 \le d + 2$.
- `no_ones_column`: in the orbit of a row with a leftmost 1, no column reads 1 from some time on.
- `center_not_eventually_ones`: `Rule30Prize.center` is not 1 from some time on.

## Argument

1. **Beside a 1, the half follows a fixed map.** While column $k$ reads 1, the OR in the update of the cell next to it
   is 1, so the half evolves by `heldOne`, Rule 30 with the column held at 1:
   $u'_0 = \lnot u_1$ and $u'_j = u_{j+1} \oplus (u_j \lor u_{j-1})$ for $j \ge 1$ (`left_heldOne`).
2. **$B$ is a fixed point of that map.** $\lnot B_1 = 0 = B_0$, and for $j \ge 1$ one of $B_j, B_{j-1}$ is 1, so
   $B_{j+1} \oplus 1 = B_j$ (`heldOne_domainB`).
3. **Stepping back adds one cell of agreement.** Suppose $u_0 = 0$ and the image $u'$ agrees with $B$ below $n$. Then
   $u_1 = \lnot u'_0 = 1 = B_1$, and for $j \ge 1$, once $u_j$ and $u_{j-1}$ agree with $B$ the OR is 1, so
   $u_{j+1} = \lnot u'_j = \lnot B_j = B_{j+1}$. So $u$ agrees with $B$ below $n + 1$ (`heldOne_agree_back`), and the
   same computation shows that a difference at $n$ in $u'$ is a difference at $n + 1$ in $u$ (`heldOne_differ_back`).
4. **The countdown** (`run_countdown`), by induction on $b$. At the last 1, time $s + b$, left of a 1 the cell is the
   opposite of the column's next value, here $\lnot 0 = 1$: so $u_0 = 1 \ne B_0$, the case $b = 0$. For $b \ge 1$, at
   time $s$ the column reads 1 now and next, so $u_0 = 0$; the half at $s + 1$ is the image of the half at $s$ under
   step 1, and by induction it agrees with $B$ below $b - 1$ and differs at $b - 1$. Step 3 moves both facts one cell
   out.
5. **The bound** (`run_bound`). No cell left of the leftmost 1 is black. For even $b$, $B_b = 0$, so the difference at
   $b$ is a black cell $b + 1$ places left of the column; for odd $b \ge 3$, $B_{b-2} = 1$ is a black cell $b - 1$
   places left. Either cell lies at or right of $m - s$.
6. **No column of 1s** (`no_ones_column`). If column $k$ reads 1 from $T$ on, step 3 applies at every step, and
   induction on $n$ shows that the half at every time $t \ge T$ agrees with $B$ below $n$, for every $n$. Then the
   half at $T$ is $B$ itself, black at every odd distance from the column, but it is white left of the leftmost 1.

## In Lean

`heldOne` is the map of step 1, and `domainB` is $B$, defined in `Rule30Open.PeriodTwo.Domains`.
`run_countdown_spot` checks the statement on the single cell: its center reads 1 at times 3, 4, 5 and 0 at 6, and at
time 3 the cells left of it read $0\,1$ and then not 0. `single_no_ones` is the single-cell form.

## Relation to the kit

The kit's
[`Rule30CenterRuns`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30CenterRuns.lean)
bounds a black run of the single cell's center column that starts at time $a$ by $a$. For the center of the single
cell, $d = s$, so `run_bound` gives the same bound for runs of odd length and one 2 weaker for runs of even length;
what it adds is the exact countdown and its validity at every column of every row.
