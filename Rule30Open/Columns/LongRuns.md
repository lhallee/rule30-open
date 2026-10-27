---
title: Runs of nine 1s rule out a periodic column
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.LongRuns
headline: [wall_check, long_runs_column, center_long_runs]
kit: independent
kit_modules: [Rule30BlackRuns]
---

# Runs of nine 1s rule out a periodic column

Nine 1s in a row in a column force the two cells to its right, whatever the rest of the row holds. That one finite
fact excludes every eventually periodic column whose runs of 1s all last at least nine steps, in the orbit of every
row with a leftmost 1. For the center column it excludes infinitely many repeating blocks, among them $01^k$ for every
$k \ge 9$.

## Statement

- `wall_check`: for every window of 11 cells right of a column, nine steps with the column reading 1 leave the first
  two cells reading 0 1.
- `wall_forms`: if column $k$ reads 1 at times $s, \dots, s + 8$, then $a_{s+9}(k+1) = 0$ and $a_{s+9}(k+2) = 1$.
- `long_runs_column`: in the orbit of a row with a leftmost 1, no column is periodic from some time $T$ with every
  run of 1s that ends after $T$ lasting at least nine steps.
- `center_long_runs`: the same for `Rule30Prize.center`.

## Argument

1. **The wall** (`wall_check`, `wall_forms`). Cells $k + 1$ and $k + 2$ at time $s + 9$ depend only on column $k$
   at times $s, \dots, s + 8$ and on the 11 cells $k + 1, \dots, k + 11$ at time $s$
   ([RightHalf.md](../Foundations/RightHalf.md)). The kernel runs all $2^{11}$ windows and finds 0 1 every time.
2. **A latch behind each run** (`latch_after_runs`). Let $t$ be a time where column $k$ reads 0. If the column read 1
   at $t - 1$, a run of at least nine 1s just ended, and step 1 gives $a_t(k+1) = 0$ and $a_t(k+2) = 1$. At the next
   step of the run of 0s, cell $k + 1$ updates to $0 \oplus (0 \lor 1) = 1$, and while column $k$ stays 0 the update
   $0 \oplus (a(k+1) \lor a(k+2))$ keeps it at 1. So at every 0 of column $k$, $a_t(k+1) = \lnot a_{t-1}(k)$: a
   function of column $k$.
3. **The left column follows** (`long_runs_column`). By left permutivity,
   $a_t(k-1) = a_{t+1}(k) \oplus \bigl(a_t(k) \lor a_t(k+1)\bigr)$. At a 1 of column $k$ the OR is 1; at a 0 it is
   $a_t(k+1)$, which step 2 gives. So column $k - 1$ is a function of column $k$ at times $t - 1$, $t$ and $t + 1$,
   and repeats with the same period. Columns $k - 1$ and $k$ are both eventually periodic, which
   [the adjacent-column theorem](AdjacentColumns.md) rules out.

Two edge cases close the proof. If the column has no 1 after $T$, it is eventually constant, which
`no_constant_column` excludes; otherwise periodicity supplies 1s at arbitrarily late times, and step 2 can start right
after one. Taking $T \ge 9$ keeps the nine steps before each 0 at nonnegative times.

## In Lean

`wall_check` is `decide +kernel` over `allLists 11`, so the kernel itself evaluates the 2,048 cases. `wall_forms`
transfers it to real rows with `drive_cells`. `single_long_runs` is the single-cell form for every column.

## Relation to the kit

The kit's
[`Rule30BlackRuns`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/7d665044b904117af9e82328aeb90a30692b2b85/lean/Ruliology/CellularAutomata/Rule30BlackRuns.lean)
proves the same nine-black shield for the single cell's center column, with consequences such as
`not_eventually_zero_ones` ($01^k$, $k \ge 9$) and `no_white_run_11`. This proof is independent and covers every
column of every row with a leftmost 1.
