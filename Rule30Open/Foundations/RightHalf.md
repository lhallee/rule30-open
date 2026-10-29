---
title: Finite windows of a row
category: foundations
problems: [1]
status: proved
lean: Rule30Open.Foundations.RightHalf
headline: [driveStep_cells, drive_cells, mem_allLists]
kit: independent
kit_modules: [Rule30StripCertificates]
---

# Finite windows of a row

Several results here are finite checks: "whatever the rest of the row holds, these cells end up reading 0 1". This
module turns such a claim into a computation the Lean kernel can run, by evolving a finite window of cells next to a
column whose values are given.

## Statement

Let $c_t = a_t(x - 1)$ be the column just left of the window that starts at cell $x$.

- `driveStep_cells`: the $n$ cells $x, \dots, x + n - 1$ at time $t + 1$ are computed from $c_t$ and the $n + 1$ cells
  $x, \dots, x + n$ at time $t$ by `driveStep`.
- `drive_cells`: after $m$ steps, `drive` turns the $n + m$ cells $x, \dots, x + n + m - 1$ at time $t$ and the
  column values $c_t, \dots, c_{t+m-1}$ into the $n$ cells $x, \dots, x + n - 1$ at time $t + m$.
- `mem_allLists`: every list of $n$ cells occurs in `allLists n`, the enumeration of all $2^n$ of them.

## Argument

Cell $y$ at time $t + 1$ reads cells $y - 1$, $y$ and $y + 1$ at time $t$. Across the window $x, \dots, x + n - 1$,
these reads cover $x - 1, \dots, x + n$: the column value on the left, the window and one cell beyond it. So
`driveStep` walks the list from the left, computing each new cell from its left neighbor (the column value for the
first cell, the old value of the previous cell after that) and the two cells under and right of it, and it drops the
last cell, whose right neighbor is outside the list. Each step shortens the window by one cell, which is why $n + m$
cells give $n$ after $m$ steps. Induction on the list gives the first statement and induction on $m$ the second.

Together with `mem_allLists`, a statement about every row becomes a statement about every list of $n + m$ cells, which
the kernel can decide. [LongRuns.md](../Columns/LongRuns.md) uses this to check that nine 1s in a column force the two
cells right of it, over all $2^{11}$ windows.

## In Lean

`cellsFrom init t x n` lists the cells $x, \dots, x + n - 1$ at time $t$, and `columnFrom init y t m` lists column $y$
at times $t, \dots, t + m - 1$. The window statements compare these lists with `driveStep` and `drive`.

## Relation to the kit

The kit's
[`Rule30StripCertificates`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30StripCertificates.lean)
proves the same light-cone fact for strips of cells encoded as bit masks (`enc_step`), for its strip certificates. This
module proves it independently, on lists.
