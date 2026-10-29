---
title: Randomness proves Problems 1 and 2 for almost every row and stops at the single cell
category: random-rows
problems: [1, 2, 3]
status: negative
kind: barrier
---

# Randomness proves Problems 1 and 2 for almost every row and stops at the single cell

**Question.** Can a probabilistic argument settle a prize problem: a counterexample that a random model produces, or a
statement about random rows tightened until it covers the single cell?

**What randomness proves.** [LeftWindow.md](../../Rule30Open/RandomRows/LeftWindow.md) proves in Lean, for every
row, the single cell's included:

- with the $n$ cells left of the center replaced by a uniformly random word, the center cells at times $1, \dots, n$
  are $n$ independent fair coins (every center word comes from exactly one left word);
- with only the cells at a set $S$ of depths free, a condition that fixes the center at a time in $S$ by the column
  before it holds for exactly half of the rows, whatever the other conditions ask; so a center column that repeats
  with period $p$ from time $T$ up to time $M$ comes from at most a fraction $2^{-|S \cap [T + p, M]|}$ of the rows.

Three consequences follow by standard arguments:

- **Problem 1 for random rows.** If the cells at an infinite set of depths are independent fair coins and the other
  cells are fixed, the center column is eventually periodic with probability 0, however sparse the set: for each of
  the countably many pairs $(T, p)$ the fraction above tends to 0 as $M$ grows.
- **Problem 2 for random rows.** If the free depths have density 1, the center column has density 1/2 with
  probability 1. At a free depth the center is a fair coin given the column before it, so the sums of
  $c(s) - \tfrac12$ over free depths form a martingale with bounded increments, which is $o(n)$ almost surely, and the
  other depths have density 0.
- **Problem 3 for a row given as input.** The center cell at time $t$ has degree $2t - 1$ over GF(2) as a function of
  the $2t + 1$ cells of its cone ([the degree finding](../../findings/structure/center-degree.md)), and a decision tree
  of depth $d$ computes a polynomial of degree at most $d$. So an algorithm that reads the row to find the cell reads
  at least $2t - 1$ cells on some row, and on every row it reads cell $-t$, whose flip flips the cell.

So none of these models yields a counterexample: the events a counterexample needs have probability 0.

**Where it stops.**

1. **The single cell is one row.** It is the row whose left half is white, and a statement about almost every row says
   nothing about one row. The rows such statements leave out are not exotic. The white row has a constant center, and
   rows on the stripe and the ether backgrounds have eventually periodic columns
   ([periodic backgrounds](../../findings/frames/periodic-backgrounds.md)). The kit's
   `Rule30Realization.column_realizable_unique` gives, for every right half, the single cell's among them, exactly
   one row with any prescribed center column; and its `seed_perturbation` gives, for every $n$, a row equal to the
   single cell from cell $-n$ rightward whose center is constant from time $n$. The rows with an eventually periodic
   center accumulate at the single cell, so no argument that treats it as a typical point of a measure or of a
   neighborhood can separate it from them.
2. **No amount of randomness interpolates.** With infinitely many free cells the statements hold almost surely,
   however sparse the free set, and they say nothing about any given row. With finitely many, "every row of the family"
   includes the single cell, the row with every free cell white, so the statement is at least as hard as Problem 1;
   and "most rows of the family" says nothing about it. No amount of randomness in between, constant, logarithmic or
   linear in the time, turns a probability bound into a statement about one row.
3. **The same gap one level down.** In the period-four lead, a fair coin beyond a window of 16 columns locks every
   window almost surely, but Rule 30's own right half is not coin-like there: 2.6% to 7.1% of random starts stay out
   of the window's certificate for 12,000 steps by building ether plugs, which happens to a window with a coin beyond it with
   chance below $10^{-5}$ ([the coin-lock finding](../../findings/columns/coin-lock.md)).

**What it means.** As Borel's theorem that almost every real number is normal decides nothing about $\sqrt{2}$, these
results secure the prize statements for typical rows and leave the single cell where it was. A proof has to use a
property that the single cell has and that the rows accumulating at it lack: its left edge, as in Jen's theorem
([AdjacentColumns.md](../../Rule30Open/Columns/AdjacentColumns.md)), or a structure such as the ether family on the
right. The finite counts are proved in Lean; the limits and the decision-tree bound are the standard arguments written
out above. For the related route through hypotheses about satisfiability, see
[the complexity entry](../complexity/hardness-hypotheses.md).
