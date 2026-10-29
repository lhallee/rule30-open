---
title: No other right extension up to 40 cells keeps the center column
category: seeds
problems: [1, 2, 3]
status: computed
formalization: partial
---

# No other right extension up to 40 cells keeps the center column

Append any $\ell \le 40$ cells right of the single black cell. Exactly two of the resulting seeds of each length keep
the center column for all time, $(10)^k1$ and $(10)^k11$, the families
[proved in Lean](../../Rule30Open/Seeds/SeedExtensions.md). Every other one of the $2^{40} - 1$ extensions changes the
column within 685 steps.

## Method

The center cell at time $t$ reads only cells $-t, \dots, t$. So if the seed $1\,x_1 \dots x_j$ changes the column at
some $t \le j$, every longer extension of it changes the column at the same $t$, and the whole subtree can be dropped.
A prefix ending in 0s is the same row as the shorter prefix, so its first difference decides its whole run of 0s. A
depth-first search with this prune covers all $2^{40} - 1$ extensions in 83.5 billion prefixes (735 s on 24 threads,
in C), and agrees with brute force over every extension up to 10 cells.

Forty extensions match the column for 4,096 steps, one family member per length. Each was then decided for all $t$
from windows at the right edge: in the frame moving right one cell per step, a window of the row's right end evolves on
its own by a bijection, so it is periodic from $t = 0$, and the two rows' windows show that the difference never
reaches the center. Every other extension differs by $t = 685$; the latest first differences come at 37 to 40 cells,
after 153 at 14 cells and 413 at 20.

## Evidence

The search ran in a C kernel that is not in this repository. The families' invariance
is the Lean module above, and [tests/test_computations.py](../../tests/test_computations.py) checks both families and
their difference sets by direct evolution for $k \le 5$.

## What it means

The map from finite rows to center columns identifies the single cell with an infinite but thin family of other rows,
all sharing its left edge. The kit's equivalent forms prove the two families in Lean as its stripe seeds and report
the same count numerically for seeds within 13 cells and 300 steps
([`TransformsSeeds`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/equivalents/Rule30Equivalents/TransformsSeeds.lean)). A port of the pruned search to this repository, and its extension past
40 cells, would be a welcome contribution.
