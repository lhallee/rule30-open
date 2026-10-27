---
title: No row with its leftmost 1 within 120 cells has an alternating center
category: period-two
problems: [1]
status: computed
formalization: wanted
---

# No row with its leftmost 1 within 120 cells has an alternating center

No row whose leftmost 1 lies within 120 cells left of the center has a center column that alternates from time 0,
whatever its right side holds, in either phase. The search behind this dies a roughly linear distance past the
support, as random constraints would, so more computation moves the bound without reaching every row.

## Method

With $c_t = t \bmod 2$, the center reads 1 at odd times, and there the OR in its update absorbs cell 1. Only cell 1 at
the even times matters; call those values the word $e$. The left half of row 0 is triangular in $e$: cell
$-(2s + 1)$ is $e_s$ plus a function of $e_0, \dots, e_{s-1}$. So a row whose leftmost 1 is at $-M$ fixes every
$e_s$ past $M$, and each further symbol must pass a consistency check.

A pruned search over $e$ builds the spacetime left of column 0 one diagonal $t + j$ at a time.

- With $e$ only constrained to have no two adjacent 1s (which the right side forces), it dies at $M = 70$ in both
  phases (by depth 102, with at most 24,157,817 branches alive), and agrees exactly with a time-indexed brute force
  where both run.
- With $e$ drawn from the exact words of 13 symbols that some right half produces, it dies at every $M$ from 70 to 120
  ($M = 120$ by depth 140, at most 9,480,685 branches). Those words are far fewer: 119 of the 377 golden-mean words at
  12 symbols, and $00000$ and $101001$ are the shortest that no right half produces.

A row with leftmost 1 at $-M$ and center $0101\dots$ gives one at $-(M + 1)$ with center $1010\dots$ a step later, so
both phases follow for every $M \le 120$.

## Evidence

The search ran in a C kernel that is not in this repository. The period-two question
for the left half alone, without the right side's constraint, is reproducible here:
[the left-half finding](left-half-alone.md).

## Bounds

This concerns a center that alternates from time 0. An eventually alternating center from a finite row reduces to the
same question at a later row, whose leftmost 1 has moved left, so the result excludes nothing for the single cell's
orbit by itself. Formalizing the search would need a certificate format the kernel can check in reasonable time.
