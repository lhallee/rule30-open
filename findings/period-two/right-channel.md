---
title: Beside an alternating center the right half nearly locks, and slips
category: period-two
problems: [1]
status: computed
formalization: not-applicable
evidence: [computations/right_half.py]
---

# Beside an alternating center the right half nearly locks, and slips

Drive the empty right half with a center that alternates. Column 1 settles almost into period 36, the blocks
$A = 1000100110$ and $B = 100110$ in the order $AAAB$, but it never locks: phase slips arrive at a steady rate, about
one per 145 steps, for as long as the run lasts. This is the right side of the period-two problem, and it is why the
finite game and every locking argument fail for the word $01$.

## Observation

Over 120,000 steps from the empty right half, in either phase:

- $AAAB$ occurs 2,114 times, first at about step 320.
- Column 1 differs from itself 36 steps earlier at 14.7% of the steps, in 826 separate slip events of about 21 cells
  each, one per about 145 steps.
- The slips start at odd times and are spread evenly over residues modulo $2^k$ ($k \le 6$) and modulo 36: no
  power-of-two clock is visible in them.

Counting the distinct column-1 words of the first $n$ steps over every right half of $n$ cells gives 86, 112, 144,
184, 231 and 287 words for $n = 20, 22, \dots, 30$: growth of about 1.12 per step, about 0.16 bit of entropy per
step. The right channel into the center is low in entropy but not finite. The left half under the same drive is the
opposite: sampled at the white times, its column $-1$ shows 4,095 of the 4,096 possible words of length 12, and at
lengths 20 and 28 nearly as many distinct words as the 60,000 samples allow.

## Why it matters

Under an eventual period the cells left of the center are a function of the center and of column 1 at its white times
([HeldColumn.md](../../Rule30Open/PeriodTwo/HeldColumn.md)). A locked column 1 would make the left half eventually
periodic, against Jen's theorem. The slips are the obstruction: column 1 keeps a positive rate of fresh information,
so the left half it reconstructs need not be periodic.

## Reproduce

`column_one("01", 0, 120000)` in [computations/right_half.py](../../computations/right_half.py) gives the column; the
word counts over all right halves came from code that is not in this repository.
