---
title: Information reaches the center from the left at speed 1, from the right at about 0.4
category: dynamics
problems: [1, 2]
status: computed
formalization: partial
evidence: [computations/sensitivity.py]
---

# Information reaches the center from the left at speed 1, from the right at about 0.4

Flip one cell of the single cell's initial row and watch the center column. A flip $d$ cells to the left changes it at
exactly $t = d$, the light cone's limit. A flip $d$ cells to the right arrives at a median of $2.51d$, and the flips at
$+1$ and $+2$ never arrive. Rule 30 is a one-way valve: the left reaches the center through the permutive XOR at every
step, the right only through the OR, and only where the middle cell is white.

## Result

- **From the left, exactly $d$.** In two rows that agree right of some cell, the rightmost difference moves right one
  cell per step and never cancels: the new cell right of it is the differing cell XOR the same OR. This is the
  left-permutivity of [Evolve.md](../../Rule30Open/Foundations/Evolve.md), and it gives arrival at $t = d$ for every
  $d$; the computation confirms it for $d \le 64$.
- **From the right, slower and irregular.** Over $d = 3, \dots, 1{,}024$ the arrival time is between $1.0d$ and $6.3d$
  (the extremes at small $d$: $d = 8$ arrives at $t = 8$, $d = 31$ at $t = 194$), with quartiles $2.37d$, $2.51d$ and
  $2.65d$; for $d \ge 64$ it is between $1.78d$ and $4.21d$. Arrivals come in plateaus, and the median puts the
  right-side influence front at about 0.4 cells per step.
- **Never from $+1$ or $+2$.** The seeds $11$ and $101$ have the single cell's center column, proved in Lean
  ([SeedExtensions.md](../../Rule30Open/Seeds/SeedExtensions.md)).

## The same asymmetry under a periodic center

Drive each half from empty with a center that repeats a word $w$ and count the distinct words in the column next to
the center, read at the white times of $w$ (lengths 12, 20 and 28, over 60,000 samples). Column 1 on the right has
few: 15, 32 and 65 for $w = 10$, and a constant 1 to 3 for $1110$, $1100$ and $1000$. Column $-1$ on the left has
about as many as the samples allow: 4,095, 29,491 and 29,971 for $w = 10$. Under an eventual period every left column
would be a sliding block code of the center and the right's column 1 at the white times, so the left half would have
to be as tame as the right channel. Turning that into a proof needs a lower bound on the complexity of a driven left
half, which is the same kind of statement as Problem 1 ([the dead end](../../negative-results/dynamics/left-half-complexity.md)).

## Reproduce

```bash
python -m computations.sensitivity 1024 8242
```

[computations/sensitivity.py](../../computations/sensitivity.py) prints both arrival times for each $d$. The word
counts came from code that is not in this repository.
