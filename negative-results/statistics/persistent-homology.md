---
title: Persistent homology does not tell the single cell's center from random rows
category: statistics
problems: [1, 2]
status: negative
kind: no-signal
evidence: [computations/persistence.py]
---

# Persistent homology does not tell the single cell's center from random rows

**Question.** Does the space-time diagram of the single black cell, near its center column, have a shape that the
diagram of a uniformly random row does not? The uniform measure is invariant under Rule 30, so random rows give the
stationary diagram; a difference in shape near the center would be structure that a proof of Problem 1 or 2 could
look for. Persistent homology measures shape at every scale at once, and it is blind to the bit-level statistics
that [the randomness tests](randomness-tests.md) already cover.

**Method.** A window is 32 steps by 32 cells (or 64 by 64). The black cells of a window, and separately its white
cells, form a point cloud in the plane, and `ripser` computes the Vietoris-Rips persistence of each cloud in
dimensions 0 and 1, up to scale 6. Grid distances are $1, \sqrt 2, 2, \sqrt 5, \dots$, so the bars read as shapes:
the H0 bars that outlive 1 and $\sqrt 2$ count the 4- and 8-connected clusters, the H1 bars born at 1 give the cycle
rank of the 4-neighbor graph, and the H1 bars that live past 2 are holes larger than one cell (for the black cells,
the white triangles); each window gives six numbers per color, twelve in all, among them the count, the total
persistence and the largest death of those holes. The test checks the H0 and H1 counts against connected components
and cycle ranks counted directly. Samples: 400 windows of the single cell's diagram on cells $-16$ to $15$, stacked
without overlap from step 1,000 (to step 13,800), and 400 windows of rows 64 to 95 of independent uniform random rows.
Two-sample statistics: the energy distance between the standardized 12-dimensional feature vectors with a
permutation p-value (200 permutations), the cross-validated AUC of a logistic regression with a permutation p-value
(100), and a Mann-Whitney test per feature, Bonferroni over the 12.

**Outcome.** Nothing separates the center from random rows.

| Comparison (400 against 400 windows of 32 by 32) | Energy distance | p | Classifier AUC | p |
|---|---:|---:|---:|---:|
| Center, steps 1,000 to 13,800, against random rows | 0.034 | 0.045 | 0.530 | 0.13 |
| Center, from step 20,000, against fresh random rows | 0.017 | 0.67 | 0.473 | |
| Center, from step 40,000, against fresh random rows | 0.015 | 0.84 | 0.484 | |
| Center, from step 60,000, against fresh random rows | 0.014 | 0.92 | 0.490 | |
| Random rows against random rows (null control) | 0.019 | 0.60 | 0.471 | 0.86 |
| Random rows with 0.2% of cells flipped (power) | 0.44 | 0.005 | 0.809 | 0.01 |
| Random rows with 1% of cells flipped (power) | 1.76 | 0.005 | 0.995 | 0.01 |
| Single cell, 17 to 48 cells inside the right edge | 0.057 | 0.005 | 0.616 | 0.01 |
| Single cell, inside the left edge | 4.92 | 0.005 | 1.000 | 0.01 |
| Fair coin flips, cell by cell | 7.29 | 0.005 | 1.000 | 0.01 |

The p-value 0.005 is the least that 200 permutations give, 0.01 the least of 100. The first row is the only one of the
four center samples below 0.05, and the least of four p-values is at most 0.045 with chance about 0.17 when nothing
differs; the three replicates, at later steps and with fresh random rows, give 0.67, 0.84 and 0.92. No single feature
differs after the Bonferroni correction in any of the four (the smallest corrected p-value is 0.41, the 8-connected
white clusters of the first sample). At 64 by 64, 200 windows each, the center against random rows gives energy
distance 0.045 (p 0.43) and AUC 0.505, the null control 0.029 (p 0.88) and AUC 0.439.

The controls show what the test sees. Flipping one cell in 500 is enough for an AUC of 0.81: in Rule 30 the cell below
the right one of two adjacent black cells is white, so black cells never form a 2 by 2 square, and in every Rule 30
window here they have cycle rank 0 in the 4-neighbor graph, while a flipped cell makes cycles. Inside its left edge the
single cell's diagram is periodic: all 400 windows there are the same window. The right edge is seen at 17 to 48 cells
inside it, mostly through the 8-connected white clusters (16.65 against 15.76 per window), and not at 33 to 96 cells
inside it at 64 by 64 (energy p 0.68, AUC 0.464).

**What it means.** At the scales of 32 and 64 cells and over steps 1,000 to 72,800, the shapes in the diagram near the
center, its clusters, cycles and holes and how long they persist, have the same law as in the stationary diagram of a
random row, to the precision of 400 windows; the test would have seen a local constraint broken at one cell in 500,
and the approach to the right edge. So persistent homology finds no structure near the center for a proof to use; the
one shape fact it shows, black cells without a 2 by 2 square, holds for every row and is one step of the rule. Like
[the randomness tests](randomness-tests.md), this is evidence consistent with Problem 2, not a step toward it.

**Reproduce.**

```bash
pip install ripser
python -m computations.persistence --count 400 --size 32           # first row and the controls, about 30 minutes
python -m computations.persistence --count 400 --size 32 --start 20000 --rows-seed 7 --no-controls
python -m computations.persistence --count 400 --size 32 --start 40000 --rows-seed 8 --no-controls
python -m computations.persistence --count 400 --size 32 --start 60000 --rows-seed 9 --no-controls
python -m computations.persistence --count 200 --size 64           # 64 by 64, about 40 minutes
```

Times are for a loaded machine with four cores.
