---
title: Deforming the rule to Rule 150 gives a polynomial of exponential degree
category: structure
problems: [3]
status: negative
kind: dead-end
evidence: [computations/deformation.py]
---

# Deforming the rule to Rule 150 gives a polynomial of exponential degree

**Question.** Rule 30 is $p \oplus (q \lor r) = p + q + r + qr$ over GF(2), with $p, q, r$ the left, center and right
cells. Deform it to $p + q + r + T\,qr$ over $\mathrm{GF}(2)[T]$. At $T = 0$ it is Rule 150, which is linear and whose
center column is computable fast; at $T = 1$ it is Rule 30. From the single black cell every cell is a polynomial in
$T$. If the center cell's degree in $T$ grew slowly, it could be recovered by interpolation in $T$ from few cheap
evaluations, which would be a shortcut for Problem 3. Interpolation in a deformation parameter is the device of the
refutation of the exponential time hypothesis by OpenAI (October 2026).

**What was done.** The deformed rule was run from the single cell with exact polynomial arithmetic to $t = 16$, and
checked against Rule 150 at $T = 0$ (every cell) and the Rule 30 center column at $T = 1$.

**Outcome.** The $T$-degree of the center cell at $t = 1$ to 16 is

0, 1, 0, 3, 6, 10, 16, 27, 44, 70, 114, 190, 313, 513, 839, 1368,

with 1, 2, 1, 3, 5, 6, 10, 15, 21, 38, 54, 102, 155, 252, 429 and 699 nonzero coefficients. The ratio of consecutive
degrees is 1.647, 1.639, 1.635 and 1.631 at $t = 13$ to 16. Heuristically, the $qr$ term adds the degrees of two
neighbors, which gives a Fibonacci-type recursion (growth near the golden ratio, 1.618) rather than $2^t$.

**Where it stops.** The degree grows like about $1.63^t$, so interpolation in $T$ needs exponentially many conditions in
$t$, and the deformation gives no shortcut. This is the step where the approach stops. Nothing else in the refutation
of the exponential time hypothesis transfers directly to a single deterministic trajectory; this was the one direct test
of its device. The growth is an observation to $t = 16$, not a proved bound.

**Reproduce.** `python -m computations.deformation 16` with
[computations/deformation.py](../../computations/deformation.py), in about a second.
