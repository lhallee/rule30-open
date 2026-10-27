---
title: The center column is the image of 1 under a 2-adic isometry
category: frames
problems: [1]
status: paper
formalization: wanted
evidence: [computations/frames.py]
---

# The center column is the image of 1 under a 2-adic isometry

In the right-edge frame of [the seed's past](seed-past.md), Rule 30 is the bijection $\Phi(y) = y \oplus (2y \lor 4y)$
of the 2-adic integers. Collect the column under the frame's starting position into one number,

$$\Psi(y) = \sum_{t \ge 0} \bigl(\text{bit } t \text{ of } \Phi^t(y)\bigr)\, 2^t.$$

Then $\Psi$ is a bijective isometry of the 2-adic integers, $\Psi(1)$ is the single cell's center column, and Prize
Problem 1 says that $\Psi(1)$ is irrational, that is, its bits are not eventually periodic.

## Proof

- **Column.** Bit $t$ of $\Phi^t(y)$ is the cell at the frame's starting position at time $t$, so $\Psi(y)$ is that
  column of the row $y$.
- **Isometry.** $\Phi$ is a T-function: bits below $n$ of $\Phi(y)$ depend only on bits below $n$ of $y$. If $y$ and
  $y'$ first differ at bit $n$, then so do $\Phi^t(y)$ and $\Phi^t(y')$ for every $t$, because bit $n$ of the image is
  bit $n$ of the argument plus a function of lower bits. So $\Psi(y)$ and $\Psi(y')$ agree below $n$ and differ at bit
  $n$ (at $t = n$). An isometry of a compact space into itself is onto, so $\Psi$ is a bijection.
- **Shift.** $\Phi(2y) = 2\Phi(y)$, which gives $\Psi(2y) = 2\Psi(\Phi(y))$.

## Restatements

- Problem 1: $\Psi(1) \notin \mathbb{Q}$.
- For a finite row, a positive integer $a$ in this frame, $\Psi(a)$ is the column at the frame's position, which lies
  at or right of its rightmost black cell. So "no column of a finite row at or right of its rightmost black cell is
  eventually periodic" is "$\Psi$ maps no positive integer to a rational number".

## Checks

`psi` in [computations/frames.py](../../computations/frames.py) computes the first bits of $\Psi$;
`tests/test_computations.py` checks that $\Psi(1)$ is the center column and that $\Psi$ keeps the first differing bit
of 200 random pairs.

The frame turned up no handle on Problem 1: rational rows do not map to preperiodic orbits even when their column is
periodic ([the negative result](../../negative-results/frames/periodic-column-preperiodic-row.md)), and every
reformulation tried in it is listed in [the dynamics dead ends](../../negative-results/dynamics/reformulations.md).
