---
title: The single cell has a unique past, and every row of it is periodic
category: frames
problems: [1]
status: paper
formalization: wanted
evidence: [computations/frames.py]
---

# The single cell has a unique past, and every row of it is periodic

Among rows that are white to the right of a frame moving right one cell per step, the single black cell has exactly
one predecessor $k$ steps back, for every $k$. Each predecessor is eventually periodic to the left, and its periodic
part, wrapped on a ring, dies under Rule 30 in exactly $k$ steps. So the periods must grow without bound. They are 1,
3, 6, 12, 24 and 48 from $k = 1, 2, 4, 10, 18$ and 66, and still 48 at $k = 3{,}000$.

## The frame

Read a row leftward from the frame: bit $j$ of the 2-adic integer $y$ is the cell $j$ places left of it. One step of
the rule, with the frame moved one cell right, is

$$\Phi(y) = y \oplus (2y \lor 4y),$$

since the new cell $j$ reads the old cells $j$, $j - 1$ and $j - 2$. Bit $j$ of $\Phi(y)$ is $y_j$ plus a function of
lower bits, so $\Phi$ is a bijection of the 2-adic integers, and the single cell is $y = 1$. Its center column is bit
$t$ of $\Phi^t(1)$. Define $\rho_k = \Phi^{-k}(1)$, the unique row that becomes the single cell after $k$ steps.

## Proof of the general facts

1. **Each $\rho_k$ is rational.** Inverting $\Phi$ bit by bit, $z_j = y_j \oplus (z_{j-1} \lor z_{j-2})$, is a
   transducer with four states. Fed an eventually periodic input, it returns to a state at the start of a period
   within four periods, so its output is eventually periodic. By induction from $\rho_0 = 1$ every $\rho_k$ is.
2. **The tail dies in exactly $k$ steps.** Far from the frame, $\Phi$ acts on the periodic tail of a row as Rule 30
   (with a rotation) on a ring of the period's length. The tail of $\Phi^m(\rho_k) = \rho_{k-m}$ is nonzero for
   $m < k$, since a positive integer cannot map to 1 (each step adds two bits above the top one), and $\rho_1 = -1$,
   the black half-line, whose tail is all black. So the ring passes through all black at step $k - 1$ and is white at
   step $k$, and not before.
3. **The periods are unbounded.** The period of $\rho_k$ divides that of $\rho_{k+1}$, since $\Phi$ maps a $p$-periodic
   tail to a $p$-periodic tail. A ring of $p$ cells has $2^p$ states, so no configuration on it dies after more than
   $2^p$ steps; the period of $\rho_k$ therefore exceeds $\log_2 k$.

## Computation

[computations/frames.py](../../computations/frames.py) carries each $\rho_k$ exactly as a prefix and a period word,
and checks for every $k \le 3{,}000$ that $\Phi^k(\rho_k) = 1$ and that the period word dies on a ring in exactly $k$
steps (16 s):

| $k$ | Preperiod | Period |
|---:|---:|---:|
| 1 to 28 | 0 or 1 | 1, 3, 6, 12, 24 (from $k$ = 1, 2, 4, 10, 18) |
| 30 | 4 | 24 |
| 66 | 188 | 48 |
| 300 | 1,509 | 48 |
| 1,000 | 4,968 | 48 |
| 3,000 | 15,615 | 48 |

Examples: $\rho_1 = -1$, $\rho_2 = (100)^\infty = -1/7$, $\rho_{10} = (100100010010)^\infty$. The word
$100010011101010111000110$ of $\rho_{28}$, repeated leftward from a cut with white cells right of it, becomes exactly
one black cell after 28 steps. A corollary: Rule 30 on a ring of 48 cells has configurations that die in exactly $k$
steps for every $k$ from 66 to 3,000.

## What it does not say

The past exists whatever the center column does later, so it gives no constraint toward Problem 1 by itself; it is a
structural fact about the frame in which the problems are phrased.
