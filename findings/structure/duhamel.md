---
title: The center column as a sum over adjacent black pairs
category: structure
problems: [1, 2, 3]
status: paper
formalization: wanted
evidence: [computations/algebra.py]
---

# The center column as a sum over adjacent black pairs

Over GF(2), Rule 30 is Rule 150 plus one product: $x' = (p + q + r) + qr$. Unrolling the linear part gives an exact
formula for the center column in which every nonlinear event, a pair of adjacent black cells, contributes through the
Rule 150 kernel:

$$c(t) = 1 + \sum_{s=0}^{t-1} \sum_{y} T_{t-1-s}(y)\, a_s(y)\, a_s(y+1) \pmod 2,$$

where $a_s$ is the single cell's row at time $s$ and $T_n(y)$ is the coefficient of $X^y$ in $(X^{-1} + 1 + X)^n$, taken
mod 2.

## Proof

Let $L$ be Rule 150 on rows, $(La)(x) = a(x-1) + a(x) + a(x+1)$, and $g_s(y) = a_s(y)a_s(y+1)$. Rule 30 reads
$a_{s+1} = La_s + g_s$, so by induction $a_t = L^t a_0 + \sum_{s<t} L^{t-1-s} g_s$. The operator $L^n$ is convolution
with $T_n$, which is symmetric, so the center cell is $T_t(0) + \sum_{s<t} \sum_y T_{t-1-s}(y) g_s(y)$. The central
trinomial coefficient $T_t(0)$ is odd for every $t$: mod 2, $(1 + X + X^2)^{2m} = (1 + X^2 + X^4)^m$ and
$(1 + X + X^2)^{2m+1} = (1 + X^2 + X^4)^m(1 + X + X^2)$, so $T_{2m}(0) \equiv T_{2m+1}(0) \equiv T_m(0)$, and
$T_0(0) = 1$. That is also why Rule 150 from a single cell has an all-black center column.

## Computation

`duhamel_center` in [computations/algebra.py](../../computations/algebra.py) evaluates the right side and matches the
center column for $t < 128$; `tests/test_computations.py` checks $t < 96$.

## Use

The formula separates what is linear in Rule 30 from the nonlinear events. The kernel $T_n$ mod 2 is a 2-automatic
pattern (Sierpinski-like), so all the irregularity of the center column sits in the positions of adjacent black
pairs, a set of density about 1/4 in late rows. A proof of Problem 1 or 2 through this formula would need to control
the parity of those pairs along the kernel's support, which is as hard as the original question; it is recorded as an
exact reformulation, not a route.
