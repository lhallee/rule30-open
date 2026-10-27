---
title: The center cell has degree exactly 2t - 1 over GF(2)
category: structure
problems: [3]
status: paper
formalization: wanted
evidence: [computations/algebra.py]
---

# The center cell has degree exactly 2t - 1 over GF(2)

Write the center cell at time $t$ as a polynomial over GF(2) in the $2t + 1$ cells $x_{-t}, \dots, x_t$ of its backward
cone. For $t \ge 2$ its degree is exactly $2t - 1$, and for $t \ge 3$ it has exactly one monomial of that degree,
$x_{-t+2} x_{-t+3} \cdots x_t$. Rule 45 gives $2t - 2$ with two top monomials, and Rules 90 and 150 stay linear.

## Proof

Write $A_t(x)$ for cell $x$ at time $t$ as a polynomial in the initial cells. Over GF(2) the rule is
$p + q + r + qr$ for left, middle and right inputs.

**At most $2t - 1$.** The leftmost cone variable $x_{x-t}$ enters $A_t(x)$ only linearly: $A_t(x) = x_{x-t} + G_t(x)$
with $G_t(x)$ free of it. This holds at $t = 1$, $A_1(0) = x_{-1} + x_0 + x_1 + x_0x_1$, and is inherited, because in
$A_{t+1}(0) = A_t(-1) + A_t(0) + A_t(1) + A_t(0)A_t(1)$ only $A_t(-1)$ contains $x_{-t-1}$. So
$\deg A_{t+1}(0) = \max(1, \deg F)$ with $F = G_t(-1) + A_t(0) + A_t(1) + A_t(0)A_t(1)$ a polynomial in the $2t + 2$
cells $x_{-t}, \dots, x_{t+1}$, and no monomial of $F$ contains all of them: $G_t(-1)$ lacks $x_t$ and $x_{t+1}$,
$A_t(0)$ lacks $x_{t+1}$, $A_t(1)$ lacks $x_{-t}$, and in the product
$(x_{-t} + G_t(0))(x_{-t+1} + G_t(1))$ the monomials with $x_{-t}$ come from $x_{-t}x_{-t+1}$ or from $x_{-t}G_t(1)$,
and $G_t(1)$ lacks $x_{-t+1}$.

**Exactly one top monomial.** Expanding, $F = G_t(-1) + A_t(0) + A_t(1) + x_{-t}x_{-t+1} + x_{-t}G_t(1) +
G_t(0)x_{-t+1} + G_t(0)G_t(1)$. For $t \ge 2$ the bound gives every term but the last degree at most $2t$, and the last
is a polynomial in the $2t + 1$ cells $x_{-t+1}, \dots, x_{t+1}$. So their product is the only monomial of degree
$2t + 1$ that $A_{t+1}(0)$ can have, and it remains to show its coefficient is 1.

**The coefficient is 1.** The coefficient of $x_{-t+2} \cdots x_t$ in $A_t(0)$ equals that of
$x_{-t+2} \cdots x_{t-1}$ in the derivative $D = A_t(0)|_{x_t=1} + A_t(0)|_{x_t=0}$. A flip of $x_t$ reaches the center
only along the right edge of the cone, one cell left per step, and only while the cell beside it is 0, since the rule
reads its right input only when the middle one is 0. So $D = \prod_{s=0}^{t-1}(1 + a_s(t-1-s))$, a function of
$x_{-t+1}, \dots, x_{t-1}$. The coefficient of a monomial is the parity of the number of 1s of the function over the
assignments supported inside it, here those with $x_{-t+1} = 0$. Count them along diagonals: with $m = t - 1$ and
$d_j(s) = a_s(m - s - j)$, so that $d_j(0) = x_{m-j}$, the rule reads
$d_{j+2}(s) = d_j(s+1) + (d_{j+1}(s) \lor d_j(s))$, and a row on $[-m, m]$ corresponds one to one to its edge
diagonals $d_0(0..m)$ and $d_1(0..m-1)$. $D = 1$ says $d_0 = 0$, which leaves $u = d_1$ free and
$x_{-m} = d_{2m}(0)$, so the count is the number of $u$ with $d_{2m}(0) = 0$, whose parity is that of the weight of
$d_{2m}(0)$ over $u_0, \dots, u_{m-1}$. By induction, $d_{2k}(s)$ depends only on $u_s, \dots, u_{s+k-1}$. Over GF(2),
$d_{2k+2}(s) = d_{2k}(s+1) + d_{2k+1}(s) + d_{2k}(s) + d_{2k+1}(s)d_{2k}(s)$; counted on $u_s, \dots, u_{s+k}$, the
first term lacks $u_s$, the second is balanced in $u_{s+k}$ and the third lacks $u_{s+k}$, so each has even weight,
while the product is 1 for exactly one value of $u_{s+k}$ wherever $d_{2k}(s) = 1$. So the weights of $d_{2k+2}(s)$
and $d_{2k}(s)$ have the same parity, and from $d_2(s) = u_s$ every $d_{2k}(s)$ has odd weight.

## Computation

[computations/algebra.py](../../computations/algebra.py) evaluates the center cell on all $2^{2t+1}$ cone rows and
takes the Moebius transform. It confirms degree $2t - 1$ and the single top monomial for $t \le 9$, with 30, 122, 346,
1,360, 4,852, 23,094 and 79,192 monomials at $t = 3, \dots, 9$; code that is not in this repository extended the
counts to $t = 14$ (87,887,332 monomials). `tests/test_computations.py` checks $t \le 8$.

## What it does not say

A polynomial of high degree in the initial cells can still be cheap to evaluate on the single cell's row, so this does
not bear on Problem 3 by itself.
