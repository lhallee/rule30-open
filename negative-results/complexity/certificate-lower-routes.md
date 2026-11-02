---
title: An all-t lower bound on the least certificate of the center stops at two cells from the algebra and at an unproved window lemma that would give t/6
category: complexity
problems: [3]
status: negative
kind: dead-end
evidence: [computations/certificate_lower.py, tests/test_certificate_lower.py]
---

# An all-t lower bound on the least certificate of the center stops at two cells from the algebra and at an unproved window lemma that would give t/6

**Question.** Write $c_t$ for the center after $t$ steps of Rule 30 as a function of the cone cells
$x_{-t}, \dots, x_t$ of a row given as input, and $m(t)$ for the least number of fixed cells of a subcube (a partial
row) on which $c_t$ is constant. Is there a lower bound on $m(t)$ that grows with $t$, for every $t$: linear, or even
$\sqrt{t}$? [MinCertificate](../../Rule30Open/Complexity/MinCertificate.md) has $m(t) = t - 1$ for $9 \le t \le 15$
by computation and every constant subcube fixes $x_{-t}$, and the [routing lemma](min-certificate-routing.md), which
would have given $m(t) \ge t - 1$, fails at $t = 12$.

**Outcome.** No bound above two cells is proved for every $t$. Two routes were followed.

1. **The algebra stops at two cells, and at three on the range computed.**
   [CertificateLower](../../Rule30Open/Complexity/CertificateLower.md) proves for every $t$ that the mixed derivative
   of $c_t$ over the comb $-t + 1, -t + 3, \dots, -t + 2j + 1, -t + 2j + 2$ is $\binom{t}{j+1} \bmod 2$, so every
   constant subcube meets every comb with an odd binomial. All combs contain $x_{-t+1}$: with $x_{-t}$, two fixed
   cells meet all of them. A constant subcube must meet every maximal monomial of the algebraic normal form of $c_t$,
   and the least number of cells that meet them all is 2 or 3 for every $t \le 11$ (`hitting_number`). So no bound
   above three cells can come from the monomials of $c_t$ on that range, and the combs give two for every $t$. At
   $t = 2^v$ the shortest odd comb spans the whole left half, which is the Rule 90 behavior ($m(2^v) = 2$ there).
2. **The window lemma would give $t/6$, and it is computed only for $t \le 14$.** Let $W(t, k)$ be the least length
   $L$ such that, for every assignment of the cells outside the window $x_{-t+k}, \dots, x_{-t+k+L-1}$, $c_t$ takes
   both values on the window. Every constant subcube fixes a cell in each such window. The computation
   (`window_lengths`) gives $W(t, k) \le 6$ for every $1 \le k \le t - 2$ and $t \le 14$. If that held for every $t$,
   the disjoint windows starting at $k = 1, 7, 13, \dots$ would give $m(t) \ge 2 + \lfloor (t - 3)/6 \rfloor$ for
   $t \ge 3$. The lemma is a statement about block sensitivity: every row has a sensitive block in each window of six
   cells of the left half.

**Where it stops.** The window lemma has no proof for all $t$. A window at offset $k \ge 2$ has $k$ fixed cells to its
left, and the derivative along its first cell is the $k$-th diagonal of the difference that the flip starts, which
depends on those fixed values through the OR of the rule: the algebraic recursion of CertificateLower covers only the
window at $k = 1$, and there it needs $2^{v+1}$ cells at $t = 2^v \cdot \text{odd}$, unbounded at the powers of two,
while the computed $W(8, 1) = 6$ uses the OR. Neither the screening argument of ConeScreening, which shows that a
fixed stretch makes the center constant, nor the routing reduction, which loses the subcube shape in one step, gives
the converse that a free window always leaks to the center.

**Where the target sits.** The conjecture $m(t) = t - 1$ is false:
[StripeGrowth](../../Rule30Open/Complexity/StripeGrowth.md) proves $m(t) \le t - 2\lfloor t/9 \rfloor + 2$ for
$t \ge 9$ (so $m(t) \le t - 2$ for $t \ge 18$) and computes $m(16) = 13$. A lower bound has to sit at or below
$t - 2\lfloor t/9 \rfloor + 2 \le 7t/9 + 34/9$, and the window lemma, if true, puts $m(t)$ between about $t/6$ and
$7t/9$.

## Reproduce

```bash
python -m computations.certificate_lower --comb-t 9 --monomial-t 11 --window-t 14 --stripe ""
```

See [CertificateLower](../../Rule30Open/Complexity/CertificateLower.md) for the run times. The test
`tests/test_certificate_lower.py` checks the comb derivatives, the maximal monomials and $W(4, k)$ against listings.
