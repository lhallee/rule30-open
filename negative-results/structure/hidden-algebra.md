---
title: No small algebraic equation for the center column, and no Rule 30 signal in the cut ranks of the cone
category: structure
problems: [1, 3]
status: negative
kind: no-signal
evidence: [computations/wild_ideas.py, tests/test_wild_ideas.py]
---

# No small algebraic equation for the center column, and no Rule 30 signal in the cut ranks of the cone

**Question.** Three tests of hidden algebraic structure, each with a random control and a positive control that the
test must find. Is the center column's generating series $f = \sum c(n) x^n$ a root of a small equation over
$\mathrm{GF}(2)(x)$? Is the column, read as the 2-adic integer $z = \sum c(n) 2^n$ or as the real number
$r = \sum c(n) 2^{-n-1}$, a root of an integer polynomial of low degree with moderate coefficients? Does the center
cell $c_t$, as a Boolean function of its cone $x_{-t}, \dots, x_t$, have low GF(2) rank across a cut, beyond what
every rule of its form has?

## 1. Ore equations over GF(2)(x)

**Test.** Polynomials $P_{-1}, P_0, \dots, P_k$ over GF(2), each of degree at most $D$, not all zero, with

$$P_{-1} + P_0 f + P_1 f^2 + P_2 f^4 + \dots + P_k f^{2^k} \equiv 0 \pmod{x^n}.$$

In characteristic 2, $f^{2^i} = f(x^{2^i})$, so these are the Mahler-type equations, and $f$ satisfies one for some
$k$ and $D$ exactly when $c$ is 2-automatic (Christol; the kit's
[`Christol`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/equivalents/Rule30Equivalents/Christol.lean),
`exists_ore_relation`). The solutions modulo $x^n$ form a GF(2) space; `ore_profile` gives its dimension for each $D$ by
inserting the $(k + 2)(D + 1)$ series $x^j f^{2^i}$ into a GF(2) basis. A random series has no solution until the
unknowns $(k + 2)(D + 1)$ reach the $n$ equations. $D^*$ below is the least $D$ with a solution.

| $n$ | $k$ | center $D^*$ | random $D^*$ | unknowns $- n$ at $D^*$, center / random | Thue-Morse $D^*$ | period-doubling $D^*$ |
|---:|---:|---:|---:|---:|---:|---:|
| 8,192 | 0 | 4,095 | 4,096 | 0 / 2 | none to 64 | none to 64 |
| 8,192 | 1 | 2,730 | 2,730 | 1 / 1 | 3 | 3 |
| 8,192 | 2 | 2,047 | 2,047 | 0 / 0 | 3 | 3 |
| 8,192 | 3 | 1,638 | 1,638 | 3 / 3 | 3 | 3 |
| 8,192 | 4 | 1,365 | 1,365 | 4 / 4 | 3 | 3 |
| 8,192 | 5 | 1,170 | 1,170 | 5 / 5 | 3 | 3 |
| 32,768 | 1 | 10,922 | not run | 1 / not run | | |
| 32,768 | 2 | 8,191 | not run | 0 / not run | | |

**Outcome.** The center column behaves exactly like the random control: a solution appears at the first $D$ at which
the unknowns reach the equations, never earlier. So no equation of this shape with
$(k + 2)(D + 1) < n$ holds, for $k \le 5$ at $n = 8{,}192$ and $k \le 2$ at $n = 32{,}768$; for example, no equation
$P_{-1} + P_0 f + P_1 f^2 \equiv 0 \pmod{x^{32768}}$ with all degrees at most 10,921. The two 2-automatic controls are found at $D = 3$
for every $k \ge 1$ (Thue-Morse satisfies $x + (1 + x)^2 f + (1 + x)^3 f^2 = 0$). The case $k = 0$ is
[the linear complexity](../complexity/linear-complexity.md). The test measures something other than
[the automaton bounds](../complexity/automaton-lower-bounds.md): it excludes algebraic equations of small degree and
small height, which can have automata of many states, and the automaton bounds exclude small automata, whose
equations can have large height. Neither covers the other.

## 2. Integer relations by LLL

**Test.** `lll` is an exact integer LLL with $\delta = 3/4$, so the first reduced vector $b_1$ is at most
$2^{(N-1)/2}$ times every nonzero vector of an $N$-dimensional lattice.

- **2-adic.** The lattice of $(a_0, \dots, a_d) \in \mathbb{Z}^{d+1}$ with $\sum a_i z^i \equiv 0 \pmod{2^m}$, of
  determinant $2^m$. A root of $P$ is a root modulo every $2^m$, so every polynomial of degree at most $d$ with root
  $z$ has coefficient norm at least $|b_1| 2^{-d/2}$.
- **Real.** Rows $(e_i, \lfloor 2^{m-8} r^i \rfloor)$, $i = 0, \dots, d$, from the first $m$ bits of $r$. An exact
  relation $P(r) = 0$ gives a lattice vector of norm at most $|a| \sqrt{1 + 4(d + 1)}$.
- **Constants.** The same embedding for one linear relation among $r$, 1, $\sqrt 2$, $\sqrt 3$, $\sqrt 5$, $\pi$, $e$
  and $\log 2$, all computed on integers to $m$ bits.

Every lattice here has volume about $2^{m}$ or $2^{m-8}$, so a lattice without a planted short vector has
$\log_2 |b_1|$ near $m / (d + 1)$ (the Gaussian heuristic, which the random control follows).

| $m = 4{,}096$ bits, $\log_2 \lvert b_1 \rvert$ | $d = 2$ | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---:|---:|---:|---:|---:|---:|---:|
| 2-adic: heuristic $m / (d + 1)$ | 1365.3 | 1024.0 | 819.2 | 682.7 | 585.1 | 512.0 | 455.1 |
| 2-adic: center $z$ | 1365.2 | 1023.0 | 818.7 | 682.7 | 584.9 | 511.8 | 455.0 |
| 2-adic: random bits | 1363.9 | 1024.0 | 818.7 | 682.3 | 584.9 | 511.3 | 454.6 |
| 2-adic: root of $x^2 + x - 4$ | 2.1 | 2.1 | 2.1 | 2.1 | 2.1 | 2.1 | 2.1 |
| 2-adic: cube root of 9 | 1365.1 | 3.2 | 3.2 | 3.2 | 3.2 | 3.2 | 3.2 |
| real: heuristic $(m - 8) / (d + 1)$ | 1362.7 | 1022.0 | 817.6 | 681.3 | 584.0 | 511.0 | 454.2 |
| real: center $r$ | 1361.9 | 1021.6 | 817.5 | 681.1 | 584.1 | 510.4 | 454.0 |
| real: random bits | 1360.3 | 1021.3 | 817.5 | 681.4 | 583.7 | 511.1 | 454.5 |
| real: $2^{1/3} - 1$ | 1362.4 | 2.9 | 2.3 | 2.2 | 2.2 | 2.2 | 2.2 |

**Outcome.** The center column sits on the Gaussian heuristic, like the random control, at every degree; the planted
algebraic numbers are found at the first degree where they can be. So $z$ is a root of no nonzero integer polynomial
of degree at most 8 with coefficient norm below $2^{451}$ ($455.0 - 8/2$), and of none of degree at most 2 below
$2^{1364}$; $r$ is a root of none of degree at most 8 with coefficient norm below $2^{447}$. For the constants, the first reduced vector has
$\log_2 \lvert b_1 \rvert = 511.2$ for the center (heuristic 511.0, random control 511.0) and involves $r$, so no
integer relation $a_0 r + a_1 + a_2 \sqrt 2 + a_3 \sqrt 3 + a_4 \sqrt 5 + a_5 \pi + a_6 e + a_7 \log 2 = 0$ with
$a_0 \ne 0$ has coefficient norm below $2^{505}$; the planted $r = \pi + \sqrt 2 - 4$ gives 2.2 and the relation
$(-1, -4, 1, 0, 0, 1, 0, 0)$. These are statements about the first 4,096 cells. Degree 1 is [the kit's](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/equivalents/Rule30Equivalents/TwoAdic.lean)
2-adic complexity (`problem1_iff_two_adic_complexity`); Problem 1 asks only that $z$ and $r$ be irrational, and an
algebraic irrational $z$ or $r$ would not contradict it, so this test looks for structure, not for a proof.

## 3. Communication rank of the cone across a cut

**Test.** Index the $2^{2t+1}$ values of $c_t$ by the $a$ leftmost cone cells (columns) and the other
$b = 2t + 1 - a$ cells (rows); `cut_rank` is the GF(2) rank of that matrix. It is at most the number of distinct
rows or columns (`distinct_lines`). Two facts about Rule 30, $x_j' = x_{j-1} \oplus (x_j \lor x_{j+1})$, cap
the rank: $c_t = x_{-t} \oplus g$, so columns pair into complements, and $x_{t-1}, x_t$ enter only through
$x_{t-1} \lor x_t$. The control keeps both facts with a random $g$. Rules 45,
$x_{j-1} \oplus (x_j \lor \lnot x_{j+1})$, and 120, $x_{j-1} \oplus (x_j \land x_{j+1})$, are left-permutive rules of the same shape outside Rule 30's
symmetry class; Rule 150 is linear. All cuts, $t \le 11$.

| $t = 11$, cut $a$ | 4 | 6 | 8 | 9 | 10 | 11 | 12 | 14 | 16 | 18 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Rule 30 rank | 7 | 23 | 87 | 172 | 153 | 104 | 79 | 39 | 19 | 9 |
| distinct rows or columns | 16 | 64 | 256 | 210 | 167 | 108 | 85 | 42 | 20 | 9 |
| random $g$ with the two facts | 9 | 33 | 129 | 257 | 513 | 1025 | 1024 | 256 | 64 | 16 |
| Rule 45 rank | 7 | 23 | 87 | 153 | 116 | 83 | 63 | 33 | 17 | 9 |
| Rule 120 rank | 7 | 23 | 86 | 165 | 139 | 102 | 79 | 43 | 22 | 11 |

The largest rank over all cuts, for $t = 4, \dots, 11$:

| $t$ | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Rule 30 | 7 | 10 | 19 | 26 | 44 | 79 | 104 | 172 |
| Rule 45 | 6 | 9 | 14 | 23 | 40 | 63 | 87 | 153 |
| Rule 120 | 6 | 11 | 20 | 28 | 43 | 78 | 102 | 165 |
| random $g$ with the two facts | 9 | 17 | 33 | 65 | 129 | 257 | 513 | 1025 |

Rule 150 has rank at most 2 at every cut.

**Outcome.** The rank of $c_t$ is far below the random control, but the deficit belongs to the rule's shape, not to
Rule 30:

- On the right cuts the rank is within a few percent of the number of distinct rows, which is the right channel's
  narrowness already counted in [the screening finding](../../findings/complexity/cone-screening.md) ($N_{\mathrm{R}}$);
  for $b \le t + 2$ it depends only on $b$ in this range: 2, 2, 4, 5, 9, 12, 19, 26, 39, 53, 79, 104, 153 for
  $b = 1, \dots, 13$.
- On the left cuts, $a \le t - 2$, the rank is $2 + (J_{a+1} - 1)/2$ for every $t \le 11$, with $J_n = (2^n - (-1)^n)/3$
  the Jacobsthal numbers: 2, 3, 4, 7, 12, 23, 44, 87, 172 for $a = 1, \dots, 9$, about a third of the $2^a$ distinct
  columns. Rule 45 has the same values for $a \le 8$ (153 at $a = 9$, $t = 11$); Rule 120 for $a \le 5$, and a few fewer
  beyond. This is an observation on
  the range computed, without a proof; it fits the staircase in which the leftmost cells enter a left-permutive rule
  (the kit's `AlgebraicDegree`, `coef_evol_eq_zero`).
- Wherever both profiles are known, the rank at a cut is the smaller of the two, and the largest rank over cuts grows like that of Rules 45
  and 120.

So GF(2) rank adds nothing to the distinct-subfunction counts on the right, and on the left it shows a structure that
two other left-permutive rules share. A bound on the rank across one cut also cannot give more than the crossing
argument of [the one-tape barrier](../complexity/one-tape-crossing.md) for Problem 3.

## What it means

Within these ranges the center column has no algebraic equation over $\mathrm{GF}(2)(x)$ of small size, its 2-adic
and real values have no low-degree integer relation with coefficients far below the lattice's random scale, and the
cone function's cut ranks are those of its rule class. Each test found its positive control at once, so each could
have seen the structure it looks for.

## Reproduce

```bash
python -m computations.wild_ideas ore --cells 8192 --max-k 5    # table 1, n = 8,192 (minutes)
python -m computations.wild_ideas lll --bits 4096 --max-degree 8 # table 2 and the constants (minutes)
python -m computations.wild_ideas rank --max-t 11                # table 3 (a few minutes)
```

The $n = 32{,}768$ rows of table 1 come from `ore_profile(center_column(32768), k, 32768, 32768 // (k + 2) + 4)` in
[computations/wild_ideas.py](../../computations/wild_ideas.py), about ten minutes for each $k$.
[tests/test_wild_ideas.py](../../tests/test_wild_ideas.py) checks the Ore solution space against enumeration of every
coefficient vector, the GF(2) ranks against a second elimination, the LLL output against the Lovász condition and the
lattice determinant, the planted roots, the constants against floating point, and $c_t$ against
[computations/algebra.py](../../computations/algebra.py).
