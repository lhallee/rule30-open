---
title: An odd-weight function has Walsh coefficients 2 mod 4 and an XOR lift that is its own inverse over GF(2), so the center after t steps has at least 2^(2t-1) nonzero Walsh coefficients and an XOR lift of GF(2) rank at least 2^(2t-1), where Rules 90 and 150 have 1 and 2
category: complexity
problems: [3]
status: proved
lean: Rule30Open.Complexity.ParityLift
headline: [cubeWalsh_emod_four, lift_sq, liftApply_liftApply, lift_injective, walsh_support_of_flip, coneFn_flip, center_walsh_emod_four, center_lift_sq, center_walsh_support, center_odd_small]
kit: new
kit_modules: [Rule30Equivalents.AlgebraicDegree]
evidence: [computations/parity_lift.py, tests/test_parity_lift.py]
---

# An odd-weight function has Walsh coefficients 2 mod 4 and an XOR lift that is its own inverse over GF(2), so the center after t steps has at least 2^(2t-1) nonzero Walsh coefficients and an XOR lift of GF(2) rank at least 2^(2t-1), where Rules 90 and 150 have 1 and 2

Write $c_t(x)$ for the center cell after $t$ steps of Rule 30 from a row $x$, a Boolean function of the $2t + 1$ cells
$x_{-t}, \dots, x_t$ of its cone, and $f_t$ for $c_t$ with $x_{-t} = x_{-t+1} = 0$, a function of the $2t - 1$ cells
$x_{-t+2}, \dots, x_t$. For a Boolean function $g$ on $\{0,1\}^m$ write

- $\mathrm{wt}(g)$ for the number of words $x$ with $g(x) = 1$, its *weight*;
- $W_g(a) = \sum_x (-1)^{g(x) \oplus a \cdot x}$ for its Walsh coefficient at $a \in \{0,1\}^m$, and
  $\mathrm{spar}(g)$ for the number of $a$ with $W_g(a) \ne 0$, its *Fourier sparsity*;
- $M_g[x, y] = g(x \oplus y)$ for its *XOR lift*, a $2^m \times 2^m$ matrix of 0s and 1s.

The XOR lift is the matrix of the two-party problem in which Alice holds $x$, Bob holds $y$, and they compute
$g(x \oplus y)$. Rules 90 and 150 give linear functions, for which every quantity below is at most 2.

## Statement

1. **Walsh coefficients of an odd-weight function** (Lean, every $m \ge 2$). If $\mathrm{wt}(g)$ is odd, then
   $W_g(a) \equiv 2 \pmod 4$ for every $a$; in particular no Walsh coefficient is 0 (`cubeWalsh_emod_four`).
2. **The XOR lift of an odd-weight function** (Lean, every $m$). Over GF(2),
   $\sum_y g(x \oplus y)\, g(y \oplus z) = \mathrm{wt}(g) \cdot [x = z]$ (`lift_sq_weight`). So if $\mathrm{wt}(g)$ is
   odd, $M_g^2 = 1$ over GF(2) (`lift_sq`): the map $v \mapsto M_g v$ on GF(2) vectors indexed by the cube is its own
   inverse (`liftApply_liftApply`) and injective (`lift_injective`), so $M_g$ has GF(2) rank $2^m$.
3. **Walsh support** (Lean, every $m \ge 2$). If $h$ on $m + 2$ cells flips with its first cell and $h$ with its first
   two cells set to 0 has odd weight, then $\mathrm{spar}(h) \ge 2^m$ (`walsh_support_of_flip`).
4. **Rule 30** (Lean with a hypothesis from the kit, every $t \ge 2$). The center flips with the first cell of its cone
   (`coneFn_flip`). If $\mathrm{wt}(f_t)$ is odd, then every $W_{f_t}(a)$ is $2 \bmod 4$ (`center_walsh_emod_four`),
   $M_{f_t}^2 = 1$ over GF(2) (`center_lift_sq`), and $\mathrm{spar}(c_t) \ge 2^{2t-1}$ (`center_walsh_support`).
   The weight of $f_t$ is odd for every $t \ge 2$: that is the kit's `AlgebraicDegree.coef_center_top`, see the
   proof. `center_odd_small` checks it in Lean by evaluation for $t = 2, 3, 4, 5$.
5. **Consequences in three models** (paper, every $t \ge 2$, from item 4 and standard lemmas).
   - *Communication of the XOR lift.* Let $D_t$ be the deterministic communication complexity of
     $(x, y) \mapsto c_t(x \oplus y)$, $x, y \in \{0,1\}^{2t+1}$, with the answer determined by the transcript. Then
     $2t \le D_t \le 2t + 2$. Through GF(2) alone, $D_t \ge 2t - 1$.
   - *Parity decision trees.* A tree that queries parities of cells needs depth at least $2t - 1$ to compute $c_t$,
     and $2t + 1$ suffice.
   - *Controls.* For Rules 90 and 150, $c_t$ is a parity of cells: Fourier sparsity 1, XOR lift of rank at most 2 over
     any field, communication 2 bits, one parity query.
6. **Computed** (`computations/parity_lift.py`). For $2 \le t \le 10$, $\mathrm{wt}(f_t)$ is odd, every
   $W_{f_t}(a)$ is $2 \bmod 4$ and the least $|W_{f_t}(a)|$ is 2. The Fourier sparsity of $c_t$, of at most $2^{2t}$:

| $t$ | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $2^{2t-1}$ (item 4) | 8 | 32 | 128 | 512 | 2,048 | 8,192 | 32,768 | 131,072 | 524,288 |
| Rule 30 | 8 | 44 | 202 | 878 | 3,618 | 15,033 | 61,672 | 250,168 | 1,017,427 |
| Rule 45 | 10 | 30 | 151 | 600 | 2,530 | 10,523 | 44,061 | 181,435 | 735,492 |
| Rule 120 | 10 | 46 | 212 | 889 | 3,668 | 15,238 | 61,979 | 251,811 | 1,006,069 |
| Rules 90, 150 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |

   The GF(2) ranks of the XOR lifts, for $2 \le t \le 6$:

| $t$ | 2 | 3 | 4 | 5 | 6 |
|---|---:|---:|---:|---:|---:|
| Rule 30, $f_t$ and $c_t$ | 8 | 32 | 128 | 512 | 2,048 |
| Rule 45, $f_t$ | 4 | 16 | 64 | 256 | 1,024 |
| Rule 45, $c_t$ | 8 | 24 | 80 | 304 | 1,184 |
| Rule 120, $f_t$ and $c_t$ | 8 | 32 | 128 | 512 | 2,048 |
| Rules 90, 150, $f_t$ and $c_t$ | 2 | 2 | 2 | 2 | 2 |

   Rule 120, $x_{j-1} \oplus (x_j \land x_{j+1})$, has $\mathrm{wt}(f_t)$ odd for $2 \le t \le 10$, so items 1 to 5
   hold for it on that range; Rule 45, $x_{j-1} \oplus (x_j \lor \lnot x_{j+1})$, has $\mathrm{wt}(f_t)$ even there.

## Proof

**Item 1.** Write $g$ and $\ell(x) = a \cdot x$ as 0/1 integers. Since $(-1)^{g \oplus \ell} = 1 - 2g - 2\ell + 4g\ell$,
$$W_g(a) = 2^m - 2\,\mathrm{wt}(g) - 2\,\mathrm{wt}(\ell) + 4\,\mathrm{wt}(g \land \ell).$$
Here $2^m \equiv 0 \pmod 4$ for $m \ge 2$, and $\mathrm{wt}(\ell)$ is even on $m \ge 2$ cells: split on the first cell
$x_0$. If $a_0 = 0$ both halves have the weight of $\ell$ on the other cells; if $a_0 = 1$ the halves have
complementary values, so the weight is $2^{m-1}$. So $W_g(a) \equiv -2\,\mathrm{wt}(g) \equiv 2 \pmod 4$
(`cubeCount_emod_two`, `cubeCount_dot_even`). This is the standard identity
$W_g(a) = 2^m [a = 0] - 2 \sum_x g(x) (-1)^{a \cdot x}$ read mod 4, as in Carlet's book.

**Item 2.** Substitute $y = u \oplus x$, a translation of the cube (`cubeXor_translate`):
$\sum_y g(x \oplus y) g(y \oplus z) = \sum_u g(u)\, g(u \oplus d)$ with $d = x \oplus z$. At $d = 0$ this is
$\sum_u g(u) = \mathrm{wt}(g) \bmod 2$. At $d \ne 0$ the terms at $u$ and $u \oplus d$ are equal, so they cancel in
pairs over GF(2); the Lean proof does this by induction on $m$, splitting on the first cell of $d$
(`cubeXor_autocorr`). Then $M_g(M_g v) = (M_g^2) v = v$ by exchanging the two sums (`cubeXor_comm`).

**Item 3.** Write $h = h(b, b', x)$ with $b$, $b'$ the first two cells, $g = h(0, \cdot, \cdot)$ and
$r = h(0, 0, \cdot)$. Since $h(1, \cdot) = \lnot g$, $W_h(0, a') = 0$ and $W_h(1, a') = 2 W_g(a')$
(`cubeWalsh_flip`), so $\mathrm{spar}(h) = \mathrm{spar}(g)$. Splitting $g$ on $b'$,
$W_g(0, a) + W_g(1, a) = 2 W_r(a)$ (`cubeWalsh_cons`), which is not 0 by item 1. So for each of the $2^m$ words $a$
at least one of $W_g(0, a)$, $W_g(1, a)$ is nonzero (`walsh_support_ge`).

**Item 4.** `coneFn t` reads a word as the cells $x_{-t}, x_{-t+1}, \dots$ of a row that is white elsewhere, and
`coneFn_flip` is `flip_center` of [ConeScreening](ConeScreening.md). The odd weight of $f_t$: the kit defines the
algebraic normal form coefficient of the monomial $\prod_{i \in S} x_i$ as
`coef f S = ∑ U ∈ S.powerset, [f (ind U)]` in ZMod 2, where `ind U` is the row that is black exactly on $U$. With
$S = \{2 - t, \dots, t\}$ this is the number of rows black only inside $S$ on which the center is black, mod 2, which
is $\mathrm{wt}(f_t) \bmod 2$. `AlgebraicDegree.coef_center_top` proves it is 1 for $t \ge 2$. The kit's equivalent forms
need Mathlib and this repository builds only the kit's core, so, as in [QueryDepth](QueryDepth.md), the two Lean
proofs are joined on paper: the Lean statements here take odd weight as the hypothesis `hodd`. The kit's
`evol` and the `evo` used here are the same function (QueryDepth.md).

**Item 5, communication.** Kushilevitz and Nisan (1997, Lemma 1.28): a protocol with transcript of at most $D$ bits
partitions the matrix of the problem into at most $2^D$ monochromatic rectangles, so the matrix is a sum of at most
$2^D$ matrices of rank 1 over any field and $D \ge \log_2 \mathrm{rank}$.
- *Real rank.* The 0/1 matrix $M_{c_t}$ is diagonalized by the characters of $\{0,1\}^{2t+1}$, with eigenvalue
  $\sum_x c_t(x)(-1)^{a \cdot x} = (2^{2t+1}[a = 0] - W_{c_t}(a))/2$ at $a$. At $a = 0$ it is $2^{2t} \ne 0$ ($c_t$ is
  balanced, the kit's `card_center_true`), and at $a \ne 0$ it is nonzero exactly when $W_{c_t}(a) \ne 0$. So the real
  rank is $\mathrm{spar}(c_t) + 1 \ge 2^{2t-1} + 1$ by item 4, and $D_t \ge \lceil \log_2(2^{2t-1} + 1) \rceil = 2t$.
- *GF(2) rank.* Restricting both players to rows with $x_{-t} = x_{-t+1} = y_{-t} = y_{-t+1} = 0$ gives the submatrix
  $M_{f_t}$, of GF(2) rank $2^{2t-1}$ by item 4, so $D_t \ge 2t - 1$.
- *Upper bound.* Alice sends $x_{-t+1}, \dots, x_t$ ($2t$ bits). Bob replies with $y_{-t} \oplus g$, where $g$ is
  the center after $t$ steps from $x \oplus y$ with cell $-t$ set white, which he can now compute. Alice adds
  $x_{-t}$ and has the answer by `center_decomp` of [ConeScreening](ConeScreening.md), and sends it:
  $D_t \le 2t + 2$, or $2t + 1$ if only one player must learn the answer.

**Item 5, parity decision trees.** A tree of depth $d$ that queries parities of cells computes the sum over its
1-leaves of products of $d$ affine forms over GF(2), a polynomial of degree at most $d$. The kit's
`AlgebraicDegree.isGreatest_card_coef_center` gives $c_t$ degree $2t - 1$ over GF(2). The ordinary tree that reads all
$2t + 1$ cells gives the upper bound. This item uses only the kit's degree theorem, not items 1 to 4.

**Item 6.** `walsh` is the fast Walsh-Hadamard transform, tested against the direct sum for $t \le 4$; `gf2_rank` is
elimination on 64-bit words, tested against an elimination on Python integers.

## The ceiling of the method

- *GF(2).* The GF(2) rank of the whole lift $M_{c_t}$ is $2^{2t-1}$ for $2 \le t \le 6$, no more than the restricted
  block (item 6). So on that range GF(2) log-rank gives $2t - 1$ and no more.
- *Real.* Only the $2^{2t}$ coefficients $W_{c_t}(a)$ with $a_{-t} = 1$ can be nonzero (the kit's
  `walsh_center_eq_zero`), so the real rank is at most $2^{2t} + 1$ and real log-rank gives at most $2t + 1$; for
  $2 \le t \le 10$ the computed sparsity is below $2^{2t} - 1$, so it gives exactly $2t$.
- *Parity decision trees.* The degree gives $2t - 1$; whether every such tree needs $2t$ or $2t + 1$ queries is not
  settled here.

Each bound is linear in $t$, the size of the cone, and the trivial algorithm meets it up to an additive constant. In
these models Rule 30 is separated from the linear rules for every $t$, but not from Rule 120, which has the same
weight parity on the range computed.

## Scope

These are statements about the center as a function of an arbitrary row of $2t + 1$ cells. They say nothing about the
single seed's center column $c(n)$ or the cost of computing it from the digits of $n$, the kit's `Problem3`, where the
input is $\log_2 n$ bits and a lower bound linear in $n$ is the question. The restricted models of
[restricted models](../../negative-results/complexity/restricted-models.md) and [the index
spectrum](../../negative-results/complexity/index-function-spectrum.md), which concern $c(n)$ as a function of the
digits of $n$, are a different function. The GF(2) cut ranks of the cone in [hidden
algebra](../../negative-results/structure/hidden-algebra.md) split the cells between the players; the XOR lift gives
each player a whole row.

## What the kit has

The kit's `AlgebraicDegree` (equivalent forms) defines `coef` and `walsh` over Finset subcubes, proves the degree
$2t - 1$ (`isGreatest_card_coef_center`, `coef_center_top`), `walsh_center_eq_zero` (every Walsh coefficient at an $a$
with $a_{-t} = 0$ vanishes) and the balance `card_center_true`. Neither the pinned kit nor its main branch has Walsh
coefficients mod 4, a Fourier sparsity bound, an XOR lift or its rank, or a communication or parity decision tree
bound; its `Matrix.rank` uses (`LinearComplexity`, `LinearRelations`) concern the center column's linear complexity.
Items 1 and 2 are standard for Boolean functions (Carlet; for XOR functions, Montanaro and Osborne); the Lean proofs
and the Rule 30 bounds are new here.

## Sources

- E. Kushilevitz and N. Nisan, *Communication Complexity*, Cambridge University Press, 1997, Lemma 1.28 (log-rank).
- C. Carlet, *Boolean Functions for Cryptography and Coding Theory*, Cambridge University Press, 2021 (Walsh
  coefficients and weight).
- A. Montanaro and T. J. Osborne, On the communication complexity of XOR functions, arXiv:0909.3392, 2009 (XOR
  functions, Fourier sparsity and parity decision trees).

## Reproduce

```bash
lake build Rule30Open.Complexity.ParityLift
python -m computations.parity_lift --max-t 10 --rank-t 6    # about 20 s and 0.6 GB on one core
python -m pytest tests/test_parity_lift.py
```
