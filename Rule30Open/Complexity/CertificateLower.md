---
title: The mixed derivative of the center over the comb -t+1, -t+3, ..., -t+2j+1, -t+2j+2 is C(t, j+1) mod 2 on every row, so every constant subcube meets each comb with an odd binomial
category: complexity
problems: [3]
status: proved
lean: Rule30Open.Complexity.CertificateLower
headline: [combPar_zero, combPar_step, combPar_front, constOn_hits_comb, constOn_odd, constOn_two_mod_four]
kit: new
evidence: [computations/certificate_lower.py, tests/test_certificate_lower.py]
---

# The mixed derivative of the center over the comb -t+1, -t+3, ..., -t+2j+1, -t+2j+2 is C(t, j+1) mod 2 on every row, so every constant subcube meets each comb with an odd binomial

Write $c_t(x)$ for the center after $t$ steps of Rule 30 from a row $x$, a Boolean function of the cone cells
$x_{-t}, \dots, x_t$, and $m(t)$ for the least number of fixed cells of a subcube (a partial row) on which $c_t$ is
constant. [MinCertificate](MinCertificate.md) proves that every such subcube fixes $x_{-t}$. This entry finds, for
every $t$, the further cells near the left edge that it must fix, from the exact derivatives of $c_t$ there, and
measures how far this kind of argument can go.

The *comb* $B_j(t)$ is the set of the $j + 2$ cells $-t + 1, -t + 3, \dots, -t + 2j + 1$ and $-t + 2j + 2$. The
*mixed derivative* of $c_t$ over a set $B$ of cells, at a row $x$, is the xor of $c_t$ over the $2^{|B|}$ rows that
differ from $x$ only on $B$.

## Statement

1. **The comb derivatives** (`combPar_zero`, `combPar_step`, `combPar_front`). Let
   $T_j(x) = \bigoplus_{q < t} \binom{t - 1 - q}{j} \lnot x(q, -t + 2j + 2 + q)$, with the binomial taken mod 2 and
   $x(q, i)$ the cell $i$ after $q$ steps. On every row: the derivative of $c_t$ along $x_{-t+1}$ is $T_0$; the
   derivative of $T_j$ along $x_{-t+2j+3}$ is $T_{j+1}$; and the derivative of $T_j$ along $x_{-t+2j+2}$ is the
   constant $\binom{t}{j+1} \bmod 2$. So the mixed derivative of $c_t$ over $B_j(t)$ is the constant
   $\binom{t}{j+1} \bmod 2$ on every row, and when it is 1 the monomial $\prod_{i \in B_j(t)} x_i$ is a maximal
   monomial of the algebraic normal form of $c_t$.
2. **Every constant subcube meets the odd combs** (`constOn_hits_comb`). If $\binom{t}{j+1}$ is odd, every subcube
   on which $c_t$ is constant fixes a cell of $B_j(t)$. In particular (`constOn_odd`), for odd $t$ it fixes $x_{-t+1}$
   or $x_{-t+2}$, so with MinCertificate's `constOn_fixes_left` it fixes at least two of the three leftmost cone
   cells; and (`constOn_two_mod_four`) for $t \equiv 2, 3 \pmod 4$ it fixes one of $x_{-t+1}, x_{-t+3}, x_{-t+4}$. By
   Lucas's theorem the least $j$ with $\binom{t}{j+1}$ odd has $j + 1 = 2^v$, the largest power of 2 dividing $t$, so
   the shortest odd comb spans $2^{v+1}$ cells (checked against the definition for $t \le 9$ by `comb_derivative`).
3. **What the algebra gives, computed** (`hitting_number`, `window_lengths`, `window_bound`).
   - Every constant subcube fixes a cell of every maximal monomial of $c_t$. The least number of cells that meet all
     maximal monomials is 2 for $t = 1, 2, 4, 8$ and 3 for $t = 3, 5, 6, 7, 9, 10, 11$, against $m(t) = t - 1$ there
     for $t \ge 9$: the maximal monomials of $c_t$ cannot certify more than three fixed cells for $t \le 11$.
   - $W(t, k)$, the least length $L$ such that no assignment of the cells outside the window
     $x_{-t+k}, \dots, x_{-t+k+L-1}$ makes $c_t$ constant on it, is at most 6 for every $1 \le k \le t - 2$ and
     $t \le 14$; the value 6 occurs at $(t, k) = (8, 1), (13, 11), (14, 11), (14, 12)$. Every constant subcube fixes
     a cell in each such window, and the most pairwise disjoint windows give the lower bounds 4, 3, 4, 3, 5, 4 for
     $t = 9, \dots, 14$, far below $m(t)$: what counts is that the lengths stay bounded, not these numbers.

## Proof

**Item 1.** Flip a cell $a$. By ConeScreening's `front_xor`, the cell $(q, a + q)$ flips on every row, for every $q$.
By SecondCells' `flip_second_cell`, the cell $(q, a - 1 + q)$ changes by $\bigoplus_{r < q} \lnot x(r, a + 1 + r)$. The
derivative along $x_{-t+1}$ is SecondCells' `center_flip_second`, which is $T_0$ since $\binom{n}{0} = 1$. In $T_j$
the cells $(q, -t + 2j + 2 + q)$ are the front of a flip of $-t + 2j + 2$, so that flip changes $T_j$ by
$\bigoplus_{q < t} \binom{t - 1 - q}{j} = \binom{t}{j+1}$ mod 2 (the hockey-stick identity, `fsum_pasc`). They are one
cell left of the front of a flip of $-t + 2j + 3$, so that flip changes $T_j$ by
$\bigoplus_{q < t} \binom{t-1-q}{j} \bigoplus_{r < q} \lnot x(r, -t + 2j + 4 + r)$. Exchanging the two sums
(`fsum_pasc_exchange`) puts the weight $\bigoplus_{r < q < t} \binom{t-1-q}{j} = \binom{t - 1 - r}{j + 1}$ on the
cell $r$, which is $T_{j+1}$. In Lean the binomial parity is Pascal's rule mod 2 (`pasc`), with `pasc_one` and
`pasc_two` for $\binom{t}{1} = t$ and $\binom{t}{2}$.

**Item 2.** Suppose $c_t$ is constant on a subcube that leaves every cell of $B_j(t)$ free. Flipping a free cell
keeps a row in the subcube (`fillRow_flipAt_none`), so the derivative of $c_t$ along $x_{-t+1}$ is 0 at every row of
the subcube, so $T_0$ is, and by induction every $T_i$ with $i \le j$; the derivative of $T_j$ along $x_{-t+2j+2}$ is
then 0, but it is $\binom{t}{j+1} \bmod 2 = 1$.

**Item 3.** `maximal_monomials` takes the Moebius transform of the table of $c_t$ and keeps the monomials with no
strictly larger monomial; `hitting_number` lists the sets of at most four cells. `window_lengths` checks every
assignment of the cells outside each window. The test checks the comb derivatives for $t \le 4$, the maximal
monomials and the hitting number at $t = 3$, and $W(4, k)$ against listings that run Rule 30 on lists.

## What it means

These are the facts about $m(t)$ that the left-permutive structure gives for every $t$. They are not a lower bound
beyond two cells: every comb contains $x_{-t+1}$, and fixing it meets them all. The computed hitting numbers say the
same of the whole algebraic normal form for $t \le 11$: its maximal monomials are met by three cells. Any lower bound
that grows with $t$ has to use the values of the fixed cells, through the OR of the rule, as the windows do; the comb at
$t = 2^v$ spans the whole left half, as for Rule 90, where $c_{2^v} = x_{-2^v} \oplus x_{2^v}$ and $m(2^v) = 2$.
[StripeGrowth](StripeGrowth.md) shows the other side: $m(t) \le t - 2\lfloor t/9 \rfloor + 2$, so $m(t) = t - 1$ fails
for large $t$. The window route and where it stops are recorded in
[routes to a lower bound](../../negative-results/complexity/certificate-lower-routes.md).

The kit's `AlgebraicDegree` (in its equivalent forms) has the one-step derivative along the left diagonal
(`deriv_evol_diag_succ`) and the top monomial $x_{-t+2} \cdots x_t$; it has no comb derivative, binomial weights or
statement about subcubes (its core Lean, its equivalent forms and its main branch were searched).

## Reproduce

```bash
python -m computations.certificate_lower --comb-t 9 --monomial-t 11 --window-t 14 --stripe ""
```

The maximal monomials take a few seconds and the windows about three minutes, most of it at $t = 14$ (under 2 GB).
The test `tests/test_certificate_lower.py` runs in a fraction of a second.
