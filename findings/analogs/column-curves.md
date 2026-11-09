---
title: For a finite row under a linear automaton over a finite field whose column curve has simple small roots, a column is eventually periodic exactly when a sum over those roots is fixed by the curve's Galois group; at radius 1 this is a twisted mirror symmetry of the row, and under the four rules x_(i-2) + a x_(i-1) + b x_i + c x_(i+1) + x_(i+2) over GF(2) with a != c, whose curves have group S_4, only the all-white columns are eventually periodic
category: analogs
problems: [1]
status: paper
formalization: wanted
evidence: [computations/column_curves.py]
---

# For a finite row under a linear automaton over a finite field whose column curve has simple small roots, a column is eventually periodic exactly when a sum over those roots is fixed by the curve's Galois group; at radius 1 this is a twisted mirror symmetry of the row, and under the four rules x_(i-2) + a x_(i-1) + b x_i + c x_(i+1) + x_(i+2) over GF(2) with a != c, whose curves have group S_4, only the all-white columns are eventually periodic

Let $F$ be a linear rule $x'_i = \sum_{k=-r}^{r'} a_k x_{i+k}$ over a finite field $\mathbb{F}_q$ with $a_{-r} a_{r'}
\ne 0$ and $r' \ge 1$ (otherwise take the mirror image of the rule; when $r = r' = 0$ every column is periodic), and $x$
a nonzero finite row. Write $X(z) = \sum_i x_i z^i$, $A(z) = \sum_k a_k z^{-k}$, so that the row at time $t$ is $A(z)^t
X(z)$, and $B(z) = z^{r'} A(z)$, a polynomial of degree $n = r + r'$ with $B(0) = a_{r'} \ne 0$. The *column curve* of
$F$ is $Q(z) = z^{r'} - s B(z) = 0$ over $\mathbb{F}_q(s)$. A sequence over a finite field is eventually periodic
exactly when its generating function is rational.

## Results

1. **The criterion** (paper). Over an algebraic closure of $\mathbb{F}_q((s))$, $Q$ has $r'$ *small* roots, of valuation
   $1/r'$, and $r$ large ones. If they are simple, the generating function of column $p$ is
   $$U(s) = \sum_t u(t) s^t = \sum_{i=1}^{r'} \Psi(\rho_i) + R(s), \qquad
   \Psi(z) = \frac{z^{-p} X(z) B(z)}{r' B(z) - z B'(z)}, \quad R \in s^{-1}\mathbb{F}_q[1/s],$$
   the sum over the small roots $\rho_1, \dots, \rho_{r'}$. So column $p$ is eventually periodic exactly when this partial
   trace lies in $\mathbb{F}_q(s)$, that is, when the Galois group of $Q$ over $\mathbb{F}_q(s)$ fixes it. If the group
   is transitive on the sets of $r'$ roots and $n \ge 3$, $1 \le r' \le n - 1$, every eventually periodic column has all
   $\Psi(\rho_i)$ equal, so its partial trace is $r' \Psi(\rho_1)$.
2. **Radius 1: twisted mirror axes** (paper). For $x'_i = a x_{i-1} + b x_i + c x_{i+1}$ ($ac \ne 0$), column $p$ is
   eventually periodic exactly when
   $$x_{p+m} = -(a/c)^m\, x_{p-m} \quad \text{for every integer } m.$$
   Over GF(2) this is mirror symmetry about $p$, the case of Rules 90 and 150 that
   [SymmetricAxes](../../Rule30Open/Analogs/SymmetricAxes.md) proves in Lean by another argument. In odd characteristic
   the single cell has no eventually periodic column.
3. **Radius 2 over GF(2)** (paper, with certificates computed by `computations/column_curves.py`). For the four rules
   $x'_i = x_{i-2} + a x_{i-1} + b x_i + c x_{i+1} + x_{i+2}$ with $a \ne c$, the Galois group of the column curve is
   $S_4$, and a column of a nonzero finite row is eventually periodic exactly when it is white at every time.

## Proofs

**The criterion.** $1 - sA(z) = Q(z)/z^{r'}$, so $U(s)$ is the constant term in $z$ of $z^{-p} X(z) z^{r'}/Q(z)$,
expanded as a power series in $s$ with Laurent polynomial coefficients. That expansion is the Laurent expansion of the
rational function in the annulus $|s|^{1/r'} < |z| < |s|^{-1/r}$, where $|sA(z)| < 1$, so its constant term is the sum
of the residues of $z^{-p-1} X(z) z^{r'}/Q(z)$ at the poles in the inner disc: the small roots, which by the Newton
polygon of $Q$ (points $(0, 1)$, $(r', 0)$, $(n, 1)$) are the $r'$ roots of valuation $1/r'$, and $z = 0$. At $z = 0$
the expansion $1/Q = -\sum_k z^{kr'}/(sB(z))^{k+1}$ gives a polynomial in $1/s$ without constant term, since every term
carries a factor $s^{-(k+1)}$. At a simple root, $\rho^{r'} = sB(\rho)$ gives $Q'(\rho) = \rho^{r'-1}(r' B(\rho) - \rho
B'(\rho))/B(\rho)$, and the residue is $\Psi(\rho)$. $\Psi$ has coefficients in $\mathbb{F}_q$, so an element $g$ of the
Galois group maps $\Psi(\rho_i)$ to $\Psi(g\rho_i)$, and the partial trace over a set $S$ of roots to the one over $gS$.
If the group is transitive on $r'$-sets and fixes the trace over the small roots, the traces over all $r'$-sets are
equal; exchanging one root of a set for one outside it gives $\Psi(\rho_i) = \Psi(\rho_j)$ for all $i, j$. $\square$

**Radius 1.** Here $r = r' = 1$, $B(z) = a z^2 + bz + c$, and $U = \Psi(w) + R$ for the small root $w$, with $\Psi(z) =
z^{-p} X(z) B(z)/(c - a z^2)$. The map $z \mapsto w$ embeds $\mathbb{F}_q(z)$ into the algebraic closure, sending
$\psi(z) = z/B(z)$ to $s$, so $U$ is rational exactly when $\Psi \in \mathbb{F}_q(\psi)$. As $\psi$ has degree 2,
$[\mathbb{F}_q(z) : \mathbb{F}_q(\psi)] = 2$, and $\sigma(z) = c/(az)$ fixes $\psi$, since $B(c/(az)) = (c/(az^2))
B(z)$; so $\mathbb{F}_q(\psi)$ is the fixed field of $\sigma$. The factor $B(z)/(c - az^2)$ changes sign under $\sigma$,
so $\Psi$ is fixed exactly when $\sigma(z^{-p} X) = -z^{-p} X$, and comparing the coefficients of $z^m$ gives the
twisted symmetry. For the single cell the condition at $m = -p$ reads $x_0 = -(a/c)^{-p} x_{2p}$, which fails for $p \ne
0$, and at $p = 0$ it reads $x_0 = -x_0$, which fails in odd characteristic. $\square$

**Radius 2.** In characteristic 2, $Q = s z^4 + a s z^3 + (1 + bs) z^2 + c s z + s$ and $Q' = s(a z^2 + c)$, so $Q$ is
separable, and $\Psi = z^{-p-1} X(z) B(z)/B'(z)$ with $B' = a z^2 + c$, which does not vanish at the small roots. By
Dedekind's theorem, at a place $\pi(s) \ne s$ where $Q$ modulo $\pi$ is separable, the degrees of its irreducible
factors are the cycle type of a Frobenius element of the Galois group. For $(a, b, c) = (0, 0, 1)$, modulo $s + 1$, $Q =
z^4 + z^2 + z + 1 = (z + 1)(z^3 + z^2 + 1)$, a 3-cycle, and modulo $s^3 + s + 1$ it is irreducible, a 4-cycle; for $(0,
1, 1)$, modulo $s + 1$, $Q = z^4 + z + 1$ is irreducible, and modulo $s^2 + s + 1$ it has the pattern $(1, 3)$; the
rules $(1, 0, 0)$ and $(1, 1, 0)$ are the mirror images, with the same certificates. A subgroup of $S_4$ with a 4-cycle
and a 3-cycle has order divisible by 12 and is not $A_4$, so it is $S_4$, which is transitive on pairs. By the criterion
an eventually periodic column has partial trace $2\Psi(\rho_1) = 0$, so $U = R(s)$ is a power series in $s$ and a
polynomial in $1/s$ without constant term: $U = 0$, and the column is white at every time. Conversely such columns are
eventually periodic. $\square$

## Checks

`computations/column_curves.py` finds the certificates by counting the roots of $Q$ modulo $\pi$ in the extensions of
degrees 1 to 4 of $\mathbb{F}_2[s]/\pi$, for every place of degree at most 3, and runs the rules from every nonzero row
up to translation, with every column within 6 cells of the row, testing for a period of at most 64 on the last three
quarters of the run (a window of a single dyadic scale is not enough: a linear column over GF(2) repeats or clears its
first $2^k$ values after time $2^k$).

- **Certificates:** a 3-cycle at $\pi = s + 1$ and a 4-cycle at $s^3 + s + 1$ for $(0, 0, 1)$ and $(1, 0, 0)$; a
  4-cycle at $s + 1$ and a 3-cycle at $s^2 + s + 1$ for $(0, 1, 1)$ and $(1, 1, 0)$.
- **Radius 2,** rows of up to 9 cells, 1,024 steps: each of the four rules has 7 eventually periodic columns, all white at every time.
- **Radius 1,** 512 steps: over GF(2) (Rules 90 and 150) rows of up to 9 cells, 10,242 columns; over GF(3), all 12
  rules, rows of up to 5 cells, 16,044 columns; over GF(5), all 80 rules, rows of up to 3 cells, 29,520 columns. In every
  case a column repeats exactly when the row has the twisted symmetry about it.

## What it means

For linear rules, eventually periodic columns come from a symmetry of an algebraic curve: at radius 1 the curve always
has the deck involution $z \mapsto c/(az)$, which exchanges its small and large root, and the periodic columns are the
twisted axes of the row; at radius 2 the four curves with $a \ne c$ have group $S_4$ and no such symmetry, and a column
can repeat only by vanishing. This is the linear barrier of the kit, the eventually constant centers of Rules 90 and
150, explained by Galois theory. Rule 30 is Rule 150 plus the product term $x_i x_{i+1}$, and its center column is the
Duhamel series over its adjacent black pairs ([the Duhamel finding](../structure/duhamel.md)), an infinite sum over the
orbit that gives no algebraic equation for $U$. $U$ is algebraic over $\mathbb{F}_2(s)$ exactly when $c$ is 2-automatic
(Christol's theorem, the kit's `Christol.not_isAutomatic_iff_transcendental`), which is open, so there is no known curve
whose Galois group could be computed: this route stops at that step.

## Relation to the kit and the literature

The kit proves that the single cell's centers under Rules 90, 150 and 210 are eventually constant (`Rule30Realization`)
and has no statement about other linear rules or about Galois groups of column curves; its Frobenius is that of power
series in `Christol`. [SymmetricAxes](../../Rule30Open/Analogs/SymmetricAxes.md) proves item 2 over GF(2) in Lean by
descent on sublattices. The generating function of a column of a linear rule from a finite row is known to be algebraic:
Litow and Dumas (1993, seen only through search results) prove it, and Rowland and Yassawi (2020) and Allouche, von
Haeseler, Peitgen and Skordev (1996) relate linear automata to finite automata ([the
literature](../../literature/measure-and-analogs.md)); Jen (1988) studies the temporal sequences of linear rules over
finite fields ([the literature](../../literature/columns.md)). Their texts were not read here, so the reading of
eventual periodicity from the Galois group of the column curve, items 1 to 3, is claimed as new only against the kit and
this repository.

## Reproduce

```bash
python -m computations.column_curves --certificates --radius-two 9   # certificates; radius 2 over GF(2) (about 1 min)
python -m computations.column_curves --radius-one 2 9                # Rules 90 and 150, rows of up to 9 cells (seconds)
python -m computations.column_curves --radius-one 3 5                # radius 1 over GF(3) (seconds)
python -m computations.column_curves --radius-one 5 3                # radius 1 over GF(5) (seconds)
```

`tests/test_column_curves.py` checks the field arithmetic, the root counts against trial division over GF(2) at $s = 1$,
the convolution against the rule applied cell by cell, and both criteria on small rows.
