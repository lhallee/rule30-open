---
title: The first twelve forced bits of the period-two condition are dense polynomials of full degree
category: period-two
problems: [1]
status: negative
kind: dead-end
evidence: [computations/held_shift.py]
---

# The first twelve forced bits of the period-two condition are dense polynomials of full degree

**Idea.** The points of the period-two Cantor set $K$ are the graph of a map from the free bits $u_0, u_2, \dots$ to
the forced bits $u_1, u_3, \dots$ ([the shift model](../../findings/period-two/shift-model.md)). A positive integer
in $K$ needs the forced bits to vanish from some point on. If the forced bit $u_{2s+1}$ were a polynomial over GF(2) of
low degree, or with few monomials, in $u_0, \dots, u_{2s}$, a vanishing condition could be solved as a system of
equations, or shown to have no solution by a degree or weight count.

**Where it stops.** Computed from the truth tables of the tree of forced bits for $s \le 11$ (up to $u_{23}$), the
forced bit $u_{2s+1}$ is a
polynomial in the $s + 1$ free bits $u_0, u_2, \dots, u_{2s}$ of algebraic degree $s + 1$, the number of variables (the product of all of them
is a monomial), with about half of all the monomials, from $s = 5$ on:

| $s$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| degree | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
| monomials | 2 | 4 | 6 | 10 | 20 | 40 | 56 | 128 | 252 | 492 | 1,004 | 1,936 |
| of at most | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1,024 | 2,048 | 4,096 |

(`python -m computations.held_shift --degree 25`, $s$ counted from 0.) The even bits are the free variables, of degree 1 with one monomial. The OR in the rule
makes each forced bit a product of the earlier ones, and the count of monomials approaches half the possible ones, as a
random polynomial's would. A solution of the vanishing conditions is a point of a variety defined by polynomials of
growing degree and weight, with no structure for a degree bound or a linear-algebra step to use.

**What it means.** It agrees with [the linear parity checks](no-finite-certificate.md), where the only parity checks
over 14 free cells are two, and closes the polynomial reading of the problem: a certificate that rests on the forced
bits being sparse or low in degree does not exist at these sizes.

**Other readings tried here.**

- A potential on the distance to the stripes, the 2-adic valuations of $3U + 1$ and $3U + 2$
  ([Domains](../../Rule30Open/PeriodTwo/Domains.md)): $K$ has $2^{\lceil d/2 \rceil}$ of the $2^d$ residues modulo
  $2^d$ ([the shift model](../../findings/period-two/shift-model.md), item 1, and the kit's `count_constrained`), so
  under the uniform measure on the free bits the points of $K$ that agree with a stripe on their first $k$ bits are a
  fraction $2^{-\lceil k/2 \rceil}$ of $K$, and most points of $K$ are far from both stripes; the temporally periodic points of $K$ include the ether and domains of spatial period 60 to over 38,000
  ([the shift model](../../findings/period-two/shift-model.md)), so no function of the distance to the two stripes
  can bound the survival of a point of $K$. No monotone quantity was found.
- A column further left forced periodic: beside an alternating center the cells of columns $-1, -2, -3$ are the
  gate at the even times, complemented or repeated ($x_{-2}(t) = \lnot x_{-1}(2\lceil t/2 \rceil)$, $x_{-3}(t) = x_{-1}(t + 2)$ for
  even $t$ and $x_{-1}(t + 1)$ for odd $t$), so these columns are one sequence in three guises and give no new
  periodicity to contradict masked Jen. The kit's eight-column renormalization goes further and stops after one step
  ([no certificate](no-finite-certificate.md)). The identities are derived by hand from the update of the center, not
  computed here.
- A front automaton for the ether ([the shift model](../../findings/period-two/shift-model.md), item 8). The top of
  a defect rises one cell per step only above a 0 of the background; following the top and the $w - 1$ cells below it
  exactly, with the cells below free, bounds the speed of the front by 0.22 at $w = 8$ and 0.18 at $w = 10$
  (`python -m computations.held_shift --front 8`, `--front 10`), where a stripe gives 0 and the vacuum 1. Defects on
  the ether do stall in every trial, so the bound is lost in the cells below the window, which a deterministic orbit
  does not fill freely. A certificate for the ether would need to carry the whole defect, or use a structure of the ether
  that was not found here. The kit's barriers in `Rule30ZeroBoundaryBarriers` already exclude, for the left half
  alone, a ranking that decreases along every surviving double step through a finite abstraction
  (`no_finite_abstract_ranking`, B1), through the width and windows at the wall and the edge (`no_local_ranking`, B2)
  or through a finite automaton read from the edge (`no_edge_dfa_ranking`, B6), which bears on the potential above.
  The front automaton is not such a ranking: it bounds the speed of a defect over a fixed background, so the barriers
  do not cover it, and it fails for the reason above.
