---
title: Condrey's proof for a constant center does not extend to an alternating center
category: period-two
problems: [1]
status: negative
kind: dead-end
evidence: [computations/alternating_horizon.py]
---

# Condrey's proof for a constant center does not extend to an alternating center

**Idea.** Condrey (2026, arXiv:2609.09431) proves that no nonzero finite row keeps a constant center, and Adler (2026)
formalizes its horizon $w + 2$ in Lean. The proof shows that for every right half $R$ the one left half that keeps the
center constant is an infinite pattern, so no finite row does. Excluding a center that alternates from some time on would follow if the same
three steps held for the word $1, 0, 1, \dots$. The paper itself calls the period-two exclusion open and notes only that
no bounded horizon law is to be expected.

**Where it stops.** The three steps, and what happens to each ([the numbers](../../findings/period-two/condrey-carryover.md)):

1. *Uniqueness of the left half given the right half and the center.* It holds for any center word, because Rule 30 is
   permutive in its left input (Condrey's Lemma 1, the kit's `Rule30ZeroBoundary.pivot`; for $1, 0, 1, \dots$ the kit's
   `Psi_unique`, [the white right half](../../findings/period-two/white-right-half.md)).
   Nothing is lost here.
2. *An explicit left half.* For the zero center, $x_{-1}(t) = x_1(t)$ and column 1 is an OR latch, so the odd cells
   of the left half are the prefix OR of $R$, the even cells mark the first 1 of $R$ when it lies in an even column, and
   beyond $R$ it is the stripe $1010\dots$; for the all-one center the OR in the center's update is 1 and the
   left half is the stripe whatever $R$ is. For the alternating center the center sees $x_1$ only at the times $t$ with
   $c(t) = 0$ (odd $t$ for $1, 0, 1, \dots$), and at the times with $c(t) = 1$, $x_1(t + 1) = \lnot(x_1(t) \lor x_2(t))$
   undoes the latch. The forced left half is then the forced bits of
   [the shift model](../../findings/period-two/shift-model.md) composed with $R \mapsto$ `u R` (column 1 at the times with
   $c(t) = 0$; the kit's `Psi_free`), and this composite, as a function of $R$, has a decision diagram in the order of the
   columns of $R$ of width 2 for the zero center and 105 at depth 20 for the alternating one (heuristic: growing by a
   factor of about 1.6 every two depths). This is the step that fails: there is no formula in $R$ to inspect, only the
   forced bits of the shift model, whose polynomials have full degree ([the forced bits](forced-bits-dense.md)).
3. *An infinite tail.* In the constant case every left half ends in the stripe, so it has infinitely many 1s. For the
   alternating word 2 to 3 percent of the right halves of at most 12 cells end in a periodic tail (period 7, 14 or 28) and
   the rest show no period to depth 1,500. For the white right half the white runs stay near $\log_2$ of the depth to
   depth $2^{20}$, as a coin-flip heuristic predicts ([the white right half](../../findings/period-two/white-right-half.md)).
   A finite row needs a tail of zeros: by the kit's `CQ01_iff_Psi`, the period-two statement for finite configurations
   holds exactly when $\Psi(R)$ has infinitely many black cells for every finitely supported $R$. An argument would
   have to say why no $R$ gives a left half with a tail of zeros, and nothing here says so.

The horizon does not help. Any finite bound $f(A)$ on how long a row of support radius $A$ keeps the center alternating,
valid for every $A$, is equivalent to the statement that no finite row alternates from some time on (the row at that
time has some radius and alternates forever from time 0), so a horizon law is no weaker than the finite-configuration
problem (the kit's CQ01, `CQ01_iff_no_finite_alternating`). The computed
horizon is $36$ at every $A$ from 19 to 26 against $A + 2 = 21$ to $28$ for a constant center.

**What it means.** Uniqueness is the only part of Condrey's mechanism that is not special to a constant column; the
latch that makes the left half explicit and the stripe that makes it infinite both come from the OR absorbing a constant
center. What a proof for period two must show is exact: by the kit's `CQ01_iff_Psi`, $\Psi(R)$ has infinitely many black
cells for every finitely supported $R$. A proof needs a structural fact about $\Psi_c(R)$ that has no analogue in
Condrey: either a rule for which right halves give a tail of zeros, or an invariant that the run of zeros of $\Psi_c(R)$
cannot exceed. Neither shows in the data: to depth $2^{20}$ for the white right half, and to depth 4,096 for every right
half of at most 14 cells.
