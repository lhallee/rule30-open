---
title: The 2-adic technology of the 3x+1 problem gives period two only its metric part, exactly and trivially; the cycle equation, Bernstein's series and Tao's density method have nothing to act on
category: period-two
problems: [1]
status: negative
kind: barrier
evidence: [computations/held_similarity.py]
---

# The 2-adic technology of the 3x+1 problem gives period two only its metric part, exactly and trivially; the cycle equation, Bernstein's series and Tao's density method have nothing to act on

**Question.** Period two reduces to the held map $H(U) = (U \gg 1) \oplus (U \lor (U \ll 1))$ and the set $K$ of 2-adic
$U$ with $H^t(U)$ odd at every odd $t$, on which $H^2$ is the full 2-shift ([the shift model](../../findings/period-two/shift-model.md)):
the same picture as the 3x+1 map $T$ on $\mathbb Z_2$, conjugate to the shift by its parity vectors. Do the tools of
the 2-adic theory of $T$ (J. C. Lagarias, "The 3x+1 problem and its generalizations", Amer. Math. Monthly 92 (1985);
D. J. Bernstein, "A non-iterative 2-adic statement of the 3N+1 conjecture", Proc. Amer. Math. Soc. 121 (1994);
D. J. Bernstein and J. C. Lagarias, "The 3x+1 conjugacy map", Canad. J. Math. 48 (1996); the cycle bounds of
R. P. Steiner (1977) and of J. Simons and B. de Weger, Acta Arith. 117 (2005); T. Tao, "Almost all orbits of the
Collatz map attain almost bounded values", Forum Math. Pi 10 (2022), arXiv 2019) say anything about a positive integer in $K$?

**What was done.** Each tool was matched with the property of $T$ it uses, and the property was proved or refuted for
$H$ ([the held map as a similarity](../../findings/period-two/held-similarity.md), proofs there).

**Outcome.**

- **Conjugacy, isometry, Haar measure.** These transfer exactly: the column map $Q$ is an isometric conjugacy of $H$
  to the shift, $H^n$ is a bijective similarity of ratio $2^n$ from each class modulo $2^n$ onto $\mathbb Z_2$, and $K$
  is the attractor of two similarities of ratio $1/4$. Each is a metric reading of triangularity, which the
  repository and the kit already have (`heldOrbit_triangular`, `column_bijective`; `Rule30ZeroBoundary.realization`,
  `zrow_aff`). Nothing about integers follows.
- **The cycle equation and Bernstein's series.** Both use that $T^n$ is affine on each class modulo $2^n$. $H^n$ is
  affine on no class, for any $n \ge 1$ (item 3 of the finding: on $a + 2^k\mathbb Z_2$ the points $a + 2^m$ and
  $a + 3 \cdot 2^m$ have images that differ from $H^n(a)$ by $2^{m-n}E^n(1)$ and $2^{m-n}E^n(3)$, and
  $E^n(3) < 2^{2n+2} < 3E^n(1)$). The fixed point of a periodic itinerary exists as the fixed point of a contraction and
  is rational by the domain argument, with no known closed form; the inverse conjugacy is a limit of nonaffine maps,
  and its bits are the dense polynomials of [the forced bits](forced-bits-dense.md). This is where the approach stops.
- **Cycle bounds from linear forms in logarithms.** They bound integer cycles of $T$. For $H$ there is nothing to bound:
  no point of $K$ with an eventually periodic itinerary is an integer. For a positive integer this is
  `positive_integer_not_preperiodic`, by the one-line argument that $H$ moves the last 1 of a finite point; $0$ and
  $-1$ are not in $K$ ($c_1 = 0$), and for $U < -1$, $H(U)$ is a positive integer (item 6 of the finding), so
  $H^2(U)$ would be a positive integer in $K$ with an eventually periodic itinerary. The hard case for $H$ is an aperiodic itinerary, the
  analog of a divergent trajectory of $T$, which these tools do not treat for $T$ either.
- **Lagarias's periodicity conjecture.** For $H$ on all of $\mathbb Z_2$ it is false: the column of an integer $U$ is
  eventually periodic only for $U \in \{0, -1\}$ (item 6 of the finding). Only its restriction to $K$, conjecture (R),
  can hold, and the inclusion "eventually periodic itinerary implies rational" is already item 4 of the shift model.
- **Tao's density method.** Tao's argument for $T$ has an exact 2-adic part (the 2-adic valuations along the
  trajectory of a random integer are close to independent geometric variables, as the parity vector of $T$ is uniform)
  and a hard 3-adic part (a fine-scale mixing estimate for the Syracuse random variables modulo powers of 3), from which
  he obtains almost bounded values in logarithmic density. For $H$ the 2-adic part is exact as well: for $T < N$,
  exactly $2^{N - \lceil T/2 \rceil}$ integers below $2^N$ pass the odd steps up to $T$. This is the residue count
  of item 1 of [the shift model](../../findings/period-two/shift-model.md) ($2^{\lceil d/2 \rceil}$ residues of $K$
  modulo $2^d$, by triangularity), the analog in this encoding of the kit's `count_constrained`, which counts in its
  own phase at the single time $W - 1$; `survivors_below` checks it for $N \le 9$ and $N = 12$. The 3-adic part has no
  counterpart, because $H$ has no multiplier. So for any $f(M) \to \infty$ with $f(M) \le M - 2$, exactly a fraction
  $2^{-\lceil f(M)/2 \rceil}$ of the integers with $M$ bits pass the odd steps up to $f(M)$, and all others fail by
  then, far below the step $2M$ of [the left half alone](../../findings/period-two/left-half-alone.md). A natural or
  logarithmic density statement says nothing beyond this: the integers in question, if any, lie among the
  $2^{\lfloor M/2 \rfloor}$ integers with $M$ bits that pass every odd step up to $M - 2$, a fraction
  $2^{1 - \lceil M/2 \rceil}$ of them, a set that density arguments do not see. (Up to step $M - 1$ the count is
  $2^{(M-1)/2}$ for odd $M$ and smaller for even $M$, for example 5 for $M = 8$ and 25 for $M = 12$, by
  `survivors_with_bits`.) The question is whether that thin set is empty, which is the kit's `Q01`.

**What it means.** The analogy between $H$ and the 3x+1 map is exact in the metric and fails in the algebra, and each of
the tools above that reaches integers uses the affine form (heuristically, this holds for the Collatz literature
beyond them as well). What transfers gives nothing new about integers. A route through
this lens would need a substitute for affinity: an invariant of $H^n$ on classes that is finer than the similarity
and controls the vacuum tail. None is known; the forced bits are dense of full degree, so a low-degree substitute does
not exist for the first twelve of them.

**Evidence.** `python -m computations.held_similarity --max-n 12`, tested in `tests/test_held_similarity.py`.
