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
the 2-adic theory of $T$ (Lagarias 1985; Bernstein 1994; Bernstein and Lagarias 1996; the cycle bounds of Steiner and of
Simons and de Weger; Tao 2019) say anything about a positive integer in $K$?

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
  is rational by the domain argument, with no closed form; the inverse conjugacy is a limit of nonaffine maps, whose
  bits are the dense polynomials of [the forced bits](forced-bits-dense.md). This is where the approach stops.
- **Cycle bounds from linear forms in logarithms.** They bound integer cycles of $T$. For $H$ there is nothing to bound:
  no point of $K$ with an eventually periodic itinerary is an integer (`positive_integer_not_preperiodic`), by the
  one-line argument that $H$ moves the last 1 of a finite point. The hard case for $H$ is an aperiodic itinerary, the
  analog of a divergent trajectory of $T$, which these tools do not treat for $T$ either.
- **Lagarias's periodicity conjecture.** For $H$ on all of $\mathbb Z_2$ it is false: the column of an integer $U$ is
  eventually periodic only for $U \in \{0, -1\}$ (item 6 of the finding). Only its restriction to $K$, conjecture (R),
  can hold, and the inclusion "eventually periodic itinerary implies rational" is already item 4 of the shift model.
- **Tao's density method.** Tao's work for $T$ is to show that the parity vector of a random integer is close to
  uniform for long enough (a 3-adic mixing estimate) and to pass from there to almost bounded values. For $H$ the
  first step is exact with no estimate: for $T < N$, exactly $2^{N - \lceil T/2 \rceil}$ integers below $2^N$ pass the
  odd steps up to $T$ (the count of `count_constrained` in the kit; `survivors_below` checks it for $N \le 12$). So
  for any $f(M) \to \infty$, all but a fraction $2^{-\lceil f(M)/2 \rceil}$ of the integers with $M$ bits fail by step
  $f(M)$, far below the step $2M$ of [the left half alone](../../findings/period-two/left-half-alone.md). A natural or
  logarithmic density statement says nothing beyond this: the integers in question, if any, lie among the
  $2^{(M-1)/2}$ that pass every step below $M$, a set of density $2^{-(M-1)/2}$ that density arguments do not see.
  The question is whether that thin set is empty, which is the kit's `Q01`.

**What it means.** The analogy between $H$ and the 3x+1 map is exact in the metric and fails in the algebra, and every
Collatz tool that reaches integers uses the algebra. What transfers gives nothing new about integers. A route through
this lens would need a substitute for affinity: an invariant of $H^n$ on classes that is finer than the similarity
and controls the vacuum tail. None is known; the forced bits are dense of full degree, so a low-degree substitute does
not exist for the first twelve of them.

**Evidence.** `python -m computations.held_similarity --max-n 12`, tested in `tests/test_held_similarity.py`.
