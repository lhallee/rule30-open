---
title: No iterate of the held map is affine on a residue class
category: period-two
problems: [1]
status: proved
lean: Rule30Open.PeriodTwo.HeldSimilarity
headline: [heldNat_not_affine, heldNat_repeat_split, edgeless_three_lt]
kit: new
kit_modules: [Rule30ZeroBoundary, Rule30Equivalents.TFunction, Rule30Equivalents.IntegerRows]
---

# No iterate of the held map is affine on a residue class

The 3x+1 map $T$ is affine on each class modulo $2^n$ after $n$ steps, which gives each periodic parity word an
explicit rational and the inverse conjugacy an explicit series. This module proves that the held map
$H(U) = (U \gg 1) \oplus (U \lor (U \ll 1))$ of [HeldColumn](HeldColumn.md) has no such property: for every $n \ge 1$
and every class $a + 2^k \mathbb Z$, the iterate $H^n$ agrees with no affine map on the class. The metric side of the
comparison, and what it means for the period-two question, is in
[the held map as a similarity](../../findings/period-two/held-similarity.md).

## Statement

Write $E(x) = x \oplus ((x \ll 1) \lor (x \ll 2))$ (`edgeless`), the held map far from cell 0.

- `heldNat_split`: if $A < 2^p$ and $q \ge p + 2$, then $H(2^q y + A) = 2^{q-1} E(y) + H(A)$ and $H(A) < 2^{p+1}$.
- `heldNat_repeat_split`: if $A < 2^p$ and $q \ge p + 2n$, then $H^n(2^q y + A) = 2^{q-n} E^n(y) + H^n(A)$ and
  $H^n(A) < 2^{p+n}$.
- `edgeless_top`: if the last 1 of $x$ is at bit $p$, the last 1 of $E(x)$ is at bit $p + 2$ and bit $p + 1$ of $E(x)$
  is 1.
- `edgeless_three_lt`: $E^n(3) < 3 E^n(1)$ for $n \ge 1$.
- `heldNat_not_affine`: for $n \ge 1$, $a < 2^k$ and $m = k + 2n + 3$,
  $H^n(a + 3 \cdot 2^m) - H^n(a) \ne 3\,(H^n(a + 2^m) - H^n(a))$ in $\mathbb Z$.

A map $U \mapsto \alpha U + c$ with $\alpha, c \in \mathbb Q_2$ on the class of $a$ modulo $2^k$ would give equality
in the last statement, since $a$, $a + 2^m$ and $a + 3 \cdot 2^m$ all lie in the class. So no iterate of $H$ is affine
on any class of the 2-adic integers; the step from the integer statement to the 2-adic one is this one line and is
not formalized.

## Argument

1. **Split.** Bit $j$ of $H(X)$ reads bits $j - 1$, $j$ and $j + 1$ of $X$. For $X = 2^q y + A$ and $j < q - 1$ these
   are bits of $A$, so bit $j$ is bit $j$ of $H(A)$; for $j \ge q - 1$ the bits of $A$ that it reads are 0 (they lie at
   $p$ or above), so bit $j$ is bit $j - q + 1$ of $E(y)$, and bit $j$ of $H(A)$ is 0 since $H(A) < 2^{p+1} \le
   2^{q-1}$. The two pieces have disjoint bits, so the OR is a sum (`Nat.testBit_two_pow_mul_add`).
2. **Iterate.** Each step lowers the exponent of the high piece by 1 and raises the bound on the low piece by 1, so
   the gap shrinks by 2 per step, and $q \ge p + 2n$ keeps it at least 2 through $n$ steps.
3. **Size.** If the last 1 of $x$ is at $p$, bit $p + 2$ of $E(x)$ is $x_{p+2} \oplus (x_{p+1} \lor x_p) = 1$, bit
   $p + 1$ is $x_{p+1} \oplus (x_p \lor x_{p-1}) = 1$, and higher bits are 0. So $E^n(1)$ has its last 1 at $2n$ and bit
   $2n - 1$ set, $E^n(1) \ge 3 \cdot 2^{2n-1}$ and $3 E^n(1) \ge 9 \cdot 2^{2n-1} > 2^{2n+2}$, while $E^n(3)$ has its
   last 1 at $2n + 1$, so $E^n(3) < 2^{2n+2}$.
4. **Conclusion.** With $A = a$, $p = k$, $q = m = k + 2n + 3$ and $y = 1, 3$, the differences are
   $2^{m-n} E^n(1)$ and $2^{m-n} E^n(3)$, and $E^n(3) \ne 3 E^n(1)$.

## In Lean

`edgeless` is $E$, `heldTopAt x p` says the last 1 of `x` is at bit `p`, and iterates are `Nat.repeat`, as in
`heldNat_repeat` of [HeldColumn](HeldColumn.md). No `sorry`, no `native_decide`, and no axioms beyond `propext` and
`Quot.sound`.

## Relation to the kit

The kit has the triangular form of the zero-boundary left half (`Rule30ZeroBoundary.zrow_aff`, `pivot`), which is the
metric half of the comparison with the 3x+1 map, and its backward transducer `back`. The map $E$ (`edgeless`) is the kit's
single-seed integer step: `Rule30Equivalents.TFunction.Phi`, defined here a second time as `tPhi` in
[LeftCutRank](../Complexity/LeftCutRank.md), and $E^n(1)$ is the kit's row `Rule30Equivalents.IntegerRows.a n`
(1, 7, 25, 111, 401, OEIS A110240), the rows of rule 30 from one cell; `edgeless_top` is the left edge of its light
cone. The kit has no statement about affinity of the held map on classes, so `heldNat_not_affine` is new.
