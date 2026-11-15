---
title: The held map is a similarity of ratio 2^n on each class modulo 2^n, and onto every residue
category: period-two
problems: [1]
status: proved
lean: Rule30Open.PeriodTwo.HeldClasses
headline: [heldNat_repeat_mod_iff, heldNat_repeat_onto, heldOrbit_agree_iff, heldNat_repeat_flip]
kit: refines
kit_modules: [Rule30ZeroBoundary]
---

# The held map is a similarity of ratio 2^n on each class modulo 2^n, and onto every residue

Let $H(U) = (U \gg 1) \oplus (U \lor (U \ll 1))$ be the held map `heldNat` of [HeldColumn](HeldColumn.md), on the
natural numbers. This module proves, with congruences in place of 2-adic distances, that $n$ steps of $H$ multiply
distances by exactly $2^n$ on each class modulo $2^n$ and map each such class onto every residue. This is the metric
half of the comparison with the 3x+1 map in
[the held map as a similarity](../../findings/period-two/held-similarity.md); the algebraic half, that no iterate is
affine on a class, is [HeldSimilarity](HeldSimilarity.md).

## Statement

- `heldNat_repeat_mod_iff`: if $U \equiv V \pmod{2^n}$ and $m \ge n$, then
  $H^n(U) \equiv H^n(V) \pmod{2^{m-n}}$ if and only if $U \equiv V \pmod{2^m}$.
- `heldNat_repeat_onto`: for every $a$, $W$ and $k$ there is $U \equiv a \pmod{2^n}$ with
  $H^n(U) \equiv W \pmod{2^k}$.
- `heldOrbit_agree_iff`: the same as the first statement on bit sequences: if $u$ and $v$ agree below $n$, the orbits
  after $n$ steps agree below $k$ exactly when $u$ and $v$ agree below $k + n$.
- `heldNat_repeat_flip`: flipping bit $k + n$ of $U$ keeps bits $0, \dots, k - 1$ of $H^n(U)$ and flips bit $k$.

In 2-adic terms, the first statement says $|H^n U - H^n V|_2 = 2^n |U - V|_2$ for $U \equiv V \pmod{2^n}$ (take the
largest $m$ with $U \equiv V \pmod{2^m}$). With the second it says that $H^n$ is a bijective similarity of ratio
$2^n$ from each class modulo $2^n$ onto $\mathbb Z_2$; that passage to the 2-adic integers, by compactness, is not
formalized.

## Argument

1. **Bits.** $x \equiv y \pmod{2^m}$ exactly when bits $0, \dots, m - 1$ agree (`mod_two_pow_eq_iff`), and bit $j$ of
   $H^n(U)$ is bit $j$ of the orbit of the bit sequence of $U$ (`heldNat_repeat_testBit` of [ShiftModel](ShiftModel.md)).
2. **Induction on $k$.** For $k = 0$ both sides of `heldOrbit_agree_iff` hold, the right one by hypothesis. Assume it
   for $k$. If either side holds for $k + 1$, then $u$ and $v$ agree below $k + n$, and `heldOrbit_triangular` at
   $(n, k)$ gives $H^n(u)_k \oplus u_{k+n} = H^n(v)_k \oplus v_{k+n}$. So bit $k$ of the orbits agrees exactly when
   bit $k + n$ of the sequences does, which is the step.
3. **Flip.** $U \oplus 2^{k+n}$ agrees with $U$ below $k + n$, so step 2 keeps bits below $k$, and the triangular
   identity at $(n, k)$ with $u_{k+n}$ flipped flips bit $k$.
4. **Onto.** By induction on $k$: start from $U = a$; if bit $k$ of $H^n(U)$ differs from bit $k$ of $W$, replace $U$
   by $U \oplus 2^{k+n}$, which keeps $U$ modulo $2^n$ and, by step 3, the lower bits of the image.

## In Lean

Iterates are `Nat.repeat heldNat n`. No `sorry`, no `native_decide`, and no axioms beyond `propext` and `Quot.sound`.

## Relation to the kit

The bit-level identity behind both statements is in the kit, in its encoding of the zero-boundary left half, as
`Rule30ZeroBoundary.zrow_aff` (flipping depth $k + t$ flips depth $k$ at time $t$ when the lower depths agree) and
`pivot`; the repository's own form is `heldOrbit_triangular`. This module refines them into the statements on
congruences of numbers, the exact similarity of ratio $2^n$ and the surjectivity onto every residue, which the kit
does not state.
