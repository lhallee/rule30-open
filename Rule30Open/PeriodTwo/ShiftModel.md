---
title: The period-two condition is a full 2-shift on 2-adic halves
category: period-two
problems: [1]
status: proved
lean: Rule30Open.PeriodTwo.ShiftModel
headline: [heldOrbit_triangular, column_bijective, inK_graph, itinerary_bijective, held_held_two_to_one, heldNat_triangular, inK_periodic_rational, inK_periodic_not_finite, positive_integer_not_preperiodic]
kit: independent
kit_modules: [Rule30ZeroBoundary, Rule30Jen]
---

# The period-two condition is a full 2-shift on 2-adic halves

Let $H$ be the held map of [HeldColumn](HeldColumn.md), acting on bit sequences $u = (u_0, u_1, \dots)$ (2-adic
integers), with $H(u)_0 = u_1 \oplus u_0$ and $H(u)_{j+1} = u_{j+2} \oplus (u_{j+1} \lor u_j)$. This module shows that
the period-two condition, that bit 0 of $H^t(u)$ is 1 at every odd $t$, cuts out a set $K$ of sequences on which
$H^2$ is the one-sided full 2-shift. It says nothing about which points of $K$ have finitely many ones; that is the
open question.

## Statement

Write $c_n(u)$ for bit 0 of $H^n(u)$, the cell next to the column after $n$ steps.

- `heldOrbit_triangular`: if $u$ and $v$ agree below $j + t$, then $H^t(u)_j \oplus u_{j+t} = H^t(v)_j \oplus v_{j+t}$.
  So bit $j$ of $H^t(u)$ is $u_{j+t}$ plus a function of $u_0, \dots, u_{j+t-1}$. For $j = 0$ this is
  `column_triangular`: $c_t(u) = u_t \oplus g_t(u_0, \dots, u_{t-1})$.
- `column_bijective`: for every sequence $T$ there is exactly one $u$ with $c_n(u) = T_n$ for all $n$.
- `inK_graph`: let $K = \{u : c_n(u) = 1 \text{ for all odd } n\}$ (`InK`). For every choice $e$ of the even bits there
  is exactly one $u \in K$ with $u_{2s} = e_s$. So $K$ is the graph of a map from the even bits to the odd bits.
- `itinerary_bijective`: the itinerary $\beta_s(u) = c_{2s}(u)$ is a bijection from $K$ onto all bit sequences.
- `inK_held_held` and `itinerary_held_held`: $H^2$ maps $K$ into $K$ and $\beta_s(H^2 u) = \beta_{s+1}(u)$.
- `held_held_two_to_one`: each $w \in K$ has exactly two preimages in $K$ under $H^2$, one for each value of the first
  reading $\beta_0$.
- `heldNat_triangular`: on numbers, for $U \equiv V \pmod{2^t}$, the parity of $H^t(U)$ plus bit $t$ of $U$ is the same
  for $U$ and $V$.
- `eventually_periodic_of_column_periodic` and `inK_periodic_rational`: if the cell next to the column has a period in
  time, which holds for every $u \in K$ whose itinerary has a period $n$ (then the period is $2n$,
  `column_periodic_of_itinerary`), then $u$ is an eventually periodic sequence: a 2-adic rational.
- `inK_periodic_not_finite`: a point of $K$ whose itinerary has a period has no last 1.
- `inK_finite_not_preperiodic` and `positive_integer_not_preperiodic`: a point of $K$ with a last 1, and in
  particular a positive integer $U$ with $H^{2s+1}(U)$ odd for all $s$, has an itinerary that is not eventually
  periodic.

The sequence 0 is not in $K$, since $H(0) = 0$ reads 0 at $t = 1$; the module does not state this, so the
three theorems above are stated for points with a last 1 rather than for all points with finitely many ones.

So the itinerary is a bijection from $K$ onto $\{0, 1\}^{\mathbb N}$ that carries $H^2$ to the shift. It is
continuous in both directions, since $\beta_s$ depends on $u_0, \dots, u_{2s}$ only and $u_k$ on
$\beta_0, \dots, \beta_{\lfloor k/2 \rfloor}$ only, which makes $(K, H^2)$ conjugate to the one-sided full shift;
the module does not prove the continuity, which the kit has in its encoding as `Theta_dep` and
`Theta_inverse_dep`. Modulo $2^d$ the set $K$ has $2^{\lceil d/2 \rceil}$ residues, one for each choice of the even
bits below $d$; the module proves the graph statement for infinite sequences, from which this count follows, and the
kit proves the count in its encoding as `count_constrained`.

## Argument

1. **Triangularity.** Induct on $t$ for all $j$ at once. For $t = 0$ both sides are 0. For the step, bit $j$ of
   $H^{t+1}(u)$ is $H^t(u)_{j+1} \oplus (H^t(u)_j \lor H^t(u)_{j-1})$ (the OR term is absent at $j = 0$). If $u$ and
   $v$ agree below $j + t + 1$ then they agree below the indices that the inductive hypothesis needs for the three
   terms $H^t(\cdot)_{j+1}$, $H^t(\cdot)_j$ and $H^t(\cdot)_{j-1}$, namely $j + 1 + t$, $j + t$ and $j - 1 + t$. The
   hypothesis gives the same lower values for the two orbits at $j$ and $j - 1$, so the OR terms agree, and the term
   at $j + 1$ differs from $u_{j+1+t}$ by an amount that agrees. Adding $u_{j+t+1}$ gives the claim
   (`heldOrbit_triangular`).
2. **The column map is a bijection.** Two sequences with the same column reads agree bit by bit: bit $n$ of
   each is $c_n \oplus g_n(\text{lower bits})$, and the lower bits agree by induction (`column_injective`). Given
   target reads $T$, build $u$ one bit at a time: bit $k$ is $T_k \oplus c_k(p)$ for $p$ the prefix of $u$ below $k$,
   padded with zeros. By step 1, $c_k(u) \oplus u_k = c_k(p) \oplus 0$, so $c_k(u) = T_k$ (`column_exists`).
3. **The graph.** Two points of $K$ with the same even bits agree: at an odd $n$ the lower bits agree by induction and
   both columns read 1, so step 1 gives equal bit $n$ (`inK_unique_of_even`). For existence, build $u$ with bit $k$
   equal to $e_{k/2}$ for even $k$ and the complement of $c_k(p)$ for odd $k$, which makes $c_k(u) = 1$ at odd $k$
   (`inK_exists_of_even`).
4. **The itinerary.** Two points of $K$ with the same itinerary have the same column reads at all $n$ (the odd ones
   are 1), hence are equal (`itinerary_injective`). Given $\beta$, apply step 2 to the target that reads $\beta_{n/2}$
   at even $n$ and 1 at odd $n$ (`itinerary_exists`).
5. **The shift.** $H^n(H^2 u) = H^{n+2}(u)$, so $H^2$ maps $K$ to $K$ and shifts the itinerary. For $w \in K$ and
   $b \in \{0, 1\}$ the point $u_b \in K$ with itinerary $(b, \beta_0(w), \beta_1(w), \dots)$ has $H^2 u_b \in K$ with
   itinerary $\beta(w)$, so $H^2 u_b = w$ by step 4. Any preimage in $K$ has the itinerary of $u_0$ or $u_1$, so it is
   one of them (`held_held_two_to_one`).
6. **Numbers.** `heldNat_repeat_testBit` identifies the bits of $H^t(U)$ for a number $U$ with the orbit of its bit
   sequence, so step 1 gives `heldNat_triangular` through the bits of $U \bmod 2^t$.

7. **Periodic itineraries give rationals.** Let $Y_k(t)$ be bit $k$ of $H^t(u)$. Solving the definition of $H$ for the
   next column gives $Y_{k+2}(t) = Y_{k+1}(t+1) \oplus (Y_{k+1}(t) \lor Y_k(t))$ and $Y_1(t) = Y_0(t+1) \oplus Y_0(t)$
   (`heldOrbit_sideways`, `heldOrbit_one`). If $Y_0$ has period $q$, so has every $Y_k$
   (`heldOrbit_columns_periodic`). The pair of words $(Y_k, Y_{k+1})$ on one period takes at most $2^{2q}$ values and
   determines all later pairs, so two of the first $2^{2q} + 1$ pairs agree, at $m < n$, and then $Y_{m+i} = Y_{n+i}$
   for every $i$. Reading time 0 gives $u_{m+i} = u_{n+i}$ (`eventually_periodic_of_column_periodic`, with the kit's
   `Rule30Jen.pigeonhole`). For $u \in K$ with an itinerary of period $n$ the odd reads are 1 and the even reads
   repeat, so $Y_0$ has period $2n$.
8. **No finite support.** If $u_m = 1$ and $u_j = 0$ for $j > m$, then $H(u)_{m+1} = u_{m+2} \oplus (u_{m+1} \lor u_m) = 1$
   and $H(u)_j = 0$ for $j > m + 1$, so the last 1 moves to $m + 1$ (`held_topBit`) and to $m + k$ after $k$ steps
   (`heldOrbit_topBit`). A point $v$ of $K$ with an itinerary of period $n$ is fixed by $H^{2n}$: $H^{2n} v \in K$ has
   the same itinerary, and the itinerary is injective on $K$ (`heldOrbit_fixed_of_periodic`). A fixed point cannot move
   its last 1, so $v$ has none (`inK_periodic_not_finite`). If $u \in K$ has finitely many ones and a preperiodic
   itinerary, then $v = H^{2\,\mathrm{pre}}(u) \in K$ has finitely many ones and a periodic itinerary, a contradiction
   (`inK_finite_not_preperiodic`); a positive integer is such a point through its bits
   (`positive_integer_not_preperiodic`).

## In Lean

`column u n` is bit 0 of `heldOrbit u n`, `InK u` the condition, and `itinerary u s` is `column u (2 * s)`. `build c`
builds a sequence from a rule `c k prefix`, and `built c` is its limit; `build_prefix` says the prefix of length $m$ is
the first $m$ bits of the limit. No `sorry`, no `native_decide`, and no axioms beyond `propext`, `Classical.choice`
and `Quot.sound` (`Classical.choice` enters through the pigeonhole and `Nat.log2` lemmas).

## Relation to the kit

Most of this module is in the kit's `Rule30ZeroBoundary`, in another encoding: the zero-boundary left half `zrow`,
whose constraint holds column $-1$ black at the even steps where $K$ reads 1 at the odd steps. The translation
between the two encodings is not proved here. Theorem by theorem:

- `heldOrbit_triangular` and `column_triangular`: `tri_odd` and `tri_even`, the triangular form.
- `column_bijective`: `realization`, every column $-1$ sequence is realized by exactly one start, and the sideways
  recursion `heldOrbit_sideways` is `recon` with `history_eq_recon`.
- `inK_graph` and `itinerary_bijective`: `Theta_inX`, `Theta_free`, `Theta_unique`, `inX_iff` and `Theta_inj`, which
  make the free bits a bijection from the constrained starts onto all sequences.
- `inK_held_held` and `itinerary_held_held`: `two_step_shift`.
- `heldOrbit_topBit`: `zrow_edge`, the last black cell moves out one depth per step.
- `inK_periodic_not_finite`, `inK_finite_not_preperiodic` and `positive_integer_not_preperiodic`:
  `free_not_eventuallyPeriodic` and `col_not_eventually_periodic`, a finitely supported constrained start has free
  bits that are not eventually periodic.
- The count of residues: `count_constrained`, $2^{\lfloor W/2 \rfloor}$ constrained starts of width $W$.

This module proves these again on the held map of [HeldColumn](HeldColumn.md), over bit sequences with `Bool`
operations. Its additions are `heldNat_triangular` (the statement for numbers), `held_held_two_to_one` (the exact
2-to-1 count of $H^2$ on $K$) and `eventually_periodic_of_column_periodic` with `inK_periodic_rational` (a point of $K$
with a periodic itinerary is a 2-adic rational; the kit's `Rule30Jen.pigeonhole` is the finite step).
