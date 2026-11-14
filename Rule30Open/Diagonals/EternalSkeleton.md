---
title: In an eternal rule 30 history white left of a frame moving left, every left diagonal is purely periodic with period dividing 2^d and the past is a forward function of the present; every row converges to exactly one such history, its shadow, and the single cell is a row of none
category: diagonals
problems: [2]
status: proved
lean: Rule30Open.Diagonals.EternalSkeleton
headline: [eternal_periodic, eternal_past, eternal_agree, shadow_eternal, shadow_unique_eternal, seed_not_eternal]
kit: new
kit_modules: [Rule30FiniteDiagonals]
---

# In an eternal rule 30 history white left of a frame moving left, every left diagonal is purely periodic with period dividing 2^d and the past is a forward function of the present; every row converges to exactly one such history, its shadow, and the single cell is a row of none

Read a row white left of a cell from that cell rightward, so that coordinate $d$ is left diagonal $d$. One step of
rule 30, with the frame moved one cell left, is

$$\mathrm{leftStep}(R)_d = R_{d-2} \oplus (R_{d-1} \lor R_d), \qquad R_{-1} = R_{-2} = 0 .$$

Coordinate $d$ of the image reads coordinates $d-2, d-1, d$ only, so the map does not increase the 2-adic distance
$2^{-(\text{first difference})}$; unlike the right-edge map of [the seed's past](../../findings/frames/seed-past.md),
it is not injective. An *eternal orbit* is a family of rows $R_t$, $t \in \mathbb{Z}$, with
$R_{t+1} = \mathrm{leftStep}(R_t)$ for every integer $t$: a rule 30 history defined at all times, each row white left
of a frame that moves left one cell per step.

## Statement

- `Ld_leftStep`: for every configuration white left of `lo`, the kit's left diagonals
  $\mathrm{Ld}(d, t) = \mathrm{cell}_t(lo - t + d)$ are a forward orbit of $\mathrm{leftStep}$.
- `eternal_periodic`: in an eternal orbit, $R_{t + 2^d}(d) = R_t(d)$ for every $d$ and every integer $t$. Every
  diagonal is purely periodic on all of $\mathbb{Z}$, with period dividing $2^d$.
- `eternal_past`: $R_t(d) = \bigl(\mathrm{leftStep}^{2^d - 1}(R_{t+1})\bigr)(d)$. The past is a forward function of
  the present, coordinate by coordinate.
- `eternal_agree`, `eternal_unique_past`: two eternal orbits that agree at one time agree at every time.
  `leftStep_injective_on_eternal`: $\mathrm{leftStep}$ is injective on the set of rows of eternal orbits.
- `shadow_eternal`, `shadow_forward`, `shadow_unique_eternal`: for every row $x$ (no condition on it), the *shadow*
  $\sigma_t(x)_d = \bigl(\mathrm{leftStep}^{\tau}(x)\bigr)_d$, read at a forward time $\tau \ge 2^d - 1$ with
  $\tau \equiv t \pmod{2^d}$ (`shadowTime`), is an eternal orbit; it agrees with the forward orbit of $x$ on diagonal
  $d$ from time $2^d - 1$ on; and every eternal orbit that agrees with the forward orbit of $x$ on each diagonal from
  some time on is the shadow (`shadow_unique`).
- `eternal_edge`: if one row of an eternal orbit has a black cell at the frame, then at every time diagonals 0 and 1
  are black, diagonal 2 is white and diagonal 3 flips at every step.
- `seed_no_preimage`, `seed_not_eternal`: the single black cell has no preimage under $\mathrm{leftStep}$ with a black
  cell at the frame, and it is not a row of any eternal orbit.

## Argument

1. **The kit's uniform period needs no edge.** `Rule30FiniteDiagonals.left_recurrence_uniform_period` takes any array
   $b(i, n)$, $n \in \mathbb{N}$, with $b(0, n+1) = b(0, n)$, $b(1, n+1) = b(0, n) \lor b(1, n)$ and the step for
   $i \ge 2$, and gives $b(i, n + 2^i) = b(i, n)$ for $n \ge 2^i - 1$. These three hypotheses are exactly
   $b(\cdot, n+1) = \mathrm{leftStep}(b(\cdot, n))$.
2. **Pure periodicity.** In an eternal orbit, apply step 1 to $b(i, n) = R_{t - s + n}(i)$ with $s = 2^d - 1$, at
   $n = s$: $R_{t + 2^d}(d) = R_t(d)$. An eternal orbit always has a row $2^d - 1$ steps earlier, so the transient of
   the forward statement is gone.
3. **The past from the present.** $R_t(d) = R_{t + 2^d}(d)$, and $R_{t+2^d} = \mathrm{leftStep}^{2^d - 1}(R_{t+1})$.
   So $R_t$ is determined by $R_{t+1}$, and by induction in both directions one row determines the orbit. For two rows
   of eternal orbits with the same image, shift the second orbit in time so that the two rows sit at the same time and
   apply this.
4. **The shadow.** On the forward orbit of $x$, diagonal $d$ has period $2^d$ from time $2^d - 1$ (step 1 again), so
   reading it at any forward time $\tau \ge 2^d - 1$ in the class of $t$ modulo $2^d$ gives one value, and for $i \le
   d$ a time in the class of $t$ modulo $2^d$ is also one modulo $2^i$ (`iter_shadowTime`). So coordinates $d - 2$,
   $d - 1$, $d$ at time $t$ and coordinate $d$ at time $t + 1$ can all be read at one forward time, where the step
   holds: the shadow is eternal. If two eternal orbits agree with the forward orbit on diagonal $d$ from some time on,
   they agree at time $t + 2^d k$ for large $k$, hence at $t$ by pure periodicity.
5. **The edge.** Coordinate 0 has period 1 (step 2 with $d = 0$), so a black frame cell is black at every time. Then
   $R_{t+1}(1) = R_t(0) \lor R_t(1) = 1$, $R_{t+1}(2) = R_t(0) \oplus (R_t(1) \lor R_t(2)) = 1 \oplus 1 = 0$, and
   $R_{t+1}(3) = R_t(1) \oplus (R_t(2) \lor R_t(3)) = \lnot R_t(3)$. The single cell has $R(0) = 1$ and $R(1) = 0$,
   so it is no row of an eternal orbit, and $\mathrm{leftStep}(R)(1) = R(0) \lor R(1) = 1$ shows it has no preimage
   with a black frame cell.

## What it means

In the right-edge frame the single cell has exactly one past ([seed past](../../findings/frames/seed-past.md)); in the
left-edge frame it has none, and its forward orbit is a transient that converges to one eternal orbit, its shadow,
whose diagonals are the periodic parts of the single cell's diagonals extended to all integer times. The set of rows
of eternal orbits, its structure as a union of odometers, and the exhaustive check that its first 22 diagonals form
one cycle are in [the eternal shadow](../../findings/diagonals/eternal-shadow.md).

## In Lean

`Rule30Open/Diagonals/EternalSkeleton.lean`. The step is `leftStep`, its iterates `iter`, and the eternal orbits
`Eternal R` with `R : Int → Nat → Bool`. Pure periodicity is `left_recurrence_uniform_period` applied to the shifted
array; the shadow reads diagonal `d` at time `t` at the forward time
`shadowTime t d = t + 2^d (|t| + 1)`; the remaining theorems are rewriting with `omega` on the integer times.

## Relation to the kit

The kit proves eventual periodicity of the left diagonals of every configuration white left of a cell, with period
$2^d$ from time $2^d - 1$ (`Rule30FiniteDiagonals.Ld_uniform_period`), and in its equivalent forms that the right-edge
reading of every nonzero finite configuration has the 2-adic odometer as orbit closure
(`Rule30Equivalents.Odometer`). Neither has eternal orbits in the left frame, pure periodicity, the backward
uniqueness, the shadow, or the absence of a past for the single cell; a search of both parts of the kit for "eternal",
"odometer" and "omega" finds only the right-edge odometer, the omega-limit forms of Problem 1
(`Rule30Equivalents.Genericity`), and the rain rows of `Rule30EdgeStaircases` (`rain_row_eternal`), an edge patch at
the right edge that alternates for ever.
