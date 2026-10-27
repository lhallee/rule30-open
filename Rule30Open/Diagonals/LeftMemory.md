---
title: Left diagonals remember only behind a white diagonal
category: diagonals
problems: [1]
status: proved
lean: Rule30Open.Diagonals.LeftMemory
headline: [D_reset, D_periodic_of_black, D_period_dichotomy, D_period_doubles, D_two_white, D_three_flips]
kit: refines
kit_modules: [Rule30Diagonals]
---

# Left diagonals remember only behind a white diagonal

The left side of the single cell's pattern is regular: read along the diagonals parallel to its left edge, every
diagonal is eventually periodic. The periods grow, but rarely: Wolfram's notes record the first diagonals of period
2, 4, 8, 16 and 32 at depths 3, 8, 29, 400 and 87,867, and Rowland proved that the periods double. This module proves
exactly when a period can grow. A diagonal forgets everything at each black cell of the diagonal before it, so it can
carry information from the past, the center column's included, only behind a diagonal that is eventually all white,
and then its period doubles exactly when the diagonal two before has odd weight per period.

## Statement

Let $D_j(t) = a_t(j - t)$ be diagonal $j$, counted from the left edge $D_0$ (the kit's `Rule30Diagonals.D`). The rule
reads $D_{j+2}(t+1) = D_j(t) \oplus \bigl(D_{j+1}(t) \lor D_{j+2}(t)\bigr)$ (`Rule30Diagonals.D_step`).

- `D_reset`: if $D_{j+1}(t) = 1$, then $D_{j+2}(t+1) = \lnot D_j(t)$.
- `D_periodic_of_black`: if $D_j$ and $D_{j+1}$ have period $P$ from $T$ and $D_{j+1}(r) = 1$ for some $r \ge T$,
  then $D_{j+2}$ has period $P$ from $r + 1$.
- `D_period_dichotomy`: if $D_j$ and $D_{j+1}$ have period $P$ from $T$, either $D_{j+2}$ has period $P$ from some
  time on, or $D_{j+1}$ is white from $T$ on, $D_j$ has an odd number of black cells in each period, and
  $D_{j+2}(t + P) = \lnot D_{j+2}(t)$ for $t \ge T$.
- `D_period_doubles`: in that last case $D_{j+2}$ has period $2P$ and never period $P$.
- `D_two_white`, `D_three_flips`: $D_2$ is white from time 2 on, and $D_3$ flips at every step from time 2 on.

## Argument

1. **Reset and accumulate.** Where $D_{j+1}(t) = 1$ the OR is 1 and $D_{j+2}(t+1) = \lnot D_j(t)$, whatever
   $D_{j+2}(t)$ was (`D_reset`). Where $D_{j+1}(t) = 0$, $D_{j+2}(t+1) = D_j(t) \oplus D_{j+2}(t)$
   (`D_accumulate`).
2. **No memory behind a black cell** (`D_periodic_of_black`). At $r + 1$ and at $r + P + 1$ the reset gives the same
   value, $\lnot D_j(r) = \lnot D_j(r + P)$. From there, $D_{j+2}$ and its shift by $P$ obey the same recursion with
   the same inputs, so they agree from $r + 1$ on, by induction.
3. **A running XOR behind a white diagonal** (`D_shift_of_white`). If $D_{j+1}$ is white from $T$ on, step 1 gives
   $D_{j+2}(t + n) = D_{j+2}(t) \oplus \pi_t(n)$, where $\pi_t(n)$ is the parity of the black cells of $D_j$ at times
   $t, \dots, t + n - 1$. For a $P$-periodic $D_j$ the parity over one period does not depend on where the period
   starts (`windowParity_periodic`): the window drops one cell and adds the same value $P$ steps later.
4. **The dichotomy** (`D_period_dichotomy`). If $D_{j+1}$ has a black cell at some $r \ge T$, step 2 applies. If not,
   step 3 gives $D_{j+2}(t + P) = D_{j+2}(t) \oplus \pi$, with $\pi$ the parity over one period: period $P$ when
   $\pi = 0$, a flip every $P$ steps when $\pi = 1$.
5. **Doubling** (`D_period_doubles`). Two flips cancel, so the period is $2P$; and a period $P$ would make
   $D_{j+2}(t) = \lnot D_{j+2}(t)$.
6. **The first instance.** $D_0$ is black and $D_1$ is black from time 1 (`Rule30Diagonals.D_zero`, `D_one`), so the
   reset makes $D_2(t + 2) = \lnot D_0(t + 1) = 0$. Behind the white $D_2$, $D_3$ accumulates the black $D_1$: it flips
   at every step.

So the eventual period of $D_{j+2}$ can exceed that of $D_j$ and $D_{j+1}$ only right after an eventually white
diagonal, and only by doubling. Only then does a diagonal carry a bit of the pattern's history, the center column's
included.

## In Lean

`windowParity f t n` is the parity $\pi_t(n)$ of $f$ on the window. Every statement reduces to `D_step` and case
analysis on a few Boolean values; the inductions run over the time offset from $r + 1$ or $T$.

## Relation to the kit

The kit's
[`Rule30Diagonals`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/7d665044b904117af9e82328aeb90a30692b2b85/lean/Ruliology/CellularAutomata/Rule30Diagonals.lean)
proves that every left diagonal is eventually periodic with period dividing $2^j$ (`D_periodic`). This module explains
where the periods grow. Where the white diagonals actually fall below depth 100,000 is computed in
[the left records finding](../../findings/diagonals/left-records.md). Wolfram's depths are in
[A New Kind of Science, notes to page 871](https://wolframscience.com/nksonline/page-871c/); Rowland's proof is in
[Complex Systems 16(3), 2006](https://www.complex-systems.com/abstracts/v16_i03_a04/).
