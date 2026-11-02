---
title: The single cell has exactly one past in Rule 30, and its tails die on their rings in exactly k steps
category: frames
problems: [1]
status: proved
lean: Rule30Open.Frames.SeedPastRing
headline: [seedRow_evolve, seed_past_iff, evolve_periodic, evolve_agree, tailRing_left, tailRing_periodic, rho_one, rho_tail_dies, seed_past_rings]
kit: refines
kit_modules: [Rule30Equivalents.Preimages, Rule30Predecessors]
---

# The single cell has exactly one past in Rule 30, and its tails die on their rings in exactly k steps

[SeedPast](SeedPast.md) and [SeedPastPeriods](SeedPastPeriods.md) prove the facts of
[the seed's past](../../findings/frames/seed-past.md) in the moving frame, on sequences of bits. This module states
them for Rule 30 itself, on rows indexed by the integers (`evolve`): the past exists and is unique among rows white
right of a cell, and the periodic tail of each row of the past, wrapped on a ring, dies under Rule 30 in exactly $k$
steps, passing through all black one step before.

## Statement

Write $\rho_k$ for the row $k$ steps before the single cell in the frame (`rho`), bit $j$ being the cell $j$ places
left of the frame.

1. **Exactly one past** (`seedRow_evolve`, `seed_past_iff`). Let $m$ be a cell and $k \ge 0$. A row white right of
   $m$ becomes, after $k$ steps of Rule 30, the single black cell at $m + k$ if and only if it is `seedRow k m`, the
   row whose cell $m - j$ is bit $j$ of $\rho_k$ for every $j \ge 0$.
2. **One step back is all black** (`rho_one`). $\rho_1$ is black at every bit: the black half-line, the 2-adic $-1$.
3. **The tail dies on its ring in exactly $k$ steps** (`rho_tail_dies`, `seed_past_rings`). Suppose $\rho_k$ repeats
   with period $p > 0$ from bit $N$. Let $c$ be the $p$-periodic row with $c(-j) = \rho_k(j)$ for $j \ge N$
   (`tailRing`, `tailRing_left`, `tailRing_periodic`): the period word wrapped on a ring of $p$ cells. Then Rule 30
   turns $c$ all white at step $k$, $c$ has a black cell at every step $t < k$, and for $k \ge 1$ it is all black at
   step $k - 1$. Every $\rho_k$ has such $N$ and $p$ ([SeedPast](SeedPast.md), `rho_evPer`).

## Argument

1. Read `seedRow k m` in the frame at cell $m$ (`frameRow`, `frame_frameRow`): it is $\rho_k$, so after $k$ steps the
   frame at cell $m + k$ reads $\varphi^k(\rho_k)$, the single cell (`frameRow_evolve`, `frame_iterate`), and the
   cells right of $m + k$ stay white (`right_white`). Conversely, [SeedPast](SeedPast.md) (`past_evPer`) shows that a
   row white right of $m$ that becomes the single cell at $m + k$ reads $\rho_k$ leftward from $m$; right of $m$ both
   rows are white.
2. $\varphi$ of the all-black sequence is $1 \oplus 0$ at bit 0, $1 \oplus 1$ at bit 1 and $1 \oplus (1 \lor 1)$ above,
   which is the single cell; since $\varphi$ is a bijection, $\rho_1 = \varphi^{-1}(1)$ is all black.
3. Two facts about Rule 30 on the integers: a $p$-periodic row stays $p$-periodic (`evolve_periodic`), and two rows
   that agree left of cell $a$ agree left of $a - t$ at time $t$ (`evolve_agree`). The ring row $c$ agrees with
   `frameRow` $\rho_k$ $0$ left of cell $-N$, so at time $t$ its cell $t - j$ is bit $j$ of $\varphi^t(\rho_k) =
   \rho_{k-t}$ for every $j \ge N + 2t$ (`tailRing_evolve`, `rho_iter`); by periodicity every cell of $c$ at time $t$
   equals one of these (`tailRing_cell`). At $t = k$ that bit belongs to the single cell above bit 0, so it is white;
   at $t < k$ some such bit of $\rho_{k-t}$ is black, since $\rho_{k-t}$ is not white far out
   ([SeedPastPeriods](SeedPastPeriods.md), `rho_not_evZero`); at $t = k - 1$ every such bit belongs to $\rho_1$, which
   is all black.

A $p$-periodic row of the integers is a configuration of the ring of $p$ cells, and Rule 30 acts on it as on that
ring, so statement 3 says that the period word of $\rho_k$, wrapped on its ring, dies in exactly $k$ steps. The frame
moves one cell per step while the ring row does not, which is the rotation in the finding's wording.

## What it covers

With [SeedPast](SeedPast.md), [SeedPastPeriods](SeedPastPeriods.md) and [SeedPastTable](SeedPastTable.md), the three
general facts of [the finding](../../findings/frames/seed-past.md) are proved for every $k$, in the frame and in Rule
30 itself. The past exists whatever the center column does later, so it gives no constraint toward Problem 1 by
itself; it is a structural fact about the frame in which the problems are phrased.

## Relation to the kit

The kit's equivalent forms prove that a configuration white from some cell on has exactly two preimages under one step,
one white and one black from that cell on
([`Preimages`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/equivalents/Rule30Equivalents/Preimages.lean),
`evol_one_eq_iff_of_eventually_white`), which is one step of the uniqueness here, and its core library counts the
predecessors of a configuration on a ring (`Rule30Predecessors`, the corrected Feynman theorem). The kit's current main
branch also reads rings in the moving frame and characterizes the rings that return to themselves (`Rule30RingOrbits`).
Neither the pinned kit nor its main branch has the $k$-step past of the single cell, its tails on rings, or their exact
death time. The proof here uses only the definitions of `Rule30Open.Foundations.Evolve` and the modules above.

## Lean

`Rule30Open.Frames.SeedPastRing`: `frameRow`, `frameRow_white`, `frameRow_of_le`, `frame_frameRow`, `frameRow_evolve`,
`seedRow`, `seedRow_evolve`, `seed_past_iff`, `evolve_periodic`, `evolve_periodic_mul`, `evolve_agree`, `tailRing`,
`tailRing_periodic`, `tailRing_left`, `tailRing_evolve`, `tailRing_cell`, `rho_one`, `rho_tail_dies` and
`seed_past_rings`.
