---
title: Every row of the single cell's past is eventually periodic to the left
category: frames
problems: [1]
status: proved
lean: Rule30Open.Frames.SeedPast
headline: [phiF_phiInv, phiInv_phiF, past_unique, phiInv_evPer, rho_evPer, frame_step, past_evPer]
kit: refines
kit_modules: [Rule30Equivalents.Preimages, Rule30Equivalents.TFunctionCycles]
---

# Every row of the single cell's past is eventually periodic to the left

[The seed's past](../../findings/frames/seed-past.md) reads Rule 30 in a frame that moves one cell right per step,
where it is a bijection of the 2-adic integers, and finds that the single black cell has exactly one predecessor at
each depth, every one of them periodic far to the left. This module proves both facts in general: the uniqueness and
the eventual periodicity, for every depth.

## Statement

Read a row leftward from the frame: bit $j$ of $y$ is the cell $j$ places left of it. One step of Rule 30 is
$\varphi(y)_j = y_j \oplus (y_{j-1} \lor y_{j-2})$, white below bit 0 (`phiF`).

1. **The frame** (`frame_step`). For a row white right of cell $m$, the frame at time $t + 1$, read from cell
   $m + t + 1$, is $\varphi$ of the frame at time $t$, read from cell $m + t$.
2. **$\varphi$ is a bijection** (`phiF_phiInv`, `phiInv_phiF`), with the inverse $\psi$ computed bit by bit,
   $\psi(y)_j = y_j \oplus (\psi(y)_{j-1} \lor \psi(y)_{j-2})$ (`phiInv`).
3. **One past at each depth** (`past_unique`). The only sequence that $k$ steps of $\varphi$ take to the single cell is
   $\rho_k = \psi^k(1)$ (`rho`).
4. **Eventual periodicity** (`phiInv_evPer`, `rho_evPer`). If $y$ repeats with some period from some bit on, so does
   $\psi(y)$; hence every $\rho_k$ does.
5. **In the orbit of a row** (`past_evPer`). If a row is white right of cell $m$ and $k$ steps later its only black
   cell is $m + k$, then the row read leftward from $m$ is $\rho_k$, and it repeats with some period from some cell on.

## Argument

1. Bit $j$ of the new frame is the cell $m + t + 1 - j$ at time $t + 1$, which reads the cells $m + t - j$,
   $m + t + 1 - j$ and $m + t + 2 - j$ at time $t$, bits $j$, $j - 1$ and $j - 2$ of the old frame; the cells right of
   $m + t$ are white, since a row white right of $m$ stays white right of $m + t$ (`right_white`).
2. $\psi$ is a transducer whose state before bit $j$ is its last two outputs (`invState`). Composed either way with
   $\varphi$ it gives the identity, bit by bit (`invState_phiF` reads the state off $\varphi(y)$).
3. Induction on $k$: if $\varphi^{k+1}(y) = 1$ then $\varphi(y) = \rho_k$, so $y = \psi(\varphi(y)) = \rho_{k+1}$.
4. Let $y$ repeat with period $p$ from bit $N$. The state at the five bits $N, N + p, \dots, N + 4p$ takes one of four
   values, so two agree, at $N + ap$ and $N + bp$ (`pigeon`). The input repeats with period $(b - a)p$ from $N$, so the
   states, and with them the outputs, repeat with that period from $N + ap$ (`invState_shift`). Starting from the single
   cell, which repeats with period 1 from bit 1, induction gives every $\rho_k$.

## What it covers

This is the rationality of $\rho_k$, the first of the three facts of [the finding](../../findings/frames/seed-past.md).
The other two, that the periodic tail of $\rho_k$ dies on a ring in exactly $k$ steps and that the periods are
therefore unbounded, stay computed and argued on paper there. From the transducer, $\rho_{k+1}$ repeats with $b - a$
times the period of $\rho_k$, for some $b - a \le 4$ (`phiInv_evPer`). As the finding says, the
past exists whatever the center column does later, so it gives no constraint toward Problem 1 by itself; it is a fact
about the frame in which the problems are phrased.

## Relation to the kit

The kit's equivalent forms prove that a configuration white from some cell on has exactly two preimages, one white and
one black from that cell on
([`Preimages`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/equivalents/Rule30Equivalents/Preimages.lean),
`evol_one_eq_iff_of_eventually_white`), which is the uniqueness of each step of this past, and that every nonzero finite
configuration has unbounded cycle lengths modulo $2^n$ in the frame of its right edge
([`TFunctionCycles`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/equivalents/Rule30Equivalents/TFunctionCycles.lean),
`per_unbounded`). The eventual periodicity of the past is not there. The proof here uses only the definitions of
`Rule30Open.Foundations.Evolve`.

## Lean

`Rule30Open.Frames.SeedPast`: `phiF`, `invState`, `phiInv`, `phiF_phiInv`, `invState_phiF`, `phiInv_phiF`, `EvPer`,
`evPer_mul`, `invState_shift`, `pigeon`, `phiInv_evPer`, `seedBits`, `rho`, `phiIter`, `phiIter_rho`, `past_unique`,
`rho_evPer`, `frame`, `right_white`, `frame_step`, `frame_iterate` and `past_evPer`.
