---
title: Probabilistic checking verifies the center cell cheaply, as it does every computation, and does not compute it
category: complexity
problems: [3, 1, 2]
status: negative
kind: barrier
---

# Probabilistic checking verifies the center cell cheaply, as it does every computation, and does not compute it

**Question.** Probabilistically checkable proofs, interactive proofs and property testers check a claim by reading a
few random places of a long certificate, or by talking to a prover. Can such a checker settle a prize problem, or give
a statistical certificate that tightens into a proof?

**What checking gives, for the center cell as for any computation.**

- **Proofs checked in polylogarithmic time.** Babai, Fortnow, Levin and Szegedy (1991) turn every computation of $T$
  steps into a proof of length $T^{1 + \varepsilon}$ that a randomized verifier checks in time polylogarithmic in $T$,
  reading a few places. Simulation computes $c(n)$ in $T = O(n^2)$ steps, so a claim "$c(n) = b$" has a proof that is
  checked in time polylogarithmic in $n$. Nothing about Rule 30 enters: the proof is the simulation, encoded so that
  errors spread, and producing it costs at least the simulation.
- **Interactive proofs.** Goldwasser, Kalai and Rothblum (2008) let a verifier check a circuit of size $S$ and depth
  $d$ in time about $d \cdot \mathrm{polylog}\, S$ against an efficient prover. The circuit that simulates Rule 30 has
  depth $n$, one layer per step, so the verifier spends about $n$ steps. A circuit for $c(n)$ of polylogarithmic depth
  would be a parallel shortcut, and it is not known whether predicting Rule 30 is that easy or as hard as any
  polynomial-time computation (Rule 110 is the latter; see [the literature](../../literature/complexity.md)).
- **Testers.** A property tester decides with few samples whether the first $N$ cells are close to periodic or to
  balanced. Each sample costs a simulation, and the answer concerns the first $N$ cells, with a confidence, never the
  limit that Problems 1 and 2 ask about.

**Where it stops.** Problem 3 asks what computing $c(n)$ costs. Checking a claimed value is cheap for every
computation in exponential time, by the results above, so the cost of checking says nothing about the cost of
computing, which is the whole question; the two separate exactly where certificates are long. Problems 1 and 2 are
statements about the limit of one sequence, and a checker certifies finite prefixes. A statistical certificate of the
first $N$ cells, however strong, is the kind of evidence the [randomness tests](../statistics/randomness-tests.md)
already give: density 0.500169 over $2^{22}$ cells is consistent with Problem 2 and does not imply it.

**What a proof of Problem 3 would give.** The weakest version of Problem 3 bounds machines, which may not use advice.
A circuit version, that no circuit of size $n^{\varepsilon}$ computes $c$ on the inputs below $n$ for large $n$, would
give a language in exponential time that needs circuits of size $2^{\varepsilon m}$ on inputs of $m$ bits, and so
$\mathrm{P} = \mathrm{BPP}$ by Impagliazzo and Wigderson (1997): every randomized polynomial-time algorithm could be
derandomized. Explicit lower bounds of that strength are open for every problem in exponential time, which is one more
measure of [how far the barrier entry's affirmative answer lies](problem-three-barrier.md). For a random configuration in
place of the single cell, the kit's equivalent forms prove the counting bound in Lean: almost surely, for all large $k$,
no circuit of $2^k / (8k)$ gates computes $c(t)$ from the digits of $t < 2^k$
([`Circuits`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/equivalents/Rule30Equivalents/Circuits.lean): `ae_circuit_lower_bound_trace`).

**What it means.** Randomized verification, in any of its forms, certifies values and finite prefixes and leaves the
prize questions where they were. A route through it would need a certificate for $c(n)$ much shorter than the
simulation, which is the shortcut Problem 3 denies ([the hardness hypotheses](hardness-hypotheses.md), item 2).
