---
title: Rule 30 has no additive conservation law
category: structure
problems: [1, 2]
status: negative
kind: no-signal
---

# Rule 30 has no additive conservation law

**Question.** Is some sum over windows of each row, $S_t = \sum_x g(a_t(x), \dots, a_t(x + w - 1))$, conserved, drifting
linearly, or conserved modulo $p$? A conservation law would constrain the density, the subject of Problem 2.

**Method.** $S_t$ is linear in the $2^w$ values of $g$, so exact invariants are null spaces, taken modulo the functions
whose sum vanishes on every finite row (one representative per class: $g$ supported on the $2^{w-1}$ patterns starting
with 1). Full column rank over GF($p$) excludes every rational solution. Near-invariants minimize the variance of $S_t$
at unit variance of $g$, read against coin-flip rows and fitted on the earlier half of the orbit, scored on the later.

**Outcome.**

- On the single cell's orbit, no conserved, linearly drifting or modular invariant of window width up to 12 (nullity 0
  modulo 2, 3, 5, 7 and $2^{31} - 1$ at every width). Controls found: Rule 184 conserves its number of 1s, Rule 150
  its parity, and Rule 90 keeps its parity even from $t = 1$.
- Over all rows: the rational and GF(2) null spaces of the $k$-block count maps have dimension $2^{k-1} - 1$ for
  $k = 1$ to 6, all coboundaries, so no additive conservation law exists on block counts up to 6.
- No GF(2) conserved sum of window-5 monomials on cyclic rows of 31 or 32 cells, for one step or two.
- The best near-invariants sit at 0.5 to 0.6 of the coin-flip null, about the share of each row outside the regular
  left side, and fitted on the earlier half they rise about 20-fold on the later half: cancellations fitted to the
  sample, not laws.

**What it means.** Problem 2 cannot come from an additive invariant of this kind.

**Evidence.** Quoted from code that is not in this repository.
