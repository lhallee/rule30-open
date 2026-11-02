---
title: One step of Rule 30 on a ring loses almost no information, less than Rule 90 does, so erased information gives no lower bound
category: complexity
problems: [3]
status: negative
kind: refuted
evidence: [computations/ring_images.py, tests/test_ring_images.py]
---

# One step of Rule 30 on a ring loses almost no information, less than Rule 90 does, so erased information gives no lower bound

**Idea.** Write the rule as $x'_i = x_{i-1} \oplus (x_i \lor x_{i+1})$ and measure what one step on a ring of $W$
cells erases, $\delta_W = W - \log_2 |F_W(\{0,1\}^W)|$. If $\delta_W \ge \varepsilon W$, a simulation that must restore
its tape (a catalytic or reversible one) would keep about $\varepsilon W$ bits of garbage per step, and over $N$ steps
on a ring wide enough for the center column (the kit's `FiniteRings`: $W = N + 1$ cells give the center up to time
$N$) the garbage would be quadratic, a restatement of the quadratic cost as an information cost. Rule 90, linear with a
small kernel, was expected to lose $O(1)$ bits and to separate.

**Outcome.** The picture is reversed.

- Rule 30 loses at most 0.678 bits per step (at $W = 3$), less than 0.088 bits for $13 \le W \le 400$, and
  $\delta_W \sim (0.8478)^W / (2 \ln 2) \to 0$: on a ring of $W$ cells it misses exactly $(p_W + 1)/2 - [3 \mid W]$
  rows, $p_W$ the power sums of the roots of $x^3 - x^2 - 2$ ([ring images](../../findings/structure/ring-images.md)).
  At $W = 24$ it reaches 16,617,680 of the 16,777,216 rows, and loses 0.0138 bits.
- Rule 90 loses 1 bit at odd $W$ and 2 bits at even $W$ (its kernel), and Rule 150 2 bits when $3 \mid W$. So the
  loss is larger for the linear rules, whose center columns take time polynomial in the digits of $n$.
- Summed over the computation, $N \delta_{N+1} \to 0$: on the ring that the center column up to time $N$ needs, all
  $N$ steps together erase at most 1.64 bits of counting information for every $2 \le N \le 79$, less than one bit
  for $13 \le N \le 79$, and 0.033 bits at $N = 40$, by the formula.

**Where it stops.** At the first step: $\delta_W / W \to 0$, and in fact $\delta_W \to 0$, so no lower bound on garbage
per step follows, and no measure of erased information through image sizes separates Rule 30 from Rule 90. The reason
is left permutivity: two rows with one image that agree on two adjacent cells are equal, so a row has at most four
preimages on any ring (three, by the kit's `Preimages.card_le_three`), and the rows with more than one form a set that
grows like $1.6956^W$, not $2^W$. On the line the kit proves the limit form: almost every configuration has exactly one
preimage (`Mixing.ae_existsUnique_preimage`). The count is an average over rows; the single cell's orbit may pass through
rows with two preimages, but each such step loses at most $\log_2 3$ bits, so this measure cannot reach a superlinear
total either.

**Reproduce.** `python -m computations.ring_images --max-width 24` prints the image sizes of Rules 30, 90 and 150 for
$3 \le W \le 24$ by enumeration, checks them against the formula, and prints the formula's loss at $W = 32, 48,
64$, its largest loss for $13 \le W \le 400$ and the summed loss $N \delta_{N+1}$ for $2 \le N \le 79$
([computations/ring_images.py](../../computations/ring_images.py)).
