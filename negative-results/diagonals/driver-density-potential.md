---
title: A potential over 27 row features certifies a black density of only 12/13 for the drivers the left half allows, even on the reachable graph to t = 60 it is fitted to, and the same weights need 17/13 on the edges from t = 60 to 100
category: diagonals
problems: [2]
status: negative
kind: no-signal
evidence: [computations/driver_density.py]
---

# A potential over 27 row features certifies a black density of only 12/13 for the drivers the left half allows, even on the reachable graph to t = 60 it is fitted to, and the same weights need 17/13 on the edges from t = 60 to 100

**Question.** The [driver density](../../findings/diagonals/driver-density.md) conjecture $S_B$ says that every driver
the left half allows has at most $\rho T + C$ black cells among $c(0), \ldots, c(T)$, with $\rho$ near $3/4$ by the
data. A proof by potential would give a function $\Phi$ of the state $s$ = (left half, $c(t)$) with
$c(t + 1) \le \rho + \Phi(s) - \Phi(s')$ on every edge $s \to s'$; summed along a driver, this bounds the count by
$\rho T + \Phi(\text{start}) - \min \Phi$. On a finite layered graph some $\Phi$ always exists (the prefix maxima), so
only a restricted $\Phi$ means anything. Is there one over a small basis of row features?

**What was done.** `fit_potential` takes $\Phi = \theta \cdot f(s)$ over 27 features: $c(t)$; $c(t)$ and cell $-1$; the
lengths of the first two alternating domains from the center; the black reach (one plus the alternating right end when
$c(t)$ is black and cell $-1$ white, zero otherwise); the number of leading cells $-1, -2, \ldots$ that agree with the
single cell's left half at the same time; the cells $-1$ to $-20$; and the number of black cells among $-21$ to $-40$.
A linear program (scipy, HiGHS) minimizes $\rho$ over every distinct edge of the reachable graph with $t < 60$, with
$|\theta_i| \le B$, and then evaluates the same $\theta$ on the edges with $60 \le t < 100$.

**Outcome.** For $B = 1$, 10 and 1,000 the least $\rho$ on $t < 60$ is $12/13 = 0.9231$, with additive constant 0.08
($B = 1$) or 0.85 ($B = 10$, 1,000), and the fitted weights need $\rho = 17/13 = 1.3077$ on $60 \le t < 100$, worse
than the trivial bound 1. The largest weights fall on $c(t)$, the black reach and cell $-1$. By duality the optimum is
a combination of 26 edges, at times 17 to 59 ($B = 1$) or 19 to 59, whose feature differences cancel and whose mean
count of black cells is $12/13$. The true slope on this range is about $0.72$ ($M(60) = 44$).

**What it means.** A fixed basis of local features does not see the cost of reaching a state with a long alternating
domain: inside a black run the black reach drops by one per step, which pays for each black cell, and nothing in the
basis records that the run had to be paid for earlier (a reading of the weights, not a computation). It is the
obstruction of [finite-state slopes](finite-state-slopes.md), where no finite automaton over the driver certifies a
black-run slope unless the admissible black runs are bounded. And a bounded potential cannot work at all if the black
reach $R_B(s)$ of the reachable states is unbounded: a run of $R_B(s)$ black cells from time $s$ forces
$2 \max |\Phi| \ge (1 - \rho) R_B(s)$; the windows from arbitrary reachable states in the
[finding](../../findings/diagonals/driver-density.md#the-maxima) show the same growth. A certificate for $S_B$ needs a
potential that grows with the reachable set, for example one that charges the white cells spent before a long domain to
the domain. With the true slope near 3/4, a certified $\rho \le 0.9$ would have been a signal for the basis; it does
not reach it, and the route stops here.

## Reproduce

```bash
python -m computations.driver_density potential --fit 60 --test 100 --bounds 1,10,1000   # about 6 min
```

The output gives the support of the dual solution (the edges with positive weight and their times).
