---
title: Bounding the single cell's white runs J_k by how fast every 2-adic seed leaves a cycle of length 2^k gives J_k ≤ T_k + 2, exact for k ≤ 4, but the escape depth T_k = 14 and 103 at k = 5 and 6 already exceeds the single cell's 8 and 14 and, at k = 6, the period 64 itself
category: complexity
problems: [3]
status: negative
kind: dead-end
evidence: [computations/edge_periodic_points.py, tests/test_edge_periodic_points.py]
---

# Bounding the single cell's white runs J_k by how fast every 2-adic seed leaves a cycle of length 2^k gives J_k ≤ T_k + 2, exact for k ≤ 4, but the escape depth T_k = 14 and 103 at k = 5 and 6 already exceeds the single cell's 8 and 14 and, at k = 6, the period 64 itself

**Question.** [Right-edge cycles](../../findings/complexity/right-edge-cycles.md) conjectures $L_n / n$ unbounded,
equivalently $J_k = W(2^k) = o(2^k)$ along a subsequence. Section 7 of [the routes](right-edge-cycle-routes.md) shows
that an argument valid for every 2-adic seed fails, because $\pm 1/3$ have cycles of length 2 at every level.
Non-Archimedean dynamics (Klimov and Shamir's cycle lifting, Anashin's tree of cycles of a measure-preserving 1-Lipschitz
map) suggests the next try: remove the periodic seeds and bound, uniformly over the rest, how many levels a seed can stay
in a cycle of length $2^k$ after it separates from them. If that depth $T_k$ were $o(2^k)$, the single cell would
satisfy the conjecture.

**What was done.** [Edge periodic points](../../findings/frames/edge-periodic-points.md) builds the finite graph whose
infinite walks are the 2-adic points of period dividing $2^k$, shows for $k \le 6$ that only $\pm 1/3$ (with their
multiples by powers of 2, and 0) are periodic, and computes the exact escape depth $T_k$: every odd seed $y \ne \pm
1/3$ that agrees with one of them to exactly $m$ bits has a cycle longer than $2^k$ modulo $2^n$ for every $n \ge m +
T_k + 2$, and this is sharp. For the seed 1, $m = 2$, so $J_k \le T_k + 2$.

**Outcome** (exact for $k \le 6$).

| $k$ | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| $T_k$ | 0 | 1 | 3 | 4 | 14 | 103 |
| $T_k + 2$ | 2 | 3 | 5 | 6 | 16 | 105 |
| $J_k$ | 2 | 3 | 5 | 6 | 8 | 14 |
| $T_k / 2^k$ | 0 | 0.25 | 0.375 | 0.25 | 0.44 | 1.61 |

The bound is exact for $k \le 4$: there the single cell stays in its short cycles as long as any seed can. From $k = 5$
it is loose, and at $k = 6$ some seed stays in a cycle of length 64 for 103 levels past its separation from the rain
pair, more than the period.

**Where it stops.** The route needs $T_k = o(2^k)$, a statement about every seed at once. The table does not refute it
asymptotically, since six values decide nothing about a limit; but nothing in the T-function structure pushes $T_k$
below $2^k$, the computed ratio grows from $k = 4$ to $k = 6$, and a seed-uniform depth is blind to what separates the
single cell: at $k = 6$ the worst seed keeps seven times as many diagonals periodic as the single cell does. What
separates the single cell is the light cone of a finite seed and the product term of the gate, as section 7 of the
routes says; $T_k$ uses neither, beyond excluding the two periodic seeds. A version of the route that could still work
replaces the supremum over all seeds by one over the seeds the single cell's row can look like at the right edge, which
is the stall analysis of the finding again.

**What it means.** T-function theory gives the global picture of the right-edge map cleanly (the cycle tree is the walk
graph, the periodic points are the rain pair for every period up to 64, and the escape from a periodic orbit is
uniform and computable), but its natural quantitative statement bounds the single cell only by the worst seed, and the
worst seed escapes much more slowly than the single cell.

## Reproduce

```
python -m computations.edge_periodic_points --k-max 6    # T_k and J_k, k <= 6: about 5 s
```
