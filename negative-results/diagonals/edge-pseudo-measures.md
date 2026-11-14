---
title: Telescoping certificates of range k <= 6 on the left-edge frame: the best provable black count on diagonals 0..J-1 levels off near 3.9, 6.4, 8.7, 11.1, 24.2 and at least 26.49 for J up to 48 to 160 (computed, floating point), suggesting but not proving that no fixed range proves a positive black density; the optimal pseudo-measures reproduce the true diagonals to a depth that grows with k and then fade to white (ratio 0.618 for k = 1, rough fits 0.78 to 0.92 for k = 2..6)
category: diagonals
problems: [2]
status: negative
kind: barrier
evidence: [computations/edge_pseudo_measures.py]
---

# Telescoping certificates of range k <= 6 on the left-edge frame: the best provable black count on diagonals 0..J-1 levels off near 3.9, 6.4, 8.7, 11.1, 24.2 and at least 26.49 for J up to 48 to 160 (computed, floating point), suggesting but not proving that no fixed range proves a positive black density; the optimal pseudo-measures reproduce the true diagonals to a depth that grows with k and then fade to white (ratio 0.618 for k = 1, rough fits 0.78 to 0.92 for k = 2..6)

**Question.** In the left-edge frame the row is $R = (R_0, R_1, \dots)$ with $R_0 = 1$ and
$R'_d = R_{d-2} \oplus (R_{d-1} \lor R_d)$ ($R_{-1} = R_{-2} = 0$). The boundary rules out the white row, so a local
certificate might prove that black cells have positive density on diagonals $0, \dots, J-1$ uniformly in $J$, the way
the pair potential of [RowWhiteDensity](../../Rule30Open/Foundations/RowWhiteDensity.md) proves white density at least
$2/5$. Which bounds can a telescoping certificate of finite range prove?

## The linear program and its dual

A *certificate of range $k$* is a spatial potential $\psi_d$ on $k+1$ adjacent cells of $R$ (allowed to depend on the
diagonal $d$), a temporal potential $\phi_d$ on $k$ adjacent cells, and numbers $c_d$ with
$[R_d = 1] + \psi_d - \psi_{d+1} + \phi_d(R'[d, d+k)) - \phi_d(R[d, d+k)) \ge c_d$ for every word of $R$ on
$[d-2, d+k)$ allowed by the boundary. Summing over $d < J$ and averaging over a period of any periodic orbit, the
$\phi$ terms cancel and the $\psi$ terms telescope, so the time-averaged number of black cells on diagonals $0..J-1$ is
at least $\sum_d c_d$ minus boundary terms. By linear programming duality the best such bound is

$$B_k(J) = \min \sum_{d<J} \mu_d[R_d = 1]$$

over *range-$k$ pseudo-measures*: probability vectors $\mu_d$ on the words of $R$ on $[d-2, d+k)$, with the boundary
cells fixed, $\mu_d$ and $\mu_{d+1}$ agreeing on their overlap $[d-1, d+k)$, and the image word $R'[d, d+k)$ having
the same law as $R[d, d+k)$ under $\mu_d$. The empirical measure of every periodic orbit is one, so
$B_k(J)$ is a valid lower bound and is the best a range-$k$ certificate gives. $B_k(J)$ is nondecreasing in $J$
(restrict a pseudo-measure to fewer diagonals). The same program with the white color gives the white bound.

**Validation.** In the ordinary frame (one translation-invariant $\mu$, with stationarity) the program for white cells
returns exactly $0.4$ for every $k$ from 1 to 5, the bound the pair potential proves; `check_pair_potential` re-verifies
the pair inequality exactly over all 8 triples.

## What the program returns (computed, floating point, HiGHS)

| $k$ | largest $J$ | $B_k(J)$ for black | tail ratio of $\mu_d[R_d = 1]$ |
|---|---|---|---|
| 1 | 48 | 3.9227 | 0.618 (successive ratios, $d = 12..16$) |
| 2 | 96 | 6.3677 | about 0.78 |
| 3 | 128 | 8.7128 | about 0.83 |
| 4 | 160 | 11.0964 | about 0.88 |
| 5 | 160 | 24.1801 | about 0.90 |
| 6 | 128 | 26.4951 (still rising slowly) | about 0.92 |

The increments shrink as $J$ grows; for example $B_5(96) = 24.1691$, $B_5(128) = 24.1797$, $B_5(160) = 24.1801$
(increments $0.0106$ and $0.0004$), and $B_2(48) = 6.3676$, $B_2(96) = 6.3677$. For $k = 6$ the value was still
rising at $J = 128$. The tail ratio for $k = 1$ is the successive ratio $\mu_{d+1}[R_{d+1} = 1] / \mu_d[R_d = 1]$,
which equals $0.618034$ for $d = 12..16$ (`successive_ratios`). For $k \ge 2$ the tail ratios are least-squares fits of
$\log \mu_d[R_d = 1]$ over the diagonals where it lies between $10^{-6}$ and $0.03$ (`tail_ratio`); they are rough. For white cells the program grows linearly with
slope $0.4$ (for $k = 1$, $B(32) - B(24) = 3.201$): the $2/5$ white bound carries over to the left-edge frame, as it
must, and nothing better appears for $k \le 4$.

**The shape of the optimal pseudo-measure.** Up to some depth the optimum that HiGHS returns (optima need not be unique) has $\mu_d[R_d = 1]$ equal to the true density of
black cells on diagonal $d$ of the single cell's cycle ($1, 1, 0, 1/2, 1, 1/2, 1/2, 0, 1/2, 1, 1/2, 1/4, 3/4, 3/4,
\dots$, through depth 3, 5, 8, 10, 28, 28 for $k = 1, \dots, 6$ at the $J$ of the table, `matching_depth`).
Beyond that depth it mixes the true behavior with white and fades geometrically.

## Why it cannot reach exactly white (proved on paper)

**No range-$k$ pseudo-measure ($k \ge 1$) has $\mu_{J-1}$ equal to the all-white word.** Suppose $\mu_d$ is all white.
Then $\mu_{d-1}$ is white on $[d-2, d+k-1)$, its overlap with $\mu_d$. Stationarity at $d-1$ says $R'_{d-1}$ has the law
of $R_{d-1}$, which is white; and $R'_{d-1} = R_{d-3} \oplus (R_{d-2} \lor R_{d-1}) = R_{d-3}$ on that support, so
$R_{d-3}$ is white and $\mu_{d-1}$ is all white. By induction $\mu_2$ is all white, but its word contains $R_0 = 1$.
(`white_end_feasible` confirms the program is infeasible for $J \in \{3, 5, 9\}$, $k \in \{1, 2\}$.)

This is left permutivity read backwards: a white region deep in the frame forces white everywhere to its left, so a
pseudo-measure must carry black mass at every depth. But nothing in the local constraints keeps that mass from
shrinking by a constant factor per diagonal, and that is what the optimum does.

## Where it stops

The step that fails is the passage from "black mass at every depth" to "black mass bounded below at every depth": for
each $k \le 6$ and each $J$ computed, the best range-$k$ certificate proves no more than about 3.9, 6.4, 8.7, 11.1,
24.2 and (for $k = 6$, $J = 128$) 26.4951 black cells on diagonals $0..J-1$, while the single cell's cycle has about
$J/2$ black cells there (computed; compare the white fraction $0.5002$ of the settled words in
[SkeletonWhiteDensity](../../Rule30Open/Diagonals/SkeletonWhiteDensity.md)). The fitted decay ratio rises with $k$, so
wider windows push the fade deeper without removing it in the range computed.

**What is a computation and what is not.** The values are floating-point optima for the stated $(k, J)$, checked
against the actual cycle (the cycle's empirical measure passes the exact rational check `verify_pseudo_measure`, and
every LP value lies below its count, `tests/test_edge_pseudo_measures.py`). That $B_k(J)$ stays bounded as
$J \to \infty$ is supported by saturation and a geometric tail, not proved: a proof would need an explicit infinite
pseudo-measure with a geometric tail, verified exactly. Two-step updates and the right-edge frame were not run.

**Consequence.** A proof that black cells have positive density on the regular left side is not supported by a
fixed-range telescoping (discharging) argument of range $k \le 6$ in the computed range: for each such $k$ the bound
levels off for $J$ up to the stated values, though whether $B_k(J)$ stays bounded is open, and a small positive slope
(for $k = 6$, $B_6(128)/128 \approx 0.2$) is not ruled out. The trend suggests (heuristic) that no fixed range works
and that a proof needs an input
that is not locally consistent in this sense, such as the period being a power of two or the global structure of the
[eternal skeleton](../../Rule30Open/Diagonals/EternalSkeleton.md). In the ordinary frame [black density from row runs](../structure/black-density-from-row-runs.md) shows that every
count valid for all rows gives black cells density 0, because the white row is allowed; here the boundary $R_0 = 1$
rules out the white row (and, by the paper argument above, every pseudo-measure ending white), so that argument does not
apply, and the obstruction is instead the geometric fade. Compare the period-uniform barrier of
[depth-register density](depth-register-density.md), which reaches the same conclusion for the depth-direction register.

## Reproduce

`python computations/edge_pseudo_measures.py` (small $J$ and the ordinary-frame check);
`python computations/edge_pseudo_measures.py --table` prints $(k, J, B_k(J)$, matching depth, tail ratio$)$ for every
table row through `table_rows` (the rows with $J \ge 96$ take up to about a minute each);
`successive_ratios(48, 1, range(12, 17))` gives the $k = 1$ ratio.
