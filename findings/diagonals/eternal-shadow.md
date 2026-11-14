---
title: The eternal rows of rule 30 in the left-edge frame form a compact set on which the step is an isometry and every orbit closure is a finite cycle or a 2-adic odometer; every row white left of a black cell converges to exactly one eternal orbit, its shadow, and for the first 22 diagonals all rows share the single cell's cycle
category: diagonals
problems: [2]
status: paper
formalization: partial
evidence: [computations/eternal_skeleton.py]
---

# The eternal rows of rule 30 in the left-edge frame form a compact set on which the step is an isometry and every orbit closure is a finite cycle or a 2-adic odometer; every row white left of a black cell converges to exactly one eternal orbit, its shadow, and for the first 22 diagonals all rows share the single cell's cycle

Read a row white left of a black cell from that cell rightward: coordinate $d$ is left diagonal $d$, and
$X = \{R \in \{0,1\}^{\mathbb{N}} : R_0 = 1\}$ is the set of such rows. Rule 30 with the frame moved one cell left is
$G(R)_d = R_{d-2} \oplus (R_{d-1} \lor R_d)$, $R_{-1} = R_{-2} = 0$ (`leftStep` of
[EternalSkeleton](../../Rule30Open/Diagonals/EternalSkeleton.md)); $G(X) \subseteq X$, and with the metric
$\mathrm{dist}(R, R') = 2^{-\min\{d : R_d \ne R'_d\}}$, $G$ is 1-Lipschitz, since coordinate $d$ of $G(R)$ reads
coordinates $d-2, d-1, d$. On the first $n$ coordinates $G$ is a map $G_n$ of the $2^{n-1}$ states with a black frame
cell. In the right-edge frame the step is a bijective isometry and the single cell has one past and an odometer as
orbit closure ([seed past](../frames/seed-past.md), the kit's `Rule30Equivalents.Odometer`). In the left-edge frame
the step is not injective and the single cell has no past (`seed_not_eternal`); this entry says what replaces both.

## The limit set (paper, using the Lean lemmas of EternalSkeleton)

Let $\Lambda = \bigcap_{k \ge 0} G^k(X)$ and $\Lambda_n$ the eventual image of $G_n$.

1. **$\Lambda$ is the set of rows of eternal orbits.** A row of an eternal orbit in $X$ is in every $G^k(X)$. Conversely
   $G^k(X)$ is a decreasing sequence of nonempty compact sets, so for $R \in \Lambda$ the compact sets
   $G^{-1}(R) \cap G^k(X)$ are nonempty and decreasing, and a point of their intersection is a preimage of $R$ in
   $\Lambda$. Repeating gives a backward orbit in $\Lambda$, so $G(\Lambda) = \Lambda$.
2. **$G$ is an isometry of $\Lambda$.** By `eternal_past`, $R_d = (G^{2^d - 1}(G R))_d$ for $R \in \Lambda$; the right
   side reads only coordinates $\le d$ of $GR$. So $GR$ and $GR'$ agree below $n$ exactly when $R$ and $R'$ do, and
   $G$ is a bijective isometry of $\Lambda$ (`leftStep_injective_on_eternal` for the injectivity alone). Its inverse
   is continuous, given coordinate by coordinate by forward iterates: $G^{-1}(R)_d = (G^{2^d - 1} R)_d$.
3. **Finite levels.** The projection of $\Lambda$ to the first $n$ coordinates is $\Lambda_n$ (a decreasing
   intersection of compact sets commutes with a continuous projection, and the projection of $G^k(X)$ is
   $G_n^k$ of the states). $\Lambda_n$ is the union of the cycles of $G_n$; by `eternal_periodic` every cycle length
   is a power of two dividing $2^{n-1}$.
4. **Orbit closures.** For $R \in \Lambda$ let $C_n(R)$ be the cycle of $G_n$ through its first $n$ coordinates. The
   orbit of $R$ meets every point of $C_n(R)$, so the orbit closure of $R$ is
   $\{R' : R'_{<n} \in C_n(R) \text{ for all } n\}$, the inverse limit of the cycles $C_n(R)$, and every point of it has
   the same cycles: **every orbit closure in $\Lambda$ is minimal.** Its lengths $|C_n(R)|$ are powers of two, each
   dividing the next. If they are bounded the orbit closure is one finite cycle. If not, put
   $\psi(\alpha)_d = (G^{\alpha \bmod |C_{d+1}(R)|} R)_d$ for $\alpha \in \mathbb{Z}_2$: it is well defined, a
   homeomorphism onto the orbit closure, and $\psi(\alpha + 1) = G\,\psi(\alpha)$. **So every infinite orbit closure
   in $\Lambda$ is the 2-adic odometer**, uniquely ergodic, and under its invariant measure the probability that
   diagonal $d$ is black is the number of black cells of diagonal $d$ per period divided by the period.
5. **Measures and entropy.** An invariant probability measure $\mu$ of $G$ on $X$ has $\mu(G^k X) \ge
   \mu(G^{-k} G^k X) = 1$, so it lives on $\Lambda$, where it is a mixture of the Haar measures of the orbit closures.
   A 1-Lipschitz map has topological entropy 0 (its Bowen balls do not shrink with time).

## The shadow (proved in Lean)

**Every row $x \in X$ converges to exactly one eternal orbit** (`shadow_eternal`, `shadow_forward`,
`shadow_unique_eternal` of [EternalSkeleton](../../Rule30Open/Diagonals/EternalSkeleton.md); the argument in the
metric language of this entry follows). Put
$S_t(d) = (G^{t + 2^d m} x)_d$ for $t \in \mathbb{Z}$ and any $m \ge 0$ with $t + 2^d m \ge 2^d - 1$. By the kit's
uniform period (`Rule30FiniteDiagonals.Ld_uniform_period`; `Ld_leftStep` identifies its diagonals with $G$), coordinate
$d$ of the forward orbit of $x$ has period $2^d$ from time $2^d - 1$, so $S_t(d)$ does not depend on $m$. Coordinate
$d$ of $S_{t+1}$ and coordinates $d-2, d-1, d$ of $S_t$ can be read at one common time $t + 2^d m$, so
$S_{t+1} = G(S_t)$ and $(S_t)$ is an eternal orbit. $G^t x$ and $S_t$ agree on every $d$ with $t \ge 2^d - 1$, so
$\mathrm{dist}(G^t x, S_t) \to 0$. If a second eternal orbit $S'$ had the same property,
$\mathrm{dist}(S_t, S'_t) \le \mathrm{dist}(S_t, G^t x) + \mathrm{dist}(G^t x, S'_t) \to 0$, while
$\mathrm{dist}(S_t, S'_t)$ is constant in $t$ by the isometry: $S = S'$.

The **shadow** $\sigma(x) = S_0$, $\sigma(x)_d = (G^{2^d} x)_d$, is a 1-Lipschitz retraction of $X$ onto $\Lambda$ with
$\sigma \circ G = G \circ \sigma$. The omega-limit set of $x$ is the orbit closure of $\sigma(x)$: a finite cycle or an
odometer by item 4. On each diagonal the forward orbit of $x$ equals its shadow from the onset of that diagonal on,
and the onset is the first time after which they agree for ever; so a statement about the settled region of $x$ is a
statement about one point of $\Lambda$.

**The eternal skeleton of the single cell** is the eternal orbit $S$ through $\sigma(\delta)$, $\delta = (1, 0, 0,
\dots)$: diagonal $d$ of $S$ is the periodic part of the single cell's diagonal $d$, extended to all of $\mathbb{Z}$
in its own phase. Its orbit closure $\Omega = \omega(\delta)$ is the odometer exactly when the single cell's left
periods are unbounded, which Nersissian (2026, in [the literature](../../literature/rule-30.md)) states and the kit's
main branch proves (`Rule30LeftUnbounded`, not in the pinned kit); unconditionally it is a minimal, equicontinuous,
uniquely ergodic set. $\Omega$ holds uncountably many eternal orbits, $\psi(\alpha)$ for $\alpha \in \mathbb{Z}_2$,
two of them time shifts of each other only when $\alpha - \beta \in \mathbb{Z}$; on each finite set of depths they
all agree with $S$ up to a time shift. $S$ is singled out in $\Omega$ only as the shadow of the single cell.

## How many eternal orbits (computed to 22 diagonals; beyond, from the skeleton tree)

`eternal_skeleton` computes $\Lambda_n$ exhaustively, iterating $G_n$ on all $2^{n-1}$ states until the image stops
shrinking, and its cycles:

| $n$ | 2, 3 | 4 to 8 | 9 to 22 |
|---|---:|---:|---:|
| $|\Lambda_n|$ | 1 | 2 | 4 |
| cycles of $G_n$ on $\Lambda_n$ | one | one | one |

**For $n \le 22$, $\Lambda_n$ is one cycle, the single cell's**: every row white left of a black cell ends, on its
first 22 diagonals, in the single cell's cycle, and all eternal orbits agree on depths $0$ to $21$ up to a time shift.
The number of steps after which $G_n^k$ of every state lies in $\Lambda_n$ reproduces the largest onsets $M_j$ of
[seed-uniform onsets](seed-uniform-onsets.md), $\max_{j < n} M_j$ (29 at $n = 22$), an independent check of both.

Past this range the cycles of $\Lambda_n$ are the nodes at depth $n - 1$ of the tree of
[SkeletonTree](../../Rule30Open/Diagonals/SkeletonTree.md): by [DrivenSkeleton](../../Rule30Open/Diagonals/DrivenSkeleton.md)
every row settles to the single cell's pairs up to a time shift as long as each white diagonal doubles the period, and
`branch_realized`, `branch_not_shift` give a second class behind the white diagonal 53,207, the first that does not
double. So, by those modules, $\Lambda_n$ is one cycle for $n \le 53{,}208$ and has two cycles at $n = 53{,}209$;
the eternal orbits with a black frame cell fall into at least two orbit closures, and into uncountably many if every
branch of the tree meets infinitely many white diagonals whose complement class is not a time shift (not known).

## What this does and does not reach

$\Lambda$ is the regular part of the left side made exact: on it the dynamics is a translation of $\mathbb{Z}_2$ (or a
finite cycle), every orbit is recurrent, all frequencies of finite patterns of diagonals exist and are uniform, and
entropy is zero. The center column $c(t) = (G^t \delta)_t$ reads the moving coordinate $d = t$ of the single cell's
own orbit, and the onset front reaches only about $0.75 t$ by time $t$ ([onset edge](onset-edge.md), computed to depth
200,000), so the center column lies in the transient, where the orbit and its shadow differ. The same holds for the
moving coordinate of $S$: $S_t(t)$ reads diagonal $t$ of an odometer point, about which item 4 says only that it is
periodic with a period that may grow with $t$. Nothing here is a statement about the density of the center column. The
density of black cells along a ray $d = \lfloor \beta t \rfloor$ with $\beta < 0.75$ in the settled region is the
density along that ray in $S$, which item 4 does not determine either: it averages over a window of $1/\beta$ times on
each diagonal, not over a period.

## Reproduce

```bash
python -m computations.eternal_skeleton --nmax 22   # the table, about 2 s
```

`tests/test_eternal_skeleton.py` checks $G_n$ against a direct rule 30 run of random rows, $\Lambda_n$ against a
brute-force search for periodic points for $n \le 8$, that the cycle lengths are powers of two, and the settling steps
against $M_j$ of seed-uniform onsets.
