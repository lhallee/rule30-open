---
title: A seed-uniform induction on the onsets of the left diagonals stops at slope 2; the later row is a seed whose settled prefix leaves the rest free, the fresh-seed subadditivity fails at one diagonal, and the single cell is the worst seed up to a delay of 8 at every depth to 76 but not at depth 139
category: diagonals
problems: [2]
status: negative
kind: dead-end
evidence: [computations/seed_onsets.py]
---

# A seed-uniform induction on the onsets of the left diagonals stops at slope 2; the later row is a seed whose settled prefix leaves the rest free, the fresh-seed subadditivity fails at one diagonal, and the single cell is the worst seed up to a delay of 8 at every depth to 76 but not at depth 139

**Question.** Over all rows white left of a black cell (seeds), the left diagonal $D_j$ settles at an onset $T_j$
and the latest onset is $M_j$ ([seed-uniform onsets](../../findings/diagonals/seed-uniform-onsets.md)). The row of a
seed at any later time is again a seed, so a bound on $M_j$ is a natural induction hypothesis: a bound
$T_j \le \lceil 3j/2 \rceil + c$ for every seed would give [SettledSlope](../../Rule30Open/Diagonals/SettledSlope.md)
its hypothesis for the single cell. Four ways to make the induction step were tested. Write
$S_j = \max(T_{j-1}, T_j)$ for the pair onset and $M'_j = \max(M_{j-1}, M_j)$ for its maximum.

## Route 1: the later row, with the settled prefix kept and the rest free

**The step.** For a seed $x$ and $n < d$, the row $v$ of $x$ at time $S_n(x)$ is a seed with $T_d(x) = S_n(x) +
T_d(v)$, and its diagonals $0, \dots, n$ repeat from time 0. So
$$M_{n+k} \le M'_n + N_{n,k}, \qquad N_{n,k} = \max\{T_{n+k}(v) : v \text{ a seed whose diagonals } 0..n
\text{ repeat from time } 0\}.$$
Below depth 53,207 every seed's settled pair at depth $n$ is the single cell's shifted in time
([DrivenSkeleton](../../Rule30Open/Diagonals/DrivenSkeleton.md); the finding also checks it on every seed of 20
cells), so $N_{n,k}$ is the largest onset of the $k$-th diagonal of a row driven by the single
cell's pair $(D_{n-1}, D_n)$ at its worst phase, over all $2^k$ vectors of the driven diagonals (`driven_max`). An
induction with slope $3/2$ needs $N_{n,k} \le 3k/2 + c$ for all $n$.

**Where it stops.** The largest $N_{n,k}$ over $1 \le n \le 80$ is

| $k$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $\max_n N_{n,k}$ | 8 | 8 | 12 | 14 | 16 | 17 | 19 | 20 | 23 | 24 | 27 | 27 | 31 | 31 | 35 | 35 |
| minus $\lceil 3k/2 \rceil$ | 6 | 5 | 7 | 8 | 8 | 8 | 8 | 8 | 9 | 9 | 10 | 9 | 11 | 10 | 12 | 11 |

The excess grows by about 0.4 per diagonal: the slope is about 2, the front walk's
([FrontWalker](../../Rule30Open/Diagonals/FrontWalker.md)). The relaxation is not loose by unreachable states: every
driven vector is itself a seed (its prefix is a state of the single cell's cycle, with $D_0 = 1$), so
$N_{n,k} \le M_{n+k}$. What it loses is the time: a seed whose prefix has already settled can still put the worst
transient into the next $k$ diagonals, and the step charges that transient on top of $M'_n$. The induction hypothesis
"every seed" is too strong to be used at the later row and too weak to say which rows occur there.

## Route 2: the remaining diagonals as a fresh seed

**The step.** If after $S_a$ the next $b$ diagonals settled no later than those of a fresh seed of $b$ cells, then
$S_{a+b}(x) - S_a(x) \le M'_b$ and $M'$ would be subadditive, so $M'_j / j$ would tend to $\inf_b M'_b / b \le
M'_8 / 8 = 1$, against the slope about $3/2$ of the table.

**Where it stops.** At once. Over every seed of 20 cells, the largest $S_{i+k} - S_i$ is 4, 5, 7, 9, 10, 12, 13, 15,
16, 18 for $k = 1, \dots, 10$, against $M'_k = 1, 2, 2, 4, 5, 6, 8, 8, 11, 12$: a settled pair drives the next
diagonal harder than the white left side drives diagonal 0. $M'$ itself is not subadditive either:
$M'_4 = 4 > M'_1 + M'_3 = 3$.

## Route 3: the single cell is the worst seed up to a delay

**The finding.** For $9 \le j \le 76$ the latest onset is the single cell's plus 6, 7 or 8, and for all but six depths
$j \le 76$ it is reached by the two-cell seed with black cells at $lo$ and $lo + 3$, whose onsets are the single cell's
plus 6 for $11 \le j \le 138$. If $M_j \le T_j(\text{single}) + 8$ held for all $j$, the seed-uniform
question would be the single cell's.

**Where it stops.** At $j = 139$: the two-cell seed itself has $T_{139} = 188$ against the single cell's 178, a delay of
10, and among 200 seeds with fair-coin cells the first depth with a delay above 8 is also 139. Over the same seeds the
largest excess over the single cell is 14 on depths 139 to 299, 34 on 300 to 599 and 67 on 600 to 1,000, so on the
sampled range the delay grows with the depth; the excess over $\lceil 3j/2 \rceil$ meanwhile falls, to $-21$, $-47$
and $-117$ on those ranges.

## Route 4: the prefix fixes the rest behind a walk

**The step.** [PrefixWalk](../../Rule30Open/Diagonals/PrefixWalk.md) proves that two seeds with the same cells
$x_1, \dots, x_i$ have the same diagonal $d$ from the time $w_d$ of a walk through black cells, so
$T_d \le \max(w_d, T'_d)$ over every extension. It makes the exact search of the finding possible.

**Where it stops.** The walk advances about two times per depth, so iterated it is the front walk again: slope 2.

## What it means

Each route reduces the step to a transient it cannot see: the worst vector over the driven diagonals (route 1), the
driven start (route 2), or the cells before the walk (route 4). Route 3 shows the shape of the worst seeds in the
exact range, a delayed single cell, and that this shape does not last. The seed-uniform conjecture stays a statement
about how fast the chaotic region of a row can spread left, as for the single cell in
[linear settling leads](linear-settling-leads.md).

## Reproduce

```bash
python -m computations.seed_onsets --relax 80 --m 16          # route 1, about 15 s
python -m computations.seed_onsets --lemmas 20                # route 2, a few seconds
python -m computations.seed_onsets --sample 1000 --samples 200  # route 3, about 20 s
python -m computations.seed_onsets --prune 76 --K 0           # the exact table, about 47 min on two cores
```
