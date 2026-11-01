---
title: Over every row white left of a black cell, the left diagonal j settles by time ceil(3j/2) + 5 for j up to 76, exactly; from depth 9 to 76 the worst row is the single cell delayed by 6 to 8 steps, and the bound is conjectured for every j
category: diagonals
problems: [2]
status: conjecture
formalization: wanted
evidence: [computations/seed_onsets.py]
---

# Over every row white left of a black cell, the left diagonal j settles by time ceil(3j/2) + 5 for j up to 76, exactly; from depth 9 to 76 the worst row is the single cell delayed by 6 to 8 steps, and the bound is conjectured for every j

A *seed* is a row white left of a black cell $lo$, with any cells $x_1, x_2, \dots$ right of it. Its left diagonals
$D_j(t) = \mathrm{cell}_t(lo - t + j)$ follow the single cell's recurrence
$D_{j+2}(t+1) = D_j(t) \oplus (D_{j+1}(t) \lor D_{j+2}(t))$ with $D_0 = 1$ and $D_j(0) = x_j$, so $D_j$ depends on
$x_1, \dots, x_j$ only, and the row of a seed at any later time is again a seed. Let $T_j$ be the onset of $D_j$ (the
least time from which it repeats) and $M_j$ the largest onset over all $2^j$ seeds. The single cell is the seed with
every $x_i = 0$; [SettledSlope](../../Rule30Open/Diagonals/SettledSlope.md) turns $T_j \le 3j/2 + o(j)$ for it,
together with $o(j)$ antiphase alternations of the settled pairs, into black center runs of slope $3/13$.

## Result

For every $j \le 76$, every seed has $T_j \le \lceil 3j/2 \rceil + 5$, and 5 is the least such constant: $M_{48} = 77$.
The exact maxima:

| $j$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $M_j$ | 0 | 1 | 2 | 2 | 4 | 5 | 6 | 8 | 7 | 11 | 12 | 14 | 14 |
| $M_j - \lceil 3j/2 \rceil$ | 0 | -1 | -1 | -3 | -2 | -3 | -3 | -3 | -5 | -3 | -3 | -3 | -4 |
| $M_j - T_j(\text{single})$ | 0 | 0 | 0 | 0 | 2 | 3 | 4 | 8 | 5 | 6 | 6 | 6 | 8 |

| $j$ | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $M_j$ | 16 | 17 | 19 | 22 | 21 | 26 | 24 | 29 | 29 | 31 | 30 | 33 | 34 |
| $M_j - \lceil 3j/2 \rceil$ | -4 | -4 | -4 | -2 | -5 | -1 | -5 | -1 | -3 | -2 | -5 | -3 | -4 |
| $M_j - T_j(\text{single})$ | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 |

| $j$ | 26 | 27 | 28 | 29 | 30 | 31 | 32 | 33 | 34 | 35 | 36 | 37 | 38 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $M_j$ | 35 | 36 | 37 | 36 | 39 | 40 | 42 | 42 | 46 | 45 | 52 | 48 | 54 |
| $M_j - \lceil 3j/2 \rceil$ | -4 | -5 | -5 | -8 | -6 | -7 | -6 | -8 | -5 | -8 | -2 | -8 | -3 |
| $M_j - T_j(\text{single})$ | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 8 | 6 | 7 | 6 |

| $j$ | 39 | 40 | 41 | 42 | 43 | 44 | 45 | 46 | 47 | 48 | 49 | 50 | 51 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $M_j$ | 56 | 61 | 58 | 63 | 62 | 67 | 65 | 70 | 68 | 77 | 71 | 79 | 80 |
| $M_j - \lceil 3j/2 \rceil$ | -3 | 1 | -4 | 0 | -3 | 1 | -3 | 1 | -3 | 5 | -3 | 4 | 3 |
| $M_j - T_j(\text{single})$ | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 |

| $j$ | 52 | 53 | 54 | 55 | 56 | 57 | 58 | 59 | 60 | 61 | 62 | 63 | 64 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $M_j$ | 82 | 81 | 84 | 84 | 88 | 85 | 90 | 91 | 92 | 93 | 93 | 97 | 94 |
| $M_j - \lceil 3j/2 \rceil$ | 4 | 1 | 3 | 1 | 4 | -1 | 3 | 2 | 2 | 1 | 0 | 2 | -2 |
| $M_j - T_j(\text{single})$ | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 |

| $j$ | 65 | 66 | 67 | 68 | 69 | 70 | 71 | 72 | 73 | 74 | 75 | 76 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $M_j$ | 99 | 100 | 103 | 102 | 105 | 105 | 105 | 106 | 105 | 108 | 107 | 110 |
| $M_j - \lceil 3j/2 \rceil$ | 1 | 1 | 2 | 0 | 1 | 0 | -2 | -2 | -5 | -3 | -6 | -4 |
| $M_j - T_j(\text{single})$ | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 |

- **Worst seeds.** For $9 \le j \le 76$, $M_j$ is the single cell's onset plus 6, 7 or 8. For every $j \le 76$ but
  $3, 8, 10, 12, 35$ and $37$ it is reached by the two-cell seed with black cells at $lo$ and $lo + 3$ ($x_3 = 1$),
  whose onsets are the single cell's plus 6 for $11 \le j \le 138$ and plus 10 at $j = 139$. So in the exact range
  the latest row is a delayed single cell, and $M_j - \lceil 3j/2 \rceil$ follows the single cell's
  $T_j - \lceil 3j/2 \rceil$, which is never positive to depth 200,000
  ([linear settling leads](../../negative-results/diagonals/linear-settling-leads.md)).
- **How many.** Exhaustively to depth 38, the number of seeds $x_1 \dots x_j$ reaching $M_j$ is 4,263,936 of $2^{26}$ at
  $j = 26$ and 17,465,081,856 of $2^{38}$ at $j = 38$.
- **Skeleton.** On every seed of 20 cells, every diagonal's periodic part is the single cell's shifted in time
  (`same_skeleton`). By [DrivenSkeleton](../../Rule30Open/Diagonals/DrivenSkeleton.md) this holds for every seed
  below depth 53,207: the periodic parts are forced by the two diagonals before, except behind the white diagonals 2,
  7, 28 and 399, where the period doubles and the two choices of the next diagonal differ by a shift
  ([left records](left-records.md), [LeftMemory](../../Rule30Open/Diagonals/LeftMemory.md)).
- **Deeper, by sampling.** Over 200 seeds with fair-coin cells to depth 1,000, the largest $T_j - \lceil 3j/2 \rceil$
  is 5 on depths 20 to 68, 3 on 69 to 138, $-21$ on 139 to 299, $-47$ on 300 to 599 and $-117$ on 600 to 1,000.

**Conjecture (seed-uniform settling).** For every seed and every $j$, $T_j \le \lceil 3j/2 \rceil + 5$. It holds for
$j \le 76$ by the searches below and holds on the sampled seeds to depth 1,000. For the single cell it is the settling
hypothesis of SettledSlope with $\delta = 5$, which also needs the alternations bounded. The conjecture asks more than
the single cell needs, but it is the form an induction over depths would carry: the row at any time is again a seed. The
routes tried for such an induction, and where each stops, are in
[seed-uniform induction](../../negative-results/diagonals/seed-uniform-induction.md). In the sampled range the
excess over the single cell grows (it is 67 near depth 1,000), while the excess over $\lceil 3j/2 \rceil$
falls, so the conjecture is about the slope, not about the single cell being the worst seed.

## Method

- **Exhaustive to depth 38** (`seed_onsets_search.c`): the cells $x_1, \dots, x_9$ in the 512 lanes of a vector,
  $x_{10}, \dots, x_J$ depth first; each node computes the whole sequence $D_i(0 .. H-1)$ from $D_{i-2}$ and $D_{i-1}$.
  About 7 min of CPU at depth 38.
- **Branch and bound to depth 76** (`seed_onsets_prune.c`): one seed at a time, and a prefix is not extended when no
  extension can raise any $M_d$: by [PrefixWalk](../../Rule30Open/Diagonals/PrefixWalk.md), every extension has
  diagonal $d$ equal to a diagonal computed from the prefix from the time $w_d$ of a walk through black cells, so
  its onset is at most $\max(w_d, U_d)$, $U_d$ one more than the last change of the computed part. The branch and
  bound agrees with the exhaustive search at every depth to 38 and reaches depth 72 in 97 million nodes (207 s on two
  cores) and depth 76 in 1.37 billion (47 min on two cores).
- **Onsets from a finite table.** Both read the times $0, \dots, H - 1$ with period 8, which is a multiple of every
  period below depth 399. The onset is the least $T$ with $D_j(t + 8) = D_j(t)$ for $T \le t \le H - 9$. If every
  onset a search computes is at most $H - 9$, then at the latest of them the vector $(D_0, \dots, D_J)$ of each seed
  equals itself 8 steps later, and the vector evolves by itself, so it repeats from there for ever and the window
  onsets are the true onsets. Both programs report the largest onset they computed, and the runs check it against
  $H - 9$ (a diagonal of another period would show an onset near $H$).
- **Checks.** `tests/test_seed_onsets.py` compares the bit-packed table of every seed of 12 cells with one seed at a
  time (a Python integer per time), both C searches with the table, the maxima with the single cell's onsets of
  `settled_slope`, and the driven relaxation with a scalar run.

## Reproduce

```bash
python -m computations.seed_onsets --exhaustive 38            # about 8 min on two cores
python -m computations.seed_onsets --prune 76 --K 0           # about 47 min on two cores
python -m computations.seed_onsets --sample 1000 --samples 200  # the sampled range, about 20 s
python -m computations.seed_onsets --lemmas 20                # the skeleton check on every seed of 20 cells
```
