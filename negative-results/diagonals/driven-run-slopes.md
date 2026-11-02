---
title: Three routes to a run slope below 3/5 over every driven left half stop at the settling time of the left diagonals, which over every driver is the single cell's open problem with a transient added
category: diagonals
problems: [2]
status: negative
kind: dead-end
evidence: [computations/run_slope_routes.py]
---

# Three routes to a run slope below 3/5 over every driven left half stop at the settling time of the left diagonals, which over every driver is the single cell's open problem with a transient added

**Question.** [Driven left runs](../../findings/diagonals/driven-left-runs.md) conjectures that over every center
column $c(0) = 1, c(1), \ldots$ the left half it drives allows a black run from time $t$ of at most $\beta t + O(1)$
with $\beta < 3/5$ (measured near $0.15$ for $t \le 175$), and a white run of at most $\omega t + O(1)$ with
$\omega < 1$. A proof would cut the kit's slopes for the single cell's center column. Three routes were tried:

1. **Forced word.** A black run of length $L$ from $t$ forces the alternating word on cells $-(L-1) .. -1$ of row $t$
   (cell $-k$ black exactly for even $k$), and behind it the trapezoid of `black_block_back`. Exclude the word at time
   $t$ unless $L \le \alpha t + \beta$, by a finite argument on the reachable left halves.
2. **Diagonals.** The trapezoid meets the left diagonals $D_j(t) = \mathrm{cell}(t, j - t)$. Where a pair
   $(D_{j-1}, D_j)$ has settled, it cannot alternate in antiphase for long, so the run is short. Bound when every
   driver's diagonals settle.
3. **Window rank.** A rank on windows of $w$ cells at the right end of the left half, certified by a finite game,
   that bounds how soon a window can turn alternating.

All three stop at the same object: when the left diagonals settle. Over every driver that is the single cell's linear
settling conjecture ([settled runs](../../findings/diagonals/settled-runs.md)) plus a transient, because down to depth
53,207 the settled part does not depend on the driver ([DrivenSkeleton](../../Rule30Open/Diagonals/DrivenSkeleton.md)).

## Route 1: every right-end word occurs, so an exclusion must use the time

Backward in time the alternating word forces exactly the trapezoid and nothing more (enumeration in
[driven left runs](../../findings/diagonals/driven-left-runs.md)), so the question is whether the word occurs as the
right end of a reachable left half at time $t$. `right_end_first_times` records, for every word of $w$ cells, the first
time it is the right end (cells $-1 .. -w$) of the left half under some driver:

| $w$ | 4 | 6 | 8 | 10 | 12 | 14 | 16 |
|---|---:|---:|---:|---:|---:|---:|---:|
| Words never seen up to $t = 100$ | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Latest first time over all $2^w$ words | 11 | 19 | 32 | 47 | 63 | 76 | 96 |
| First time of the alternating word | 5 | 16 | 28 | 37 | 58 | 68 | 89 |

Every word of up to 16 cells occurs, all of them by $t \approx 6w$, and the alternating word occurs a few steps before
the last one. So no argument that looks only at the right end, an automaton on words included, can exclude the
alternating word: an exclusion must certify that the word's first time grows like $w / \beta$, which is a statement
about the reachable set $\mathcal{L}_t$ at each $t$. Its size grows like $2^{0.09 t}$ on $t \le 175$ with no finite
description known, and the step that would bound it is the settling of route 2.

## Route 3: a window rank does not even give the light cone

In the game where a window of $w$ cells at the right end moves with a free driver and a free cell entering from the
left (`window_game_distances`), every window is reached from the white window, and the alternating word at the
distance:

| $w$ | 2 | 4 | 6 | 8 | 10 | 12 | 14 | 16 | 18 | 20 | 22 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Steps to the alternating word | 1 | 3 | 4 | 5 | 6 | 8 | 10 | 12 | 13 | 15 | 16 |

The distance is below $w$ (about $0.73 w$ at $w = 22$), so a rank certified by this game bounds a black run from
time $t$ only by about $1.4t$, worse than the light cone ($L \le t + 1$), let alone $3/5$. The kit's slope $3/5$ comes
from the left edge ($D_0 = D_1 = 1$), not from a window; a window next to the edge is the
[fixed-depth strip](fixed-depth-strips.md), which gains a constant. A rank that improves the slope must know the
depth of the window at time $t$, which makes the game infinite: that is route 2.

## Route 2: the settling time over every driver

**What closes.** Three facts, proved:

- The window argument of [settled runs](../../findings/diagonals/settled-runs.md): if the pair $(D_{j-1}, D_j)$ repeats
  from time $T_j$ and its periodic part has no antiphase alternation longer than $A_j$ steps, the trapezoid cannot
  cover the pair for more than $A_j + 1$ consecutive times after $T_j$. If $T_j \le \gamma j$ for every $j$ and
  $A_j = o(j)$, black runs have slope at most $3(\gamma - 1)/(5\gamma - 1) < 3/5$.
  [SettledRuns](../../Rule30Open/Diagonals/SettledRuns.md) proves the argument in Lean for period 16 and
  $\gamma = 3/2$; [SettledSlope](../../Rule30Open/Diagonals/SettledSlope.md) proves it with $A + 1$ in place of $P + 1$
  and any periods, at $\gamma = 3/2$ and $27/20$. Always
  $A_j \le P_j$ (`altBound_of_period_le`): a pair that alternated for $P_j + 1$ settled times would alternate forever,
  which `no_alt_pair` forbids.
- [DrivenSkeleton](../../Rule30Open/Diagonals/DrivenSkeleton.md): every driver's eventual pair at depth $j$ is the
  single cell's read with a time shift, for $j \le 53{,}207$ (Lean step and base, a computed check at the four white
  diagonals 2, 7, 28, 399). So there $A_j$ and the period $P_j$ are the single cell's, and only $T_j$ depends on the
  driver. At the white diagonals 53,207 and 58,286 the period does not double and the step leaves a second,
  complemented class, which one flipped cell realizes ([the skeleton tree](../../findings/diagonals/skeleton-tree.md)).
- The reset bound: by `shift_of_black` (and `D_periodic_of_black` of [LeftMemory](../../Rule30Open/Diagonals/LeftMemory.md)),
  $T_{j+1} \le \max(T_j, j + 1) + g_j + 1$, where $g_j$ is the longest cyclic white run of the periodic part of
  $D_j$ ($g_j = -1$ for a white diagonal). With $T_1 = 2$ this gives a bound $B_j$ for every driver,
  `onset_bound`; the test checks $T_j \le B_j$ over every driver for $j \le 32$. For the single cell the bound is
  proved in Lean as `pair_repeats_of_white_runs` of [SettledSlope](../../Rule30Open/Diagonals/SettledSlope.md): the pair
  $(D_j, D_{j+1})$ repeats from $1 + \sum_{i \le j} (g_i + 1)$ (white diagonals counting 0).

**The numbers.** Over every driver (`driver_pairs`, all pairs $(D_{j-1}, D_j)$ on a horizon of $4j + 128$ steps,
deduplicated):

| $j$ | Pairs | Largest period | Classes up to a shift | Largest onset $T_j$ | $T_j / j$ |
|---:|---:|---:|---:|---:|---:|
| 10 | 14 | 4 | 1 | 14 | 1.400 |
| 20 | 80 | 4 | 1 | 31 | 1.550 |
| 30 | 258 | 8 | 1 | 41 | 1.367 |
| 40 | 638 | 8 | 1 | 63 | 1.575 |
| 50 | 2,134 | 8 | 1 | 81 | 1.620 |
| 60 | 6,466 | 8 | 1 | 94 | 1.567 |
| 70 | 14,746 | 8 | 1 | 107 | 1.529 |
| 80 | 36,232 | 8 | 1 | 119 | 1.488 |
| 90 | 82,184 | 8 | 1 | 135 | 1.500 |

So over every driver and $j \le 90$, $T_j \le 1.62 j$; with $\gamma = 1.62$ the window argument would give slope
$0.26$. The single cell's skeleton (`skeleton`, 24,600 rows, depths below 8,001), with the reset bound:

| $j$ | Largest $g_i$, $i < j$ | Mean $g_i$ | Largest $A_i$ | $B_j / j$ | $3(\gamma-1)/(5\gamma-1)$ at $\gamma = B_j/j$ |
|---:|---:|---:|---:|---:|---:|
| 50 | 6 | 2.02 | 2 | 2.84 | 0.418 |
| 100 | 7 | 2.35 | 3 | 3.25 | 0.443 |
| 400 | 7 | 2.63 | 7 | 3.60 | 0.459 |
| 800 | 15 | 3.11 | 7 | 4.09 | 0.477 |
| 2,000 | 15 | 3.42 | 7 | 4.41 | 0.486 |
| 8,000 | 15 | 3.59 | 7 | 4.59 | 0.491 |

**Where it stops.** Every bound above is a statement about finitely many depths. For all depths the route needs
$T_j \le \gamma j$ over every driver, and the only general tool, the reset bound, gives $B_j/j$ close to one plus the mean of
$g_i$, which rises with the period: from 2.84 at $j = 50$ to 4.59 at $j = 8{,}000$, stepping up after the period becomes 16 at
depth 400. The periods are unbounded (Nersissian 2026, in [the literature](../../literature/rule-30.md); 32 from depth
87,867, [the records](../../findings/diagonals/left-records.md)), longer periods allow longer white runs ($g_j < P_j$),
and nothing bounds the mean of $g_j$ over all depths, so the reset bound may not even be linear. The true onsets are
smaller (81 against $B_{50} = 142$ at $j = 50$), and bounding them is the single cell's linear settling conjecture
with a driver-dependent transient on top. The relaxation to every driver gains nothing: by DrivenSkeleton the settled
part is the single cell's down to depth 53,207, and $A_j$ and $g_j$ are its numbers; deeper, a driver may also settle
to complemented pairs, which can only add cases.

## What it means

The driven-runs conjecture is not easier than [linear settling](../../findings/diagonals/settled-runs.md): its natural
proof is linear settling for every configuration white left of a black cell, which contains the single cell's case.
The new inputs a proof would need are about the single cell's left skeleton at every depth (and, from depth 53,208
on, about the complemented skeletons that DrivenSkeleton does not exclude): that the mean cyclic white
run of its periodic diagonals stays bounded (which by the reset bound gives linear settling over every driver, with
$\gamma$ one more than that mean) and that the longest antiphase alternation $A_j$ is $o(j)$ (it is at most 7 below
depth 8,000). Either is a statement about all depths of the single cell's left side, open like the periods themselves.
White runs were not pursued separately: their slope below 1 needs the same settled diagonals (the white-block window of
[settled runs](../../findings/diagonals/settled-runs.md)).

## Reproduce

```bash
python -m computations.run_slope_routes ends --width 16 --steps 100   # route 1 table, about 2 s
python -m computations.run_slope_routes game --width 22               # route 3 table, about 25 s
python -m computations.run_slope_routes pairs --depth 90              # route 2, every driver, about 3 min
python -m computations.run_slope_routes skeleton --depth 8001         # route 2, the single cell, about 7 s
python -m computations.run_slope_routes followers --depth 59000 --steps 110000   # white diagonals to 59,000, about 3 s
```
