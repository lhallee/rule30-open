---
title: A walk that steps down on black cells and down-left on white ones bounds when the left diagonals settle; it advances 2.01 times per depth to depth 200,000, and a walk of slope 2 + o(1) would give black center runs of slope 1/3
category: diagonals
problems: [2]
status: proved
lean: Rule30Open.Diagonals.FrontWalker
headline: [pair_repeats_of_walk, black_run_le_of_walk, black_run_le_of_steep_walk]
kit: refines
kit_modules: [Rule30Diagonals, Rule30CenterRuns]
evidence: [computations/front_walker.py]
---

# A walk that steps down on black cells and down-left on white ones bounds when the left diagonals settle; it advances 2.01 times per depth to depth 200,000, and a walk of slope 2 + o(1) would give black center runs of slope 1/3

[SettledSlope](SettledSlope.md) turns linear settling of the left diagonals into a slope $3/13$ for black runs of the
center column, and its reset bound turns the settling into a sum of costs $c_i$, one more than the longest white run of
the periodic part of $D_i$. The mean cost rises with the period (4.64 at period 16, 5.52 at period 32), so the reset
bound is not expected to stay linear. This module replaces the longest white run by the white run the reset actually
meets. The result is a walk through the settled part of the pattern whose mean step is about 2.01 at periods 16 and 32, and
a slope theorem whose hypothesis is about that walk alone.

## Statement

Let $D_j(t) = \mathrm{cell}(t, j - t)$ be the left diagonals, and say $f$ *repeats with period $P$ from $T$* if
$f(t + P) = f(t)$ for $t \ge T$ (`RepeatsFrom`).

- `FrontWalk w J`: $w_1 \ge 1$, and for every $1 \le i \le J$, diagonal $i$ has a black cell at some time
  $r$ with $w_i \le r < w_{i+1}$, or $D_i$ is eventually white and $w_i \le w_{i+1}$.
- `pair_repeats_of_walk`: along a front walk to depth $J$, for every $j \le J$ the pair $(D_j, D_{j+1})$ repeats with
  a common period $P > 0$ from time $w_{j+1}$.
- `black_run_le_of_walk`: if moreover $w_{j+1} \le 2j + \delta$ for $j \le J$, and the antiphase alternations of every
  pair $j \le J$ are eventually bounded by $A$ (`AltBound` of [SettledSlope](SettledSlope.md)), then a black run of the
  center column of length $L$ from time $a \ge 1$ with $\lfloor 4a/9 \rfloor \le J$ has
  $$9L \le 3a + 60A + 60\delta + 200.$$
- `black_run_le_of_steep_walk`: the same with $w_{j+1} \le \lceil 41j/20 \rceil + \delta$ and
  $\lfloor 16a/37 \rfloor \le J$ gives $185 L \le 63 a + 1200 A + 1200\delta + 4000$.

The slopes are $3(\gamma - 1)/(5\gamma - 1)$ at $\gamma = 2$ and $41/20$: $1/3$ and $63/185 \approx 0.341$, against
$3/5$ unconditionally. As in SettledSlope the theorems hold for every $J$, $\delta$ and $A$, so the slope $1/3$ follows
for all $a$ as soon as the least front walk has $w_j \le 2j + o(j)$ and $A_J = o(J)$.

**The least front walk.** Put $w_0 = 0$, $w_1 = 1$, and from $w_i$ let $r$ be the first time with $D_i(r) = 1$; then
$w_{i+1} = r + 1$, or $w_{i+1} = w_i$ if $D_i$ is white from $w_i$ on. On the space-time diagram the walk sits at the
cell $(w_i, i - w_i)$ of diagonal $i$; from a black cell it moves straight down to $(r + 1, i - r)$, which is on
diagonal $i + 1$, and from a white cell down-left along its diagonal. Each step costs one time for the black cell plus
the white run it slides over.

## Argument

1. **The walk bounds the settling** (`pair_repeats_of_walk`). The pair $(D_0, D_1)$ is black from time 1 on, so it
   repeats with period 1 from $w_1 \ge 1$. Suppose $(D_j, D_{j+1})$ repeats with period $P$ from $w_{j+1}$. If
   $D_{j+1}$ is black at some $r$ with $w_{j+1} \le r < w_{j+2}$, then $D_{j+2}$ repeats with period $P$ from $r + 1$
   (`D_periodic_of_black` of [LeftMemory](LeftMemory.md): behind a black cell the next diagonal forgets its past), so
   the pair $(D_{j+1}, D_{j+2})$ repeats from $w_{j+2}$. If $D_{j+1}$ is eventually white, it is white from $w_{j+1}$
   (a periodic sequence that is eventually white is white), and the pair repeats with period $2P$ from $w_{j+1}$
   (`pair_step_white` of SettledSlope), hence from $w_{j+2} \ge w_{j+1}$.
2. **The window** (`black_run_le_of_walk`). This is step 3 of [SettledSlope](SettledSlope.md) at $\gamma = 2$: put
   $j = \lfloor 4a/9 \rfloor$ and $s_0 = \lfloor (a + 2 - j - L)/2 \rfloor$. If $9L > 3a + 60A + 60\delta + 200$, then
   $L \le a$ (the kit's `black_run_le`) and `omega` checks that the trapezoid of the run covers diagonals $j$ and
   $j + 1$ at the $A + 1$ times $a - s_0 - A, \dots, a - s_0$, all after $w_{j+1}$, which contradicts the bound on the
   alternations (`black_run_window`, `altBound_of_repeats`). At $\gamma = 41/20$ the depth is
   $\lfloor 16a/37 \rfloor$.

Every cell the walk reads is at or after the onset of its diagonal (step 1), so $w_j$ is a function of the periodic
parts of the diagonals and their phases alone: the hypotheses of the slope theorems say nothing about the transient.

## The range of the hypotheses

`front_walker` reads the onsets $T_j$ (the first time from which $D_j(t + 64) = D_j(t)$ holds to the end of the table)
and the last 256 rows of `settled_slope.stream` for $J = 200{,}000$ and 300,600 steps, and runs the least front walk on
them, checking at each step that it reads at or after the onset. A white run that lasts a whole period of 64 is a white
diagonal; the walk crosses one at once exactly at the seven white diagonals 2, 7, 28, 399, 53,207, 58,286 and 87,866.
For every $j \le 200{,}000$:

- $T_j \le w_j$, as `pair_repeats_of_walk` says; $w_{200{,}000} = 402{,}228$.
- $w_{j+1} \le \lceil 41j/20 \rceil + 1$: `black_run_le_of_steep_walk` applies with $\delta = 1$, $A = 9$ (the
  alternation bound of SettledSlope in this range) and $J = 199{,}999$, and gives $185 L \le 63a + 16{,}000$ for
  $1 \le a \le 462{,}499$. The largest $w_j / j$ past depth 1,000 is 2.0270.
- $w_{j+1} \le 2j + 2262$: `black_run_le_of_walk` applies with $\delta = 2262$. The excess $\max_{j \le J}(w_j - 2j)$ is
  1 at $J = 1{,}000$, 206 at $10^4$, 996 at $5 \cdot 10^4$, 1,385 at $10^5$ and 2,260 at $2 \cdot 10^5$, so in this
  range it grows by about 0.011 per depth: the mean step is a little above 2.

Grouped by the least period of the diagonal the walk slides along (white diagonals left out):

| Period | Diagonals | Mean step | Largest step | Steps of 1 | Uniform phase | After a black cell | Mean cost $c_j$ |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 4 | 56 | 1.625 | 4 | 0.589 | 1.768 | 1.744 | 2.911 |
| 8 | 668 | 2.061 | 7 | 0.472 | 1.977 | 1.976 | 3.813 |
| 16 | 87,119 | 2.014 | 15 | 0.487 | 2.001 | 2.002 | 4.642 |
| 32 | 112,131 | 2.009 | 18 | 0.498 | 2.000 | 2.000 | 5.524 |

"Uniform phase" is the mean over the diagonals of one plus the distance from a phase chosen uniformly in the period to
the next black cell; "after a black cell" averages only over the phases $s$ with $D_{j-1}(s - 1) = 1$, where the walk
arrives. The step of the walk is the cost of the reset at the phase where it happens, and that phase is typical: the
mean step matches the uniform-phase mean, about 2 at every period, while the mean cost $c_j$, which charges the worst
phase, rises by 0.83 to 0.90 at each doubling.

## What it means

**The walk is the reset bound at the actual phase.** The reset bound of SettledSlope charges each diagonal its longest
white run; the walk charges the white run it meets, and $w_{200{,}000} / 200{,}000 = 2.011$ against
$1 + \sum c_i \approx 5.13 j$. The onsets themselves are smaller still, about $1.33j$: the walk is what the front law
gives when the defect bit is 1 at every depth (see [linear settling leads](../../negative-results/diagonals/linear-settling-leads.md)),
and the actual front moves faster because about 45% of the bits are 0.

**A heuristic for all depths, not a proof.** The 199,597 steps of the walk past depth 400 (white diagonals left out)
are close to one plus a geometric variable of parameter $1/2$, the gap to the next black cell in a sequence of fair
coins: steps of $k = 1, \dots, 7$ have frequencies 0.4931, 0.2559, 0.1253, 0.0622, 0.0319, 0.0158 and 0.0078, against
$2^{-k}$, and the fraction of steps of 1 after a step of $k$ is between 0.475 and 0.502 for each $k \le 7$ and for
$k \ge 8$. The deviation is small but real: steps of 1 fall short of one half by 0.0069, six standard errors, and the
mean step is $2.0113$, against a standard error of $0.0032$. The uniform-phase mean of a word of $P$ fair bits is
about $1 + \sum_{g = 1}^{P - 1} 2^{-g}$, close to 2 at every $P$, unlike its longest white run, which grows like
$\log_2 P$. *Heuristic (not proved):* if the cells the walk reads stay this close to fair coins at every depth, $w_j$
stays within $(2.011 + o(1))\,j$, below $41j/20$ with fluctuations of order $\sqrt{j}$, and the hypothesis of
`black_run_le_of_steep_walk` holds at every depth with a bounded $\delta$. The reset bound's hypothesis $\sum c_i \le 6j$ is expected to fail on the same heuristic. So the
open input for a slope below $3/5$ becomes a statement about the settled left side only: the walk advances at least
one depth per $41/20$ times on average (with fluctuations $o(j)$), and the alternations stay $o(j)$. Neither is proved;
where the attempts stop is in [linear settling leads](../../negative-results/diagonals/linear-settling-leads.md).

**What the computed range gives.** As in SettledSlope, only the range: black runs from $a \le 462{,}499$ with
$185 L \le 63a + 16{,}000$, where computation already bounds every black run by 22.

## In Lean

`FrontWalk` is a hypothesis on a sequence, not a definition of the least walk, so the least walk does not need a
search over unbounded times: any sequence that meets a black cell on each slide, or crosses an eventually white
diagonal, is a front walk. `pair_repeats_of_walk` is an induction on $j$ over `D_periodic_of_black` and
`pair_step_white`, the steps of `pair_repeats_of_white_runs` in SettledSlope. The two slope theorems choose $j$ and
$s_0$ and leave the arithmetic to `omega`. The axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Relation to the kit

The pinned kit proves each left diagonal eventually periodic with period dividing $2^j$
(`Rule30Diagonals.D_periodic`) and has no onset bound linear in $j$. The kit's main branch, after the pinned revision,
has the least front walk as `Rule30FrontLaw.frontBound` ($\mathrm{frontBound}\,(j+2)$ is one more than the first
black cell of $D_{j+1}$ at or after $\max(\mathrm{frontBound}\,j, \mathrm{frontBound}\,(j+1))$, or that maximum if there
is none; the bound is nondecreasing, so the maximum is the later one) and proves `D_periodic_from_frontBound`, the onset part of `pair_repeats_of_walk` for the least walk. It
bounds frontBound by sums of periods (`frontBound_le_periodSum`, `frontBound_le_linear`) and, through
`Rule30SettledBarrierEffective.frontBound_le_count`, by $1 + m\,2^c$ with $c$ a count of white diagonals. The reading
of frontBound as a walk on the space-time diagram, its measured mean step 2.01, and the slope theorems from it are not
in the kit at either revision.

## Reproduce

```bash
python -m computations.front_walker --depth 200000   # every number here, about 3 min, 0.2 GB
```
