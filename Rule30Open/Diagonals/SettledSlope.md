---
title: If the left diagonals repeat from time 3j/2 with any periods and no settled pair alternates in antiphase more than A times, black center runs have 13L at most 3a + 130A + 260; the reset bound reduces the settling to the white runs of the settled diagonals
category: diagonals
problems: [2]
status: proved
lean: Rule30Open.Diagonals.SettledSlope
headline: [altBound_of_repeats, altBound_of_period_le, black_run_window, black_run_le_of_settling, black_run_le_of_fast_settling, pair_repeats_of_white_runs, black_run_le_of_white_runs]
kit: new
kit_modules: [Rule30Diagonals, Rule30CenterRuns]
evidence: [computations/settled_slope.py]
---

# If the left diagonals repeat from time 3j/2 with any periods and no settled pair alternates in antiphase more than A times, black center runs have 13L at most 3a + 130A + 260; the reset bound reduces the settling to the white runs of the settled diagonals

[SettledRuns](SettledRuns.md) bounds black runs of the center column under the hypothesis that the left diagonals
repeat with the fixed period 16 from time $3j/2$, which is false from depth 87,867 on. This module removes the period
from the hypothesis: the window argument needs only a bound $A$ on how long a settled pair of diagonals alternates in
antiphase, and the period of each diagonal may be anything. It also proves the reset bound, which turns the settling
time into a sum of the white runs of the settled diagonals. **The hypotheses are not proved, only checked by
computation for every depth $j \le 200{,}000$**; with them the theorems bound runs from times $a \le 324{,}999$ (and
$a \le 1{,}449{,}999$ for the white-run form), where the kit's computation already bounds the runs by 22.

## Statement

Let $D_j(t) = \mathrm{cell}(t, j - t)$ be the left diagonals. Say $f$ *repeats with period $P$ from $T$* if
$f(t + P) = f(t)$ for $t \ge T$. An *antiphase window* of length $A + 1$ of the pair $(D_j, D_{j+1})$ at $T$ is
$D_{j+1}(T + k) = \lnot D_j(T + k)$ for $0 \le k \le A$ and $D_j(T + k + 1) = \lnot D_j(T + k)$ for $0 \le k < A$; the
pair has *alternations bounded by $A$ from $T$* (`AltBound j T A`) if it has no such window at any time $\ge T$.

- `altBound_of_repeats`: if the pair repeats with a period $P > 0$ from $T$ and its alternations are bounded by $A$
  from some time on, they are bounded by $A$ from $T$.
- `altBound_of_period_le`: if the pair repeats with period $P > 0$ from $T$, its alternations are bounded by $P$ from
  $T$. So the longest antiphase alternation of a settled pair lasts at most $P$ times (exactly $P = 1$ times for the
  pair $(D_1, D_2)$, black and white).
- `black_run_window`: if a black run of length $L$ from time $a$ and numbers $j, s_0$ satisfy
  $a + 1 \le 2 s_0 + j + L$ and $5(s_0 + A) + j + 1 \le a$, then the alternations of $(D_j, D_{j+1})$ are not bounded
  by $A$ from any $T \le a - s_0 - A$.
- `black_run_le_of_settling`: suppose that every diagonal $j \le J + 1$ repeats, with a period $P_j > 0$ that may
  depend on $j$, from time $\lceil 3j/2 \rceil + \delta$, and that the alternations of every pair $j \le J$ are bounded
  by $A$ from some time on. Then a black run of the center column from time $a \ge 1$ with $\lfloor 8a/13 \rfloor \le J$
  has length $L$ with
  $$13 L \le 3a + 130 A + 130 \delta + 260.$$
- `black_run_le_of_fast_settling`: the same with the settling time $\lceil 27j/20 \rceil + \delta$ and
  $\lfloor 16a/23 \rfloor \le J$ gives $115 L \le 21 a + 1600 A + 1600 \delta + 4000$, the slope $21/115 \approx 0.183$.
- `pair_repeats_of_white_runs` (the reset bound): suppose that each diagonal $1 \le i \le J$ is eventually white, or
  from some time on has a black cell among every $c_i$ consecutive times (its white runs are shorter than $c_i$). Then
  for every $j \le J$ the pair $(D_j, D_{j+1})$ repeats with a common period from time $1 + c_1 + \dots + c_j$.
- `black_run_le_of_white_runs`: if moreover $c_1 + \dots + c_j \le 6j + \delta$ for $j \le J$ and the alternations of
  every pair $j \le J$ are bounded by $A$ from some time on, a black run from $a \ge 1$ with
  $\lfloor 4a/29 \rfloor \le J$ has $29 L \le 15 a + 90 A + 90 \delta + 180$, the slope $15/29 \approx 0.517$. Its
  hypotheses are about the periodic parts of the diagonals only, not about when they start.

The slopes are $3(\gamma - 1)/(5\gamma - 1)$ at $\gamma = 3/2$, $27/20$ and $6$, all below $3/5$. The theorems hold for
every $J$, $\delta$ and $A$; in particular they may be applied at each start time $a$ with $J = \lfloor 8a/13 \rfloor$
and with $A$ and $\delta$ the largest needed up to that depth. So the slope $3/13$ follows for all $a$ as soon as the
longest antiphase alternation $A_J$ and the settling excess $\delta_J = \max_{j \le J}(T_j - \lceil 3j/2 \rceil)$ over
the depths $j \le J$ are $o(J)$: a fixed period is not needed, and neither is a bounded $A$.

## Argument

1. **Alternations in place of the period.** [SettledRuns](SettledRuns.md) uses the period $P$ for one thing: a pair
   that alternates in antiphase over $P + 1$ settled times does so forever (`settled_alt_pair`), which `no_alt_pair`
   forbids. What the window argument needs is only that no antiphase window of some length $A + 1$ starts after the
   settling time, which is `AltBound`. It holds with $A = P$ (`altBound_of_period_le`), and in the computed range with
   $A = 9$ while the periods reach 32. For a pair that repeats from $T$ with period $P$, a window at $T' \ge T$ is
   carried to $T' + mP$ by the period, so a bound that holds eventually holds from $T$ (`altBound_of_repeats`); two
   diagonals with periods $P_0$ and $P_1$ share the period $P_0 P_1$ (`altBound_of_settled`).
2. **The window** (`black_run_window`). A black run of length $L$ from $a$ makes row $a - s$ read the alternating
   pattern on the cells $-(L - 1) - s .. -4s$ (`black_block_back` of [SettledRuns](SettledRuns.md)), so $D_j(a - s)$ and
   $D_{j+1}(a - s)$ read it whenever $a + 1 \le 2s + j + L$ and $5s + j + 1 \le a$. For the $A + 1$ values
   $s = s_0, \dots, s_0 + A$ this is an antiphase window at the time $a - s_0 - A$.
3. **Choice of the depth** (`black_run_le_of_settling`). Put $j = \lfloor 8a/13 \rfloor$ and
   $s_0 = \lfloor (a + 2 - j - L)/2 \rfloor$ (or 0). If $13L > 3a + 130A + 130\delta + 260$, then $L \le a$ (the kit's
   `black_run_le`) gives $10a > 130A + 130\delta + 260$, and `omega` checks the window conditions and that
   $a - s_0 - A$ is past $\lceil 3(j+1)/2 \rceil + \delta$, the later settling time of the pair. With $\gamma$ in place of
   $3/2$ the depth is $j = \lfloor 4a/(5\gamma - 1) \rfloor$: the window must end after $\gamma j$, which needs
   $(2\gamma - 1) j \lesssim a + L$, and must fit under the trapezoid, which needs $3a \lesssim 3j + 5L$; together they
   give $(5\gamma - 1) L \gtrsim 3(\gamma - 1) a$. The constants $130A + 260$ come from the case $s_0 = 0$ of long runs,
   where only $L \le a$ is used; they are not optimized.
4. **The reset bound** (`pair_repeats_of_white_runs`). The pair $(D_0, D_1)$ repeats with period 1 from time 1. Suppose
   $(D_j, D_{j+1})$ repeats with period $P$ from $Q$. If $D_{j+1}$ is eventually white, it is white from $Q$ (a periodic
   sequence that is eventually white is white), so $D_{j+2}$ accumulates $D_j$ from $Q$ on and changes over each period
   by the parity of $D_j$ over a period (`D_shift_of_white` and `windowParity_periodic` of
   [LeftMemory](LeftMemory.md)); two periods cancel, so $D_{j+1}, D_{j+2}$ repeat with period $2P$ from $Q$
   (`pair_step_white`). Otherwise the white runs of $D_{j+1}$ are shorter than $c_{j+1}$ from $Q$ on (by the period,
   `blackWithin_of_repeats`), so $D_{j+1}$ is black at some $r < Q + c_{j+1}$, and $D_{j+2}$ repeats with period $P$
   from $r + 1$ (`D_periodic_of_black` of [LeftMemory](LeftMemory.md); `pair_step_black`). By induction the pair $j$
   repeats from $1 + c_1 + \dots + c_j$.
5. **White runs in place of settling times** (`black_run_le_of_white_runs`). With $c_1 + \dots + c_j \le 6j + \delta$
   the pair $j$ repeats from $6j + \delta + 1$, and step 3 at $\gamma = 6$, $j = \lfloor 4a/29 \rfloor$, applies.

## The range of the hypotheses

`settled_slope` runs the vector $(D_0(t), \dots, D_J(t))$, which evolves by itself because $D_j$ depends only on the
diagonals $i \le j$, for $J = 200{,}000$ and 300,600 steps, records for each diagonal the first time $T_j$ from which
$D_j(t + 64) = D_j(t)$ holds to the end of the table (64 is a multiple of every period in this range), and reads the
periodic parts from the last 256 rows. Every onset is at least four periods before the end.

| Depths | Largest $T_j / j$ | At depth | Largest $g_j$ | Mean $c_j = g_j + 1$ | Largest $A_j$ |
|---|---:|---:|---:|---:|---:|
| 8 to 99 | 1.4792 | 48 | 7 | 3.413 | 3 |
| 100 to 399 | 1.4112 | 107 | 7 | 3.710 | 7 |
| 400 to 7,999 | 1.3379 | 7,978 | 15 | 4.637 | 8 |
| 8,000 to 53,206 | 1.3455 | 28,584 | 15 | 4.646 | 8 |
| 53,207 to 87,866 | 1.3397 | 70,950 | 15 | 4.630 | 8 |
| 87,867 to 199,999 | 1.3356 | 88,089 | 23 | 5.524 | 9 |

Here $g_j$ is the longest cyclic white run of the periodic part of $D_j$ (white diagonals, at 2, 7, 28, 399, 53,207,
58,286 and 87,866, have cost $c_j = 0$), and $A_j$ is the longest antiphase alternation of the pair $(D_j, D_{j+1})$,
counted in times, so that `AltBound j T A_j` holds. Grouped by the least period of the diagonal:

| Period | Diagonals | Mean $c_j$ | Largest $g_j$ | Largest $A_j$ |
|---:|---:|---:|---:|---:|
| 4 | 56 | 2.911 | 3 | 3 |
| 8 | 668 | 3.813 | 7 | 7 |
| 16 | 87,119 | 4.642 | 15 | 8 |
| 32 | 112,132 | 5.524 | 23 | 9 |

So for every $j \le 200{,}000$, on this table:

- $T_j \le \lceil 3j/2 \rceil$: the hypothesis of `black_run_le_of_settling` holds with $\delta = 0$, $A = 9$ and
  $J = 199{,}999$, which gives $13 L \le 3a + 1430$ for $1 \le a \le 324{,}999$.
- $T_j \le \lceil 27j/20 \rceil + 10$ ($\delta = 10$ is needed at small depths; the largest ratio past depth 1,000 is
  1.3455; the excess 10 is attained at depth 85): `black_run_le_of_fast_settling` gives $115 L \le 21a + 34{,}400$
  for $1 \le a \le 287{,}499$. At $\gamma = 4/3$ the excess $\delta$ is 349 to depth 30,000 and 452 to depth
  200,000, and grows with the depth while $T_j/j$ exceeds $4/3$.
- $c_1 + \dots + c_j \le 6j$: `black_run_le_of_white_runs` applies with $\delta = 0$, $A = 9$, $J = 199{,}999$ and gives
  $29 L \le 15a + 990$ for $1 \le a \le 1{,}449{,}999$. With $5j$ in place of $6j$ the excess is 0 to depth 10,000 and
  26,601 up to depth 200,000, growing at the rate $5.524 - 5$ per depth since the period became 32. [FrontWalker](FrontWalker.md) replaces the
  longest white run by the white run the reset actually meets, which gives a walk of about $2.01j$.

The table checks each equality only up to time 300,535. It extends to all later times by the reset step: once $D_j$
and $D_{j+1}$ repeat from some time, one equality $D_{j+2}(t_0 + 64) = D_{j+2}(t_0)$ at a later $t_0$ gives it for every
$t \ge t_0$, because $D_{j+2}(t + 1)$ is a function of $D_j(t)$, $D_{j+1}(t)$, $D_{j+2}(t)$ (`D_step`); by induction on
$j$ the checked equalities give the periodicity for all times (on paper, not in Lean). The same holds for $g_j$ and
$A_j$, which are read from settled rows.

## What it means

**The window argument does not need a bounded period.** The period enters [SettledRuns](SettledRuns.md) only through
$P + 1$, the length of a window that forces an alternation forever; any bound $A$ on the alternations of the settled
pairs does the same, and $A = P$ always suffices. In the computed range $A = 9$ while the period grows from 16 to 32, and $A$ rose by
one when it did. The hypothesis of `black_run_le_of_settling` is not refuted at any depth, unlike that of
SettledRuns, and it has the form a slope needs: $T_j \le 3j/2 + o(j)$ and $A_j = o(j)$ for all $j$ give black runs of
slope $3/13$, against the kit's $3/5$.

**What the computed range gives.** Only the range: runs from $a \le 324{,}999$ with $13L \le 3a + 1430$, where
computation already bounds every black run by 22 (the kit's `Rule30CenterRuns` docstring, to time $10^6$). The
theorems have asymptotic content only through the open statement that the settling time is linear and the
alternations sublinear at every depth, the linear settling conjecture of [settled runs](../../findings/diagonals/settled-runs.md)
with the period freed.

**The reset bound does not give a fixed $\gamma$.** `pair_repeats_of_white_runs` reduces the settling time to the
running mean of $c_j = g_j + 1$, a property of the periodic parts alone. The mean cost rises with the period: 2.91,
3.81, 4.64 and 5.52 at periods 4, 8, 16 and 32, by 0.8 to 0.9 at each doubling, as the longest white run of a word of
$P$ fair bits grows like $\log_2 P$. On that heuristic (not a proof) the mean cost passes 6 some time after the first diagonal
of period 64, which [the records](../../findings/diagonals/left-records.md) place near depth $10^{10}$, also on a
heuristic; so the reset bound is linear only while the period is bounded, and $6j$ is not expected to hold at every
depth. The onsets themselves stay near $1.34 j$, far below the reset bound, which is $5.13 j$ at depth 199,999. This is the stop recorded in
[driven run slopes](../../negative-results/diagonals/driven-run-slopes.md): the reset bound alone does not give linear
settling.

## In Lean

`altBound_of_repeats` shifts a window by a multiple of the period with `RepeatsFrom.iter`. `black_run_window` is the
window part of SettledRuns' `black_run_le_of_settled` with $A$ in place of 16, from `black_diag`, `altPat_succ` and
`altPat_pred`. The three slope theorems choose $j$ and $s_0$ explicitly and leave the arithmetic to `omega`.
`pair_repeats_of_white_runs` is an induction on $j$ over `pair_step_white` and `pair_step_black`, with the sum
$c_1 + \dots + c_j$ as `costSum`. The axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Relation to the kit

The pinned kit bounds black runs by $L \le a$ (`Rule30CenterRuns.black_run_le`) and proves each left diagonal eventually
periodic with period dividing $2^j$ (`Rule30Diagonals.D_periodic`); its `Rule30AgedLeftDiagonals` has the reset step
for periods (`reset_first_period`, `reset_inherits`). The kit's main branch, after the pinned revision, has the slope
$3/5$ with $\log \log$ margins (`Rule30BlackRunErosion`, `Rule30SettledBarrierEffective`), a bound
$5L + 3k \le 3a + 18$ from one eventually white diagonal $k$ (`Rule30SettledBarrier.black_run_bound_at_white`), and the
eventual period $2^w$ with $w$ the number of white diagonals (`Rule30LeftReset`). Its `Rule30FrontLaw` bounds when the
diagonals settle by the same reset recursion: `frontBound` is the first black cell of $D_{j+1}$ after both earlier
onsets, and `frontBound_step_le` and `frontBound_le_periodSum` bound the onset of $D_k$ by $1$ plus the sum of the
periods of $D_0, \dots, D_{k-1}$. So `pair_repeats_of_white_runs` refines that bound, with $c_i$, one more than the
longest white run of the periodic part (at most the period), in place of the period. The barrier bound uses one
eventually white diagonal, and the white diagonals are sparse (seven below depth 200,000), so it gives no slope
below $3/5$ there. The alternation bound, the window argument with it and the conditional slopes $3/13$, $21/115$ and $15/29$ are
not in the kit at either revision.

## Reproduce

```bash
python -m computations.settled_slope --depth 200000   # both tables, about 3 min, 0.2 GB
```
