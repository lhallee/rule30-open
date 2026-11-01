---
title: Three leads to linear settling of the single cell's left diagonals stop, to depth 200,000, at the transient or at a law of large numbers for the settled left side; the onset phases are uniform, the front shows nothing at the white diagonals, and no settled pair repeats up to a time shift
category: diagonals
problems: [2]
status: negative
kind: dead-end
evidence: [computations/front_walker.py]
---

# Three leads to linear settling of the single cell's left diagonals stop, to depth 200,000, at the transient or at a law of large numbers for the settled left side; the onset phases are uniform, the front shows nothing at the white diagonals, and no settled pair repeats up to a time shift

**Question.** [SettledSlope](../../Rule30Open/Diagonals/SettledSlope.md) gives black center runs of slope $3/13$ if
every left diagonal $D_j(t) = \mathrm{cell}(t, j - t)$ of the single cell repeats from time $3j/2 + o(j)$ (its onset
$T_j$) and adjacent settled diagonals alternate in antiphase $o(j)$ times. To depth 200,000 the onsets are about $1.33j$
and never above $\lceil 3j/2 \rceil$, but the only general bound, the reset bound, charges each diagonal the longest
white run of its periodic part and reaches $5.13j$ at depth 199,999. Three leads were tested for a proof of linear
settling, with any constant:

1. **Phase.** The onset uses the gap from the earlier onsets to the next black cell of $D_j$, not the longest white run.
   Is the phase at which the reset happens constrained, so that the gap is small on average?
2. **Front.** The onsets define a front of slope about $4/3$. Does it have a self-similar structure at the depths where
   the period doubles, or a bounded rate between two white diagonals?
3. **Finite state.** Is there a bounded set of settled pairs $(D_j, D_{j+1})$ up to a time shift, or a local invariant
   of them, that bounds $T_{j+1} - T_j$ on average?

**What was done.** `front_walker` reads the onsets (with respect to the period 64) and the periodic parts of every
diagonal $j \le 200{,}000$ from 300,600 steps, as in SettledSlope, and tests each lead on them.

## Lead 1: the phase is constrained, and it is typical

**What closes.** Write $S_j = \max(T_{j-1}, T_j)$. The front law (the kit main branch's `Rule30FrontLaw.D_front_law`;
`D_periodic_of_black` of [LeftMemory](../../Rule30Open/Diagonals/LeftMemory.md)) says: from $S_j$ on, the defect
$D_{j+1}(t + 64) \oplus D_{j+1}(t)$ keeps its value while $D_j$ is white and becomes 0 at the first black cell $r$ of
$D_j$. So $T_{j+1} \le C_{j+1} = r + 1$, with equality exactly when the defect at $S_j$ is 1; if $D_j$ is white from $S_j$
(the seven white diagonals), put $C_{j+1} = S_j$, and $T_{j+1} \le S_j$. Applied to the bound
instead of the onset, this is the front walk of [FrontWalker](../../Rule30Open/Diagonals/FrontWalker.md):
$w_{j+1}$ is one more than the first black cell of $D_j$ at or after $w_j$, and the pair $(D_j, D_{j+1})$ repeats from
$w_{j+1}$, in Lean. The walk arrives on $D_j$ just after a black cell of $D_{j-1}$, so its phase is constrained:
$D_j(w_j) = \lnot D_{j-2}(w_j - 1)$ by the reset.

**The numbers.** The constraint carries no bias. The walk's step is about 2 at every period, while the reset cost
rises:

| Period | Diagonals | Mean step of the walk | Uniform phase | Mean reset cost $c_j$ |
|---:|---:|---:|---:|---:|
| 8 | 668 | 2.061 | 1.977 | 3.813 |
| 16 | 87,119 | 2.014 | 2.001 | 4.642 |
| 32 | 112,131 | 2.009 | 2.000 | 5.524 |

So $w_{200{,}000} = 402{,}228$, and $w_{j+1} \le \lceil 41j/20 \rceil + 1$ for every $j < 200{,}000$. The residues of
the walk modulo the period are uniform: $\chi^2 = 10.4$ and 8.0 modulo 16 (15 degrees of freedom) on depths 400 to
53,206 and 53,207 to 87,866, and 18.9 modulo 32 (31 degrees of freedom) on depths 87,867 to 199,999. So are the onsets:
13.5, 24.7 and 41.1. The steps are close to one plus a geometric variable of parameter $1/2$ (49.31% of them are 1,
mean 2.0113 with standard error 0.0032), the gap to the next black cell in a sequence of fair coins.

**Where it stops.** Two places.

- *The settled side gives the walk and no less.* Each onset is either $C_{j+1}$ (defect 1, for 54.58% of the depths,
  with or without the seven white diagonals) or at most $S_j$ (defect 0); the bit is 1 exactly when $D_{j+1}$ has not settled by $S_j$, so it compares a value of
  the transient of $D_{j+1}$ with the periodic part, and the settled parts do not determine it. With the bits unknown the front law cannot bound $T_{j+1}$ below $C_{j+1}$, and iterated it
  gives $w_j$, about $2.01j$. The onsets reach $1.33j$ because about 45% of the bits are 0: $T_{j+1} - S_j$ ranges from
  $-17$ to 16 (mean 0.733), and $T_{j+1} - T_j$ from $-17$ to 23. A bound below slope 2, such as the $3j/2$ of
  SettledSlope, has to control the transient.
- *The walk needs a law of large numbers.* Its mean step is an average of the gap at a phase that the walk itself
  sets, along the depths. No local argument bounds it: the largest sum of $m$ consecutive steps past depth 400 is 18,
  25, 44, 67, 111, 188, 323 and 2,226 for $m = 1, 2, 8, 16, 32, 64, 128$ and 1,024, so a bound read off windows of 8
  steps is 5.5 per step, no better than the reset cost, and even windows of 1,024 steps allow 2.17. A proof that the
  mean stays below $41/20$ must show that the cells the walk reads are close to fair on average over all depths, a
  statement of the same kind as the densities of Problem 2, here for the settled left side.

## Lead 2: the front has no visible structure at the white diagonals

The onsets advance at the same mean rate on both sides of each white diagonal, and so does the walk (2,000 depths on
each side; for 399, from depth 1):

| White diagonal | Mean $T_{j+1} - T_j$ before | after | Mean walk step before | after |
|---:|---:|---:|---:|---:|
| 399 | 1.2563 | 1.3155 | 1.9648 | 1.9700 |
| 53,207 | 1.3425 | 1.3475 | 1.9505 | 2.0790 |
| 58,286 | 1.3230 | 1.3140 | 1.9470 | 1.9750 |
| 87,866 | 1.3425 | 1.2995 | 2.0760 | 1.9920 |

Over whole regimes the mean onset increment is 1.2762 on depths 8 to 399, 1.3373 on 400 to 53,206 (period 16), 1.3332
on 53,207 to 87,866 (period 16) and 1.3257 on 87,867 to 199,999 (period 32). In space-time the front sits at
$x = j - T_j \approx -T_j/4$: it is the left edge of the chaotic region, and its rate does not change when the period
doubles. **Where it stops.** A doubling changes only the periodic parts behind the front, and the front does not see
it, so there is nothing to renormalize at these depths. A rate for the front between two white diagonals is lead 1's
question for the onsets, and stops at the transient.

## Lead 3: no settled pair repeats up to a time shift

Between two white diagonals the settled pair $(D_{j+1}, D_{j+2})$ is a function of $(D_j, D_{j+1})$ (the reset), and
$(D_j, D_{j+1})$ is a function of $(D_{j+1}, D_{j+2})$ (solve the rule for $D_j$), so the depth acts as an injective map
on pairs of periodic words; the kit's main branch uses this injectivity to prove the periods unbounded
(`Rule30LeftUnbounded`). Counted up to a time shift, which is what a finite set of pair types would need:

| Depths | Period | Pairs | Types up to a time shift |
|---|---:|---:|---:|
| 400 to 53,205 | 16 | 52,806 | 52,806 |
| 53,208 to 58,284 | 16 | 5,077 | 5,077 |
| 58,287 to 87,864 | 16 | 29,578 | 29,578 |
| 87,867 to 199,998 | 32 | 112,132 | 112,132 |

Every pair is new. On the walk the same holds for any coarser local state: every pair of consecutive steps $(a, b)$ with
$a, b \le 6$ occurs at least 49 times, and the fraction of steps of 1 after a step of $k$ is between 0.475 and 0.502
for every $k$, so no step pattern is excluded. **Where it stops.** A finite-state certificate would be a bounded set of
types closed under the depth step; there is none to find in this range, and a potential on pair types that bounds
the mean step would have to be certified along an orbit that never returns.

## What it means

The available tools (the reset and the front law, the skeleton map on settled pairs, and the injectivity that makes
periods unbounded) reduce linear settling to two inputs, and neither comes from them:

- **Slope 2 from the settled side.** [FrontWalker](../../Rule30Open/Diagonals/FrontWalker.md) proves in Lean that the
  walk bounds the onsets and that a walk of slope $41/20$ (any constant would do) gives black runs of slope $63/185$.
  What is missing is a law of large numbers for the settled left side along the walk: the walk's mean step stays
  below a constant. The data fit 2.011, and the fair-coin heuristic makes it about 2 at every period, unlike the reset
  cost, but nothing proves it.
- **Below slope 2 from the transient.** The $3/13$ of SettledSlope needs onsets near $3j/2$, which needs the defect
  bits, set where $D_{j+1}$ is still chaotic. The front at $x \approx -t/4$ is the edge of the chaotic region, so
  bounding it is a statement about how fast the chaotic region spreads left, which nothing here touches.

This refines the stop recorded in [driven run slopes](driven-run-slopes.md): there the reset bound was the only general
tool and its mean cost grows with the period; the front walk removes the growth from the bound but leaves its average
open.

## Reproduce

```bash
python -m computations.front_walker --depth 200000   # every number here, about 3 min, 0.2 GB
```
