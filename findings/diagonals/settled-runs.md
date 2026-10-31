---
title: A linear settling time of the left diagonals with periods o(j) would cut the slope of center-column runs to 3/13 (black) and 1/3 (white) at settling time 3j/2; depths 8 to 7,999 repeat with period 16 from time 3j/2 to time 12,583
category: diagonals
problems: [2]
status: conjecture
formalization: partial
evidence: [computations/diagonal_cones.py, computations/projections.py]
---

# A linear settling time of the left diagonals with periods o(j) would cut the slope of center-column runs to 3/13 (black) and 1/3 (white) at settling time 3j/2; depths 8 to 7,999 repeat with period 16 from time 3j/2 to time 12,583

**Conjecture (linear settling).** There is $\gamma$ such that every left diagonal $D_j(t) = \mathrm{cell}(t, j - t)$
of the single cell repeats with a period $P(j)$ from time $\gamma j$ on, with $P(j) = o(j)$ (the period is a power of
two). The data below fit $\gamma = 3/2$. Under it, the window argument below gives, since it needs only $P(j) + 1$
consecutive times inside the forced pattern:

- a black run of the center column from time $a$ has length at most $\left(\frac{3(\gamma - 1)}{5\gamma - 1} +
  o(1)\right) a$, which is $(3/13 + o(1))\,a$ at $\gamma = 3/2$, against $L \le a$ in the pinned kit
  (`Rule30CenterRuns.black_run_le`) and $5L + 18\lfloor \log_2 \log_2 a \rfloor \le 3a + 51$ in kit pull request #46
  (`Rule30BlackRunErosion`, merged after the pinned revision; see [the kit pull requests](../../literature/kit-pull-requests.md));
- a white block of row $a$ reaches at most $(1 - 1/\gamma + o(1))\,a$ cells left of the center, which is
  $(1/3 + o(1))\,a$ at $\gamma = 3/2$, and at $\gamma = 3/2$ a white run of the center column has length at most
  $(1/3 + o(1))\,a$ (derived in [Structure of white runs](#structure-of-white-runs), not formalized).

[The Lean module](../../Rule30Open/Diagonals/SettledRuns.md) proves the black-run and white-block bounds for the fixed
period 16 at $\gamma = 3/2$ up to a finite depth $J$; that case has no asymptotic content (see the module).

The unconditional bounds stay at slope $3/5$ for black runs and $1$ for white runs. The hypothesis is not proved. The
pinned kit proves each left diagonal eventually periodic with period $2^j$ (`Rule30Diagonals.D_periodic`), without a
bound on the onset in its statement. A fixed period cannot hold for all depths: the left-diagonal periods are unbounded
(Nersissian 2026, in [the literature](../../literature/rule-30.md)), and the period becomes 32 at depth 87,867
([the records](left-records.md)).

## Evidence

Direct check of the Lean hypothesis, $D_j(t + 16) = D_j(t)$ for $8 \le j \le 7{,}999$ and
$\lceil 3j/2 \rceil \le t \le 12{,}583$ (so that $t + 16$ stays in a table of 12,600 steps): no violation. This is a
check over a finite window. Since $D_{j+2}(t + 1)$ is a function of $D_j(t)$, $D_{j+1}(t)$ and $D_{j+2}(t)$
(`D_step`), one equality $D_{j+2}(t_0 + 16) = D_{j+2}(t_0)$ at a time $t_0$ from which $D_j$ and $D_{j+1}$ repeat with
period 16 gives it for every $t \ge t_0$; by induction on $j$ the check would give period 16 from time
$\lceil 3j/2 \rceil$ for all later times and $8 \le j \le 7{,}999$, once diagonals 6 and 7 are shown to repeat with
period 16 from time 12, which the code does not check. The settling constants of the true orbit at depths up to 1,499 (3,600 steps, a 256-step window):

| Depths | Largest onset / depth | At depth | Largest period |
|---|---:|---:|---:|
| $\ge 8$ | 1.4792 | 48 | 16 |
| $\ge 100$ | 1.4112 | 107 | 16 |
| $\ge 400$ | 1.3150 | 1,492 | 16 |

Every ratio is below $3/2$. Over depths $\ge 400$ the largest ratio sits at the edge of the table (depth 1,492 of
1,499), so in this range it rises slowly with depth and does not fall. Every observed period is 1, 2, 4, 8 or 16.
A streamed check reaches further (`onsets` in [projections.py](../../computations/projections.py)): over $2^{17}$
steps, every depth $8 \le j < 80{,}000$ repeats with period 16 from its onset to time $2^{17} - 16$, and no onset
exceeds $\lceil 3j/2 \rceil$, so the hypothesis holds in that window. The settling constants there:

| Depths | Largest onset / depth | At depth | Median onset / depth |
|---|---:|---:|---:|
| 4,096 to 8,191 | 1.3397 | 8,117 | 1.3302 |
| 8,192 to 16,383 | 1.3432 | 15,424 | 1.3356 |
| 16,384 to 32,767 | 1.3455 | 28,584 | 1.3407 |
| 32,768 to 65,535 | 1.3421 | 32,780 | 1.3367 |
| 65,536 to 79,999 | 1.3397 | 70,950 | 1.3373 |

The ratios stay near $4/3$ and do not rise toward $3/2$ in this range. Depths from 80,000 on are untested, among them
the white diagonal at 87,866 ([the records](left-records.md)).

## What the hypothesis gives

Both bounds come from the time window in which a pattern forced by the run meets two adjacent diagonals that have
already settled.

- **Black run.** A black run of length $L$ from time $a$ forces, at time $a - s$, the alternating pattern (black on
  even $-x$) on the cells $-(L - 1) - s .. -4s$, and nothing more (checked by enumerating every preimage for runs of 12
  and up to three steps back). Two adjacent diagonals inside that trapezoid for $P + 1$ times in a row alternate in
  antiphase; settled, they alternate forever, and the alternation propagates down to $D_0$, which is always black.
- **White block.** White cells $-m .. \ell$ of row $a$ force the white triangle below; two adjacent diagonals inside it
  for $P$ times stay white forever, and again reach $D_0$.

The longest run that the window argument cannot exclude, for $P = 16$ and diagonals from $j = 8$ on, at
$\gamma = 1.48$ (a count of the windows that the model leaves open; it uses no orbit data: settling time $\gamma j$ and
period 16 are assumed for every $j \ge 8$, and the white model uses the row-$a$ structure of white runs, the kit's
`row_at_start`):

| $a$ | Longest open black run | Ratio | Longest open white run | Ratio |
|---:|---:|---:|---:|---:|
| 500 | 147 | 0.294 | 276 | 0.552 |
| 1,000 | 258 | 0.258 | 438 | 0.438 |
| 2,000 | 483 | 0.242 | 762 | 0.381 |
| 4,000 | 933 | 0.233 | 1,411 | 0.353 |

The ratios fall toward the predicted slopes 0.225 (black) and 0.324 (white) at $\gamma = 1.48$. The formulas by
$\gamma$:

| $\gamma$ | 1.35 | 1.5 | 2 | 2.5 | 5 | $\infty$ |
|---|---:|---:|---:|---:|---:|---:|
| Black slope $3(\gamma - 1)/(5\gamma - 1)$ | 0.183 | 0.231 | 0.333 | 0.391 | 0.500 | 0.600 |
| White slope $1 - 1/\gamma$ | 0.259 | 0.333 | 0.500 | 0.600 | 0.800 | 1.000 |

## Structure of white runs

For a maximal white run of the center column from time $a \ge 3$, let $\ell$ be the number of white cells right of the
center in row $a$, $L$ the run length and $m = \min(\ell, L - 1)$. In every run with $a < 6000$ (1,486 runs; 346 with
$a < 1500$), with no exception:

- row $a$ is white on $-m .. \ell$, and row $a - 1$ is black on $-m - 1 .. \max(\ell - 1, 0)$;
- if $\ell + 1 < L - 1$, cell $-(\ell + 1)$ of row $a$ is black, and cell $-k$ is black exactly for odd $k$ from
  $\ell + 2$ to $L - 1$;
- $L + 2\lfloor (a - \ell - 3)/5 \rfloor \le a$.

The shape of row $a$ left of the center in the first two lines (white on $-m .. 0$, black at $-(\ell + 1)$, then black
exactly at odd $k$ out to $L - 1$) is the pinned kit's `Rule30CenterRuns.row_at_start` for some $\ell$. The computation
adds that this $\ell$ is the number of white cells right of the center; that, the claim about row $a - 1$ and the last
line are numerical checks.

With the window argument, the kit's row shape bounds white runs. Under period $P$ from time $3j/2$, the alternating
tail on $-(L - 1) .. -(\ell + 2)$ erodes as the trapezoid behind a black run does (`erode_alt`, translated), and two
adjacent diagonals meet it in $P + 1$ settled times, which is excluded, unless $13L \le 3a + 4\ell + O(P)$. The white
block excludes $m \ge a/3 + O(P)$. If $\ell < a/3 + O(P)$, the first bound gives $L \le a/3 + O(P)$; otherwise
$m = \min(\ell, L - 1)$ forces $L - 1 < a/3 + O(P)$. So a white run has length at most $a/3 + O(P)$, the slope
$1 - 1/\gamma$ at $\gamma = 3/2$ that the white column of the table approaches. This is not formalized: the Lean module
proves only the white-block bound.

## Where the argument stops

The only missing input is the linear settling time with a period $o(j)$ for all depths. Direct comparison cannot
supply it: [fixed-depth strips](../../negative-results/diagonals/fixed-depth-strips.md) show that comparing the forced
cone with a true strip of the pattern near the left edge, without propagating the rule, gains only a constant, so the
slope stays $3/5$.

## Reproduce

```bash
python -m computations.diagonal_cones --depth 1500 --steps 3600 --window 256
python -m computations.projections front   # depths below 80,000 over 2^17 steps, about 1 min
```

The command prints the settling table and the slopes by $\gamma$ in about 6 s. The longest-open-run counts are
`longest_open_black` and `longest_open_white` in [computations/diagonal_cones.py](../../computations/diagonal_cones.py),
and `white_run_violations(6000)` checks the white-run structure. The command also prints `settled_violations`, the number of diagonals $j \ge 8$ that break the Lean hypothesis;
`--depth 8000 --steps 12600` gives 0.
