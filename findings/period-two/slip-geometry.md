---
title: The slips of the right channel are one front crossing a locked layer, fed from the chaotic region at the leftward speed of Rule 30
category: period-two
problems: [1]
status: computed
formalization: not-applicable
evidence: [computations/slip_geometry.py]
---

# The slips of the right channel are one front crossing a locked layer, fed from the chaotic region at the leftward speed of Rule 30

Drive the empty right half with an alternating center, white at the even steps (the other phase gives the same column
one step later). Column 1 nearly repeats $AAAB$ of 36 steps and slips about once per 145 steps
([the right channel](right-channel.md)). Followed in space and time, over 200,000 to 1,000,000 steps, each slip is the
same event: a front that closes a thin locked layer next to the center and crosses it along one fixed path. The
front is set off at the far edge of the layer by what arrives from the chaotic region beyond it, and that information
travels leftward at about a quarter of a column per step, the speed at which damage spreads leftward in Rule 30;
256 steps back, column 1 uses less than a third of its light cone. A window of up to 32 columns with a white edge
locks. Where the slips fall looks like coin flips:
the number of $AAAB$ blocks between slips is geometric with no serial correlation detected, and a window of 48 to 64
columns fed by fair coin flips at its right edge has the same slips as the true half.

## Result

All counts are for the empty right half from step 0; the *lock depth* at step $t$ is the number of columns $1, 2, \dots$
equal to themselves 36 steps earlier before the first that is not.

- **The symbolic form.** The empty half is in the gap trap from step 293 ([the gate census](gate-census.md), the kit's
  `u_empty_gaps`), so at the white steps the black cells of column 1 come 3 or 5 white steps apart. From step 1,000 to
  1,000,000 there are 17,734 gaps of 3 and 89,259 of 5, and no two gaps of 3 are adjacent. So column 1 at the white
  steps is a sequence of runs: a gap of 3 followed by $n \ge 1$ gaps of 5. $AAAB$ is $n = 3$ repeated (18 white steps);
  a slip is a run with $n \ne 3$. Of 17,733 runs, 10,817 (61%) have $n = 3$; the others take $n = 1$ (218), 4 (329),
  5 (1,915), 7 (927), 9 (982), 10 (691), 11 (440) and other values up to 39.
- **The locked layer.** Over steps 2,000 to 200,000 the lock depth has median 7, 95th percentile 16, and maximum 35;
  beyond it the diagram is chaotic. The layer is neither the stripe nor the ether: stripe cells (constant for a step,
  unlike both neighbors) are 21.5% of the layer, 18.8% beyond it and 18.7% of diagrams of random rows, and ether cells
  (a 3 by 3 block of cells each repeating after 4 steps and 7 columns) 0.09%, 0.27% and 0.29%.
- **One front.** Over the last 15 steps before a slip the lock depth follows the same trace before every one of the
  1,372 slips of 200,000 steps: $6, 5, 6, 5, 4, 5, 4, 5, 4, 3, 2, 3, 2, 1, 0$. Over the last 21 steps it has 4
  traces, the commonest (1,065 slips) starting at depth 10, so the front crosses the layer at half a column per step
  (median slope $-0.500$, quartiles $-0.516$ and $-0.464$, from the last maximum of the depth in the 40 steps before
  the slip).
- **Set off at the edge of the layer.** Keep the layer and the 3 columns beyond it at a step $k$ steps before a slip,
  and replace every other column by fresh random bits: in all 32 draws column 1 still slips at the same step for every
  one of 150 slips at $k \le 16$, for 98% at $k = 18$ and 20, 85% at 24 and 50% at 28 (with 5 columns beyond the
  layer: every slip to $k = 20$, 99% at 24). So a slip is decided about 20 steps ahead, when the front is about 10
  columns out, and the cells beyond the layer then decide it.
- **Information arrives at about speed 1/4.** Let $X(k)$ be the least $X$ such that replacing every column right of $X$
  by random bits, $k$ steps before a step $s$, leaves column 1 unchanged from $s - k$ to $s$ in 48 draws. For 40
  slips and $k = 8, 16, 32, 64, 128, 256$ the median $X(k)$ is 5, 9, 17, 28.5, 48 and 78.5 (largest 104 at
  $k = 256$); for 40 random steps it is 4, 7, 13, 24.5, 41 and 79.5. The median grows like $0.26\,k$ from $k = 64$ to
  256 (0.29 at the random steps), against 0.247 for the left edge of the damage of one flipped cell in uniform random
  rows (200 rows of 2,048 cells, steps 200 to 400). The light cone allows $X(k) = k + 1$; at $k = 256$ column 1 uses
  less than a third of it.
- **The layer alone locks; generic noise makes the slips.** Run columns 1 to $W$ alone, with the column right of $W$
  white or fair coin flips (400,000 steps; the true half has one slip per 144.1 steps there). With a white edge and $W =
  8, 12, 16, 24, 32$ column 1 ends periodic (period 10, or 14 with gaps of 2 and 5 at the white steps) and never slips
  again; at $W = 20$ and 48 it keeps slipping, but with gaps far from the true law (Kolmogorov-Smirnov distance 0.60 and
  0.23). With coin flips the slips appear, and their law approaches the true one as $W$ grows: one per about 450, 235,
  153, 149, 151, 146 and 145 steps at $W = 8, 12, 16, 20, 24, 32, 48$, with a two-sample Kolmogorov-Smirnov distance
  between the gaps of 0.50, 0.26, 0.11, 0.06, 0.06, 0.025 to 0.045 and 0.013 to 0.023 (p 0.48 to 0.98 at $W = 48$ and
  0.75 to 0.83 at 64, three seeds each), and the same for the runs $n$. One of the three runs at $W = 32$ entered the
  lock of period seven ([SevenLock](../../Rule30Open/PeriodTwo/SevenLock.md)) before the gap trap and never slipped. A
  window of 64 columns with a white edge, a finite deterministic system, also matches (distance 0.026, p 0.32): the
  window makes enough chaos by itself.
- **When the slips come.** Over 1,000,000 steps the stretches of $n = 3$ between slips number 4,520 and have mean 2.39
  blocks of 36 steps; their law is within 0.006 of a geometric law (largest gap between the two distribution functions)
  and consecutive stretches are uncorrelated (Spearman $|\rho| \le 0.024$ at lags 1 to 5, permutation p at least 0.12).
  Counted as clusters of steps where column 1 differs from itself 36 steps earlier (joined when fewer than 36 steps
  apart), there are 6,852 slips, at least 46 and at most 692 steps apart, quartiles 92, 128 and 178, coefficient of
  variation 0.53; consecutive gaps have Spearman $|\rho| \le 0.031$ at lags 1 to 5, the largest at lag 5 (p 0.0065,
  0.03 after the five lags). So the slip times are close to a renewal process whose lock lasts a geometric number of
  blocks, as if a coin decided at each block whether the lock survives (probability 0.58). The runs themselves are not
  independent: the table of consecutive pairs $(n_i, n_{i+1})$ has chi-square 1,443 against 1,000 shuffles (p 0.001,
  the least the test can give), and so does the table of locked or not (89.9, p 0.001); the shape of a slip depends on
  the one before, the time to the next one does not, to this precision.

## Method

The right half is the integer whose bit $i$ is cell $i + 1$, one step $R \mapsto ((R \ll 1) \mid c) \oplus
(R \lor (R \gg 1))$ with center bit $c$, cut back every 4,096 steps to the bits that column `width` can still feel
before the end of the run; 1,000,000 steps of column 1 take about a minute. The test checks the run against a direct
run of the rule, against `right_half.column_one`, and against the 826 slips in 120,000 steps of the right-channel
finding. The reach $X(k)$ is a binary search over $X$ with 48 random completions; it bounds from below the columns
column 1 depends on, since a dependence that few completions expose can be missed.

## What it means

The slips do not need information from far away: column 1 is fed through a layer of about 16 columns, the width of the
gap trap, which without input locks, and what drives it across that layer is generic: a coin at column 33 to 65 does as
well as the true right half. The far right half matters only through the chaotic region next to the layer, whose
information comes in at the leftward speed of Rule 30. So the right channel behaves like a finite-state transducer
from a nearly random column to column 1, with a positive rate of slips because every block gives the lock a fixed
chance to break.

For a proof this is a picture, not a lever. That column 1 never locks is the statement that the chaotic region keeps
delivering the patterns that set off the front, forever; that is a statement about the chaotic region of the same
kind as the problem, as with entry into a trap ([the gate census](gate-census.md), [the absorption
route](../../negative-results/period-two/absorption-route.md)). The renewal form and the geometric lock times are
heuristic properties of a deterministic orbit, established only as far as these tests reach. The window runs also show
the opposite risk: a window with random input can fall into the lock of period seven, which the true half, inside the
gap trap from step 293, never can.

## Reproduce

```bash
python -m computations.slip_geometry --steps 1000000             # symbolic form, slip statistics, renewal tests
python -m computations.slip_geometry --steps 200000 --fronts     # layer, front traces, decision ahead of a slip
python -m computations.slip_geometry --steps 200000 --reach      # X(k) and the leftward damage speed
python -m computations.slip_geometry --steps 400000 --windows    # windows with a white or coin-flip edge
```

The first takes about a minute, the others a few minutes each.
