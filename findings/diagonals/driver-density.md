---
title: Over every center column that the left half allows, the most black cells among c(0..T) is 141 at T = 190 exactly and at least 2,254 at T = 3,000, a rate near 3/4; chaining dense periodic words does not raise it, and a long stretch is mostly followed by a gap of comparable length
category: diagonals
problems: [2]
status: conjecture
formalization: wanted
evidence: [computations/driver_density.py]
---

# Over every center column that the left half allows, the most black cells among c(0..T) is 141 at T = 190 exactly and at least 2,254 at T = 3,000, a rate near 3/4; chaining dense periodic words does not raise it, and a long stretch is mostly followed by a gap of comparable length

**Setting.** $\Lambda_L$ is the set of drivers $c(0) = 1, c(1), c(2), \ldots$ such that, with the left half $x$
(columns $\le -1$) driven by $c$ from white, $c(t + 1) = \lnot x_{-1}(t)$ whenever $c(t) = 1$; after a white center
the next value is free. This is the left-only constraint of [driven left runs](driven-left-runs.md#the-left-only-constraint):
since $c(t + 1) = x_{-1}(t) \oplus (c(t) \lor x_1(t))$, it needs no right half, and the single cell's center column
lies in $\Lambda_L$. Write $M(T)$ for the largest number of black cells among $c(0), \ldots, c(T)$ over
$c \in \Lambda_L$.

**Conjecture $S_B$.** There are $\rho < 1$ and $C$ such that $M(T) \le \rho T + C$ for every $T$. The measurements
below put the least such $\rho$ near $3/4$ (a heuristic reading: they bound nothing past $T = 190$). Since the single
cell's center column lies in $\Lambda_L$, $S_B$ would give its white cells lower density at least $1 - \rho$, about
$1/4$, against the logarithmic counts the kit proves. It says nothing about black cells: $1, 1, 0, 0, 0, \ldots$ lies
in $\Lambda_L$ ($c(1)$ and $c(2)$ are forced, the rest free), so a lower density of black cells needs the right half.

## The maxima

`driver_dp` runs a dynamic program over the reachable states (left half at time $t$, $c(t)$), keeping for each the
largest count of black cells over the drivers that reach it. It agrees with enumeration of every admissible driver
for $T \le 12$, the single cell's count lies below it, and an optimal driver it returns is admissible (`tests/`).

| $T$ | states | $M(T)$ | $M(T)/(T+1)$ |
|---:|---:|---:|---:|
| 60 | 3,580 | 44 | 0.7213 |
| 100 | 96,293 | 73 | 0.7228 |
| 120 | 373,726 | 88 | 0.7273 |
| 140 | 1,282,375 | 103 | 0.7305 |
| 160 | 4,575,350 | 119 | 0.7391 |
| 170 | 8,475,028 | 126 | 0.7368 |
| 180 | 15,303,915 | 133 | 0.7348 |
| 190 | 26,979,741 | 141 | 0.7382 |

The ratio is not monotone: on the multiples of 5 from 60 to 190 it lies between 0.7143 ($T = 90$) and 0.7410
($T = 165$). Past $T = 190$ the count is a lower bound: a beam that keeps the 60,000 states with the largest counts
equals $M(T)$ at every multiple of 5 up to 190, and gives

| $T$ | 500 | 1,000 | 1,500 | 2,000 | 2,500 | 3,000 |
|---|---:|---:|---:|---:|---:|---:|
| beam count | 373 | 749 | 1,125 | 1,503 | 1,878 | 2,254 |
| ratio | 0.7445 | 0.7483 | 0.7495 | 0.7511 | 0.7509 | 0.7511 |

The gain per 100 steps lies between 73 and 78 from $T = 100$ to 3,000 and averages 75.25 from $T = 1{,}000$ to 3,000.
A beam four times wider (240,000 states) gives the same count at every multiple of 100 up to 1,000. The greedy driver,
black whenever the value is free, reaches only 0.6711 at $T = 3{,}000$.

**Windows from any reachable state.** $G(s, T)$, the most black cells among $c(s), \ldots, c(T)$ from any state
reachable at time $s$, bounds every driver's gain on $[s, T]$, so $M(T) \le M(s) + G(s, T)$. Exactly:
$G(60, 120) = 49$ and $G(90, 180) = 74$ (ratios 0.803 and 0.813 over the $s + 1$ cells), $G(60, 190) = 102$,
$G(120, 190) = 59$. The excess over $3/4$ of a window of 41 cells grows with its start: $G(s, s + 40) - 30.75$ is
2.25, 4.25 and 6.25 at $s = 60, 90, 120$. So the rate from an arbitrary reachable state is not the rate from the start:
some states at time $s$ hold a dense future whose length grows with $s$ (a black run alone lasts up to $R_B(s)$, about
$0.14 s$, by [driven left runs](driven-left-runs.md)), and what makes $S_B$ plausible is that reaching them costs white
cells. A proof of $S_B$ therefore has to charge that cost (an amortization); a bound uniform over the reachable states,
with a constant independent of $s$, is false as soon as $R_B$ is unbounded.

## Dense words and their lifetimes

For a periodic word $w$, $l_w(t)$ is the most letters $c(t), c(t + 1), \ldots$ that a driver in $\Lambda_L$ takes from
$w$ in phase, over every reachable state at time $t$ and every phase (`follow_lengths`, checked against cell-by-cell
simulation of single drivers and against enumeration at $t = 9$). For all 24 primitive words of period at most 8 with
at least $3/5$ of their letters black, at $t = 10, 20, \ldots, 170$:

| $w$ | density | $l_w(60)$ | $l_w(100)$ | $l_w(140)$ | $l_w(170)$ | fitted slope on $[60, 170]$ |
|---|---:|---:|---:|---:|---:|---:|
| 1 | 1 | 12 | 16 | 18 | 23 | 0.099 |
| 110 | 0.667 | 18 | 28 | 32 | 36 | 0.190 |
| 1110 | 0.750 | 18 | 23 | 28 | 32 | 0.131 |
| 11010 | 0.600 | 20 | 31 | 44 | 39 | 0.198 |
| 11110 | 0.800 | 16 | 20 | 30 | 39 | 0.170 |
| 111110 | 0.833 | 18 | 24 | 33 | 35 | 0.135 |
| 1111110 | 0.857 | 16 | 23 | 27 | 31 | 0.122 |
| 11111110 | 0.875 | 16 | 23 | 25 | 28 | 0.117 |

Over all 24 words the fitted slopes lie between 0.099 and 0.198 and $l_w(170)/170$ between 0.135 and 0.265; the
largest value is $l_{110}(150) = 49$. For the five words of density at least $0.8$, $l_w(t) \ge t/2$ only at $t = 10$
and 20 (7 and 14 letters); from $t = 30$ the ratio is at most 0.467, from $t = 40$ at most 0.375 and from $t = 60$ at
most 0.30. The black letters of the longest stretch track the size of the reachable set: their number over
$\log_2 N(t)$, with $N(t)$ the number of reachable states, lies between 0.84 and 1.66 at $t = 60, 70, \ldots, 170$ (a
heuristic reading: each black letter imposes one forced value, which behaves like a fair bit, as the black runs do in
[driven left runs](driven-left-runs.md#long-runs-against-fair-bits-a-heuristic)). On this range $\log_2 N(t)$ grows
linearly, by about 0.10 per step (least squares on $t = 60, 70, \ldots, 170$), and so do the lifetimes.

**Re-entry.** A longest $w$-stretch from time $t$ ends at a state at time $t + l_w(t)$ whose center is forced off $w$;
there are one to three such end states over all the reachable states and phases that attain $l_w(t)$. From each,
`reentry` finds by breadth-first search the least number of further steps after which some state again has
$l_w \ge \lceil l_w(t)/2 \rceil$, and $g$ is the least of these over the ends, with the most black cells a driver puts
in those steps (checked against a separate search over integer-coded states in `tests/`). Entries are $l_w(t)$ / $g$ /
the density of the stretch and the gap together (">40": no end reaches such a state within 40 steps).

| $w$ | density | $t = 40$ | $t = 80$ | $t = 120$ | $t = 160$ |
|---|---:|---|---|---|---|
| 110 | 0.667 | 15 / 11 / 0.50 | 26 / 9 / 0.60 | 28 / 18 / 0.59 | 39 / 25 / 0.62 |
| 1110 | 0.750 | 14 / 11 / 0.64 | 22 / 27 / 0.69 | 27 / 22 / 0.67 | 32 / 33 / 0.65 |
| 11110 | 0.800 | 12 / 1 / 0.77 | 19 / 17 / 0.64 | 28 / 24 / 0.67 | 31 / 35 / 0.71 |
| 111110 | 0.833 | 15 / 8 / 0.74 | 24 / 11 / 0.74 | 27 / 40 / 0.67 | 31 / >40 |
| 11010 | 0.600 | 23 / 2 / 0.60 | 25 / 19 / 0.57 | 31 / 24 / 0.56 | 42 / 39 / 0.59 |
| 1111110 | 0.857 | 14 / 4 / 0.72 | 19 / 8 / 0.74 | 23 / 18 / 0.76 | 26 / 6 / 0.81 |
| 11111110 | 0.875 | 13 / 2 / 0.73 | 18 / 6 / 0.71 | 25 / 23 / 0.69 | 30 / >40 |

At $t = 40$ some gaps are short (1 and 2 steps). At $t = 120$ the gap is at least half the stretch for every word, 0.64
to 1.48 times its length, and at $t = 160$ for every word but 1111110, which re-enters 6 steps after one of its three
stretch ends (the other two need 25 and 36). So a long stretch is mostly followed by a gap of comparable length: from
one state the reachable set has to grow again before a state with a long stretch appears in it. Stretch and gap
together have density 0.50 to 0.81; the one value above 0.8 is that short re-entry, and the next stretch it reaches is
only guaranteed half as long.

**Chaining.** `chain_beam` keeps 20,000 states and adds, from each kept state, a jump to the end of every maximal
stretch of at least 8 letters of 110, 1110, 11110, 111110, 11010, 1111110 or 11111110, so dense stretches survive even
when their intermediate states would leave the beam. It gives exactly the plain beam's count at every multiple of 100
up to $T = 1{,}000$ (749, ratio 0.7483).

## The optimal drivers

`describe` reads off the run lengths. The optimal driver at $T = 160$ (119 black cells) has black runs of mean 3.22
(13 of length 1, longest 12) and white runs of mean 1.17 (30 of length 1, 6 of length 2). The beam's driver at
$T = 3{,}000$ has 2,254 black cells in black runs of mean 3.70 (165 of length 1, 92 of length 2, longest
20) and white runs of mean 1.23 (491 of length 1, 102 of length 2, 16 of length 3,
1 of length 4). Of its 747 white cells, 610 are forced by a black cell before them and 137 are chosen after a white
one. Each black run lasts exactly as long as the alternating right end of the left half at its start allows (the
identity of [driven left runs](driven-left-runs.md#the-reduction-paper-every-step-a-kit-lemma), checked on every
complete run). So the optimal drivers are not chained periodic words: they take black whenever it is free, except about
one free cell in five, and the rate is set by the mean length of the alternating domains that the left half offers at
the run starts, about 3.7 against white gaps of about 1.2.

## What it means

- **No sign of a rate toward 1.** The beam's gain stays at 73 to 78 per 100 steps and its ratio at 0.7511 by
  $T = 3{,}000$, below 0.8; the only lifetimes of dense words reaching $t/2$ are the additive constants at $t \le 20$;
  the chaining beam does not beat the plain beam. So $S_B$ survives with $\rho$ near $3/4$, and the data give no sign
  of a density rising toward 1.
- **Why chaining does not help (heuristic).** A stretch of a dense word from time $t$ is as long as the reachable set
  at $t$ is large, about $\log_2 N(t)$ forced values that come out right, and the end of a stretch is a single state,
  from which a long stretch is again available only after the reachable set has regrown, which at $t \ge 120$ mostly
  takes a gap of comparable length (one exception in 14 in the table). The same mechanism bounds the black runs in
  [driven left runs](driven-left-runs.md).
- **What a proof needs.** The quantity is a growth rate over a set of drivers that a finite automaton does not
  describe ([finite-state slopes](../../negative-results/diagonals/finite-state-slopes.md)), and a potential over a
  fixed basis of 27 row features certifies only $12/13$ even on the graph it is fitted to
  ([driver-density potentials](../../negative-results/diagonals/driver-density-potential.md)). As the windows above
  show, a proof has to charge the cost of reaching a state with a dense future to the white cells spent on the way.
- **The kit.** Neither the pinned kit nor its main branch (at commit 93d98bb) states a density over drivers: its
  density statements (`Rule30P2Bridge`, `BlackTimes`, `ProblemTwo`) are about the center column itself, and
  `Rule30DrivenLeft`, `CoupledHalves`, `Rule30CenterRuns` and `Rule30SettledBarrierEffective` bound runs and settling,
  not counts over drivers.

## Reproduce

```bash
python -m computations.driver_density exact --steps 190 --every 5 --forks 60,90,120   # about 7 min, 4 GB
python -m computations.driver_density beam --steps 3000 --width 60000 --track        # about 11 min
python -m computations.driver_density beam --steps 1000 --width 240000               # about 5 min
python -m computations.driver_density lifetimes --steps 170 --every 10               # about 6 min, 2 GB
python -m computations.driver_density reentry --times 40,80,120,160                    # about 1 min
python -m computations.driver_density chain --steps 1000 --width 20000                 # about 6 min
python -m computations.driver_density describe --steps 160 --beam-steps 3000          # about 15 min
```

`lifetimes` prints the fitted slopes, the ratios $l_w(t)/t$ and the black letters over $\log_2 N(t)$; `describe`
prints the greedy driver's count. The beam's equality with $M(T)$ for $T \le 190$ compares the `exact` output with
`beam --steps 190 --every 5`.
