---
title: With right cells 1 to k exact and cell k + 1 free, the most white cells of the center column among c(0..150) is 117 at k = 1 (exact), where the left half alone allows 149, the best free words found gain about 0.80 white cells per step to T = 3,000 at k = 1 and 2, and both colors' rates fall with k, to 0.66 and 0.68 at k = 16
category: diagonals
problems: [2]
status: conjecture
formalization: wanted
evidence: [computations/right_ladder.py]
---

# With right cells 1 to k exact and cell k + 1 free, the most white cells of the center column among c(0..150) is 117 at k = 1 (exact), where the left half alone allows 149, the best free words found gain about 0.80 white cells per step to T = 3,000 at k = 1 and 2, and both colors' rates fall with k, to 0.66 and 0.68 at k = 16

**The ladder.** Level $k$ is the following system. The left half (cells $-1, -2, \ldots$) is exact from a white start
and driven by the center $c$; the right cells $1, \ldots, k$ are exact from a white start,
$x_i(t + 1) = x_{i-1}(t) \oplus (x_i(t) \lor x_{i+1}(t))$ with $x_0 = c$; cell $k + 1$ is free at every step (a free
word $f(0), f(1), \ldots$); and $c(0) = 1$, $c(t + 1) = x_{-1}(t) \oplus (c(t) \lor x_1(t))$. For a color $b$ write
$M_b(k, T)$ for the largest number of times $t \le T$ with $c(t) = b$ over all free words of level $k$.

- **Every level holds the single cell.** Its free word is its own column $k + 1$. More generally level $k$ holds the
  center column of every configuration that is white on cells $< 0$ and on $1 .. k$ and black at 0 at time 0,
  whatever it holds right of $k$. So $M_b(k, T)$ bounds the single cell's count of color $b$ before $T$ from above.
- **The levels are nested.** In level $k + 1$ the word that reaches cell $k + 1$ is the column of an exact cell, one
  free word among all, so $M_b(k + 1, T) \le M_b(k, T)$. The free cell at time $s$ reaches the center no earlier
  than time $s + k + 1$, so for $T \le k$ level $k$ is the single cell up to time $T$.
- **Level 0 allows all white.** With cell 1 free, $c(1) = 1$ is forced and then a free cell equal to $x_{-1}(t)$ keeps
  every later center white: $M_0(0, T) = T - 1$. Its black maxima are those of the left-only constraint of
  [the driven left runs](driven-left-runs.md#the-left-only-constraint), where a black center fixes the next one.
- **Level 1 is a switch.** At level 1, $x_1(t + 1) = c(t) \oplus (x_1(t) \lor f(t))$. While the center is white,
  $x_1(t + 1) = x_1(t) \lor f(t)$: column 1 turns black at a time the free word chooses and then stays black, and
  $c(t + 1) = x_{-1}(t) \oplus x_1(t)$. After a black center $x_1(t + 1) = \lnot (x_1(t) \lor f(t))$. So a white run
  of the center at level 1 lasts while column $-1$ under the white driver reads $0^z 1^o$ with the switch at $z$,
  which is the reduction behind the white bound $R_W$ of [the driven left runs](driven-left-runs.md): the white rate
  of level 1 is a property of the driven left half with one switch per white run.

Write $\rho_b(k) = \limsup_{T} M_b(k, T) / T$, with $\rho_W = \rho_0$ and $\rho_B = \rho_1$.

**Conjecture $S_W(k)$, for $k \ge 1$.** $\rho_W(k) < 1$: there are $\rho < 1$ and $C$ such that $M_0(k, T) \le \rho T
+ C$ for every $T$. Since the levels are nested, $S_W(1)$ gives every $S_W(k)$, and it gives the single cell at least
$(1 - \rho) T - C$ black cells among $c(0 .. T)$, a positive lower density of black cells, where the kit's counts are
of order $\log T$. The data below put $\rho_W(1)$ near 0.80.

**Conjecture $S_B(k)$, for $k \ge 1$.** $\rho_B(k) < 1$: there are $\rho < 1$ and $C$ such that $M_1(k, T) \le \rho T +
C$. Each $S_B(k)$ gives the single cell a positive lower density of white cells. The data put $\rho_B(1)$ near 0.74. At
level 0 the same statement is about the left half alone, the conjecture $S_B$ of [the driver
density](driver-density.md), and the data put its rate near 0.75; it would give every $S_B(k)$.

## Exact maxima

`ladder_exact` computes $M_b(k, T)$ by dynamic programming over the states (left half, $c$, $x_1 .. x_k$), keeping
the largest count per state; `tests/test_right_ladder.py` checks it against every free word for $T \le 12$ and
$k \le 3$. The window is the largest count of the color among $c(76 .. 150)$ over every state reachable at time 75,
with the count reset there, so it bounds $M_b(k, 150) - M_b(k, 75)$ and is free of the start.

| $k$ | white, $T = 60$ | 100 | 150 | window of 75 | black, $T = 60$ | 100 | 150 | window of 75 | states at 150 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | 59 | 99 | 149 | 75 | 44 | 73 | 110 | 60 | 2,418,959 |
| 1 | 45 | 78 | 117 | 65 | 44 | 72 | 109 | 60 | 2,578,279 |
| 2 | 44 | 75 | 114 | 64 | 43 | 71 | 107 | 58 | 1,669,509 |
| 3 | 40 | 70 | 109 | 63 | 43 | 71 | 105 | 57 | 1,546,239 |
| 4 | 40 | 67 | 105 | 61 | 43 | 71 | 105 | 57 | 1,891,626 |
| 5 | 37 | 67 | 103 | 59 | 42 | 69 | 103 | 56 | 1,755,629 |
| 6 | 37 | 65 | 102 | 59 | 42 | 69 | 103 | 56 | 2,142,330 |
| 7 | 37 | 65 | 102 | 59 | 39 | 67 | 102 | 56 | 1,993,437 |
| 8 | 37 | 65 | 98 | 57 | 39 | 66 | 102 | 55 | 1,341,522 |
| 12 | 37 | 65 | 97 | 53 | 36 | 62 | 97 | 52 | 1,135,404 |
| 16 | 37 | 64 | 95 | 52 | 33 | 58 | 91 | 52 | 1,669,104 |
| 24 | 30 | 53 | 84 | 49 | 33 | 58 | 89 | 46 | 1,740,989 |
| single cell | 28 | 49 | 73 | | 33 | 52 | 78 | | 1 |

- At $k = 1$ the largest white count over $c(0 .. 150)$ is 117 of 151 cells, and over $c(76 .. 150)$, from any state
  reachable at time 75, it is 65 (0.867 per cell); the left half alone allows 149 and 75. The window is above the beam
  rates below, so on this range the exact upper side does not yet reach the rates the beam finds.
- At small $k$ the black maxima fall more slowly than the white ones: 110, 109 and 107 at $k = 0, 1, 2$ against
  149, 117 and 114 (at $T = 150$). While the center is black, $c(t + 1) = \lnot x_{-1}(t)$ whatever the right half
  holds, so the right columns act on black cells only through the white cells between black runs.
- The reachable states grow by 0.082 to 0.091 bits per step from $t = 120$ to 150 at every level $k \le 24$ in the
  table, as at level 0 (0.090), and their number at $T = 150$ is within a factor 2.2 of level 0's. The right columns
  lower the maxima without cutting the reachable set by more than a constant factor on this range.

## Beam rates

`ladder_beam` keeps, after each step, the `width` states with the largest counts and returns a free word that attains
its best count; the module replays that word cell by cell (`simulate`) and checks the count, so each number below is
attained by a free word and is a lower bound on $M_b(k, T)$. The beam with width 15,000 and the lookahead below equals
the exact maximum at every $T = 10, 20, \ldots, 150$ for $k = 1, 4, 8, 12, 16, 24$ and both colors, while it keeps at
most 1.4% of the 1.1 to 2.6 million states at $T = 150$. The rate is the beam's gain per step from $T/2$ to $T$
(`steady_rate`): an estimate of the long-run slope from counts that are lower bounds, not itself a bound. The plain beam
ranks states by their count so far; the beam with lookahead ranks them by the count over $c(0 .. t + k)$, which the
state at $t$ already fixes (`committed`), since the free cell at time $s$ reaches the center no earlier than $s + k +
1$.

| $k$ | white rate | black rate | $T$ | beam |
|---:|---:|---:|---:|---|
| 0 | 1 (exact) | 0.754 | 2,000 | plain, width 60,000 |
| 1 | 0.805 | 0.743 | 3,000 | plain, width 60,000 |
| 2 | 0.800 | 0.724 | 2,000 | plain, width 60,000 |
| 4 | 0.747 | 0.716 | 2,000 | plain, width 60,000 |
| 8 | 0.710 | 0.694 | 1,000 | lookahead, width 60,000 |
| 16 | 0.664 | 0.676 | 1,000 | lookahead, width 60,000 |
| 32 | 0.634 | 0.632 | 1,000 | lookahead, width 60,000 |
| 48 | 0.558 | 0.582 | 1,000 | lookahead, width 60,000 |

The single cell has 520 white and 481 black cells among $c(0 .. 1000)$, and 1,023 and 978 among $c(0 .. 2000)$.

- **Steady from the start.** At $k = 1$ the white gain is 78 to 83 per 100 steps over each of the 29 blocks from $T =
  100$ to 3,000, with no trend: 802 white cells by $T = 1{,}000$, 2,410 by 3,000. The black gain at $k = 1$ is 72 to 77
  per 100 steps on the same range.
- **Width and ranking, $k \le 16$.** For $k = 1$ (white) the plain beams of width 15,000, 60,000 and 240,000 reach the
  same count at every checkpoint to $T = 1{,}000$ (802); for $k = 4$ (white) the plain beams of width 60,000 and 240,000
  reach 739 and the beam with lookahead and width 15,000 reaches 737. For $k = 8$ the plain beam of width 15,000 and the
  beam with lookahead and width 60,000 agree at every checkpoint to $T = 1{,}000$ for white (705) and differ by at most
  2 for black (687 at $T = 1{,}000$ in both); for $k = 16$ they reach 663 and 666 white, 649 and 661 black. Plain beams
  of width 15,000 to $T = 2{,}000$ give rates 0.714 and 0.686 at $k = 8$, and 0.665 and 0.658 at $k = 16$.
- **Where the beam stops being reliable.** A free cell's effect on the center often arrives later than $k + 1$ steps
  (see [the drivers](#the-drivers-the-beam-finds)), and a beam that ranks by counts cannot plan for it. At $k = 32$
  (white, $T = 1{,}000$) the plain beam of width 15,000 reaches 572, the beam with lookahead 598 at width 15,000 and 617
  at width 60,000; at $T = 400$ the widths 60,000 and 240,000 reach the same count (241, against 230 at 15,000), but
  at $T = 200$ they reach 112 and 114. At $k = 48$ the gain per 100 steps varies from 49 to 66 and the plain beam of
  width 15,000 gives rates 0.564 and 0.542 to $T = 2{,}000$. So the rates for $k \ge 32$ are not settled in the beam,
  and part of the fall past $k = 16$ may be the beam's.

## The drivers the beam finds

`drivers` takes the free word of the beam (with lookahead, width 15,000, $T = 600$), replays it, and flips each free
cell $f(s)$ alone for $150 \le s < 300$ to find the first center value it changes. The counts are over the second half,
$c(300 .. 600)$.

| $k$, color | mean run of the color | mean run of the other | free cells that change the center | first change exactly $k + 1$ later | median lag | largest lag |
|---|---:|---:|---:|---:|---:|---:|
| 1, white | 5.37 | 1.17 | 67 of 150 | 1.00 | 2 | 2 |
| 2, white | 4.92 | 1.25 | 77 of 150 | 0.84 | 3 | 5 |
| 4, white | 3.75 | 1.29 | 42 of 150 | 0.40 | 7 | 20 |
| 8, white | 3.41 | 1.30 | 47 of 150 | 0.19 | 13 | 27 |
| 16, white | 2.63 | 1.23 | 43 of 150 | 0 | 46 | 98 |
| 1, black | 3.01 | 1.07 | 20 of 150 | 0.75 | 2 | 3 |
| 2, black | 3.37 | 1.26 | 25 of 150 | 0.36 | 5 | 14 |
| 4, black | 3.48 | 1.37 | 41 of 150 | 0.10 | 10 | 25 |
| 8, black | 3.13 | 1.36 | 33 of 150 | 0 | 23 | 36 |
| 16, black | 2.76 | 1.44 | 40 of 150 | 0 | 44 | 81 |

- **Shape.** The white drivers are white runs separated by single black cells (39 of the 46 black runs at $k = 1$
  have length 1, and the white runs reach 19); the black drivers are black runs separated by single white cells (68
  of the 73 white runs at $k = 1$). As $k$ grows the runs of the favored color shorten (white 5.37 to 2.63 from
  $k = 1$ to 16) and the other color's runs stay near 1.2 to 1.4 cells.
- **When the free cell decides.** A free cell $f(s)$ decides the center at time $s + k + 1$, the earliest possible,
  exactly when the cells $x_k(s), x_{k-1}(s + 1), \ldots, x_1(s + k - 1)$ and $c(s + k)$ on the diagonal from it
  are white, since a flip of a cell's right neighbor passes the `or` only when the cell is white. At $k = 1$ every
  free cell that matters for the white driver decides the center two steps later; at $k = 2$, 84% of them do; at
  $k = 8$, 19% (white) and none (black); at $k = 16$, none. At $k = 8$ and 16 the first change comes a median of 13
  to 46 steps later, about $1.6 k$ to $2.9 k$, near [the one-way valve](../dynamics/one-way-valve.md)'s median of
  $2.5 d$ for a flip at distance $d$, and the largest lag is 98 (at $k = 16$, white). These are the free cells of one
  witness per level, 150 cells each. So past small $k$ the adversary steers the center through delayed, indirect
  effects, which a beam that ranks by counts cannot plan for (above).

## What the limit measures

$\rho_b(k)$ cannot increase with $k$, so it has a limit $\rho_b(\infty)$, at least the single cell's upper density of
color $b$. The limit need not be the single cell's density: for each fixed $T$ the levels reach the single cell once $k
\ge T$, but $\rho_b(k)$ is a long-run rate at fixed $k$: an adversary that controls cell $k + 1$ forever, with the cells
between exact. Since level $k$ holds every configuration white on cells $< 0$ and $1 .. k$ and black at 0, $\rho_b(k)$
is at least the largest upper density of color $b$ that the right half beyond a white gap of $k$ cells, chosen at will,
can impose on the center, and the limit is at least the limit of those as $k$ grows. [The one-way
valve](../dynamics/one-way-valve.md) says how fast the right side reaches the center (a flip at distance $d$ arrives
after about $2.5 d$ steps), not how much it can bias it; the rates here measure the bias.

- If $\rho_W(\infty) = \rho_B(\infty) = 1/2$, with $S_W(k)$ and $S_B(k)$ at every level, both colors have density
  1/2 in the single cell, which is Problem 2. The beam rates fall from 0.80 and 0.74 at $k = 1$ to 0.66 and 0.68 at
  $k = 16$ and 0.63 at $k = 32$, by 0.01 to 0.05 per doubling of $k$ from $k = 2$; whether they tend to 1/2 is open,
  since past $k = 16$ the beam is not settled. This reading is a heuristic.
- A finite automaton over the center column certifies neither conjecture if the runs of the relevant color are
  unbounded at that level, by the pumping argument of
  [finite-state slopes](../../negative-results/diagonals/finite-state-slopes.md): pumping a run of $q$ or more cells
  gives accepted words of density as close to 1 as wanted. At level 1 a white run is bounded only through the left
  half's readings $0^z 1^o$, so a proof of $S_W(1)$ has to average over the left half's memory, as the driven-runs
  conjecture has to bound it.
- The kit, at the pinned commit and on its main branch, has no relaxation of the right half by columns: its
  equivalent form `CoupledHalves` couples the two driven halves exactly, its counts (`Rule30CenterRuns`: at least
  $\log_2 T$ black and $\log_4 T$ white cells before $T$) are of order $\log T$, and the run bounds of
  `Rule30SettledBarrierEffective` on the main branch give no density either.

## Reproduce

```bash
python -m computations.right_ladder exact --steps 150 --levels 0,1,2,3,4,5,6,7,8 --every 10   # about 40 min, 1.5 GB
python -m computations.right_ladder exact --steps 150 --levels 12,16,24 --every 10            # about 40 min
python -m computations.right_ladder beam --steps 3000 --levels 1 --width 60000 --plain        # about 50 min
python -m computations.right_ladder beam --steps 2000 --levels 0,2,4 --width 60000 --plain    # about 2 h
python -m computations.right_ladder beam --steps 1000 --levels 8,16,32,48 --width 60000       # about 1.5 h
python -m computations.right_ladder beam --steps 150 --levels 1,4,8,12,16,24 --width 15000 --every 10  # about 2 min
python -m computations.right_ladder beam --steps 2000 --levels 8,16,32,48 --width 15000 --plain   # about 40 min
python -m computations.right_ladder beam --steps 1000 --levels 1,4 --colors 0 --width 240000 --plain   # about 40 min
python -m computations.right_ladder beam --steps 1000 --levels 1 --colors 0 --width 15000 --plain      # about 3 min
python -m computations.right_ladder beam --steps 1000 --levels 4,32 --colors 0 --width 15000           # about 10 min
python -m computations.right_ladder beam --steps 400 --levels 32 --colors 0 --width 240000             # about 5 min
python -m computations.right_ladder drivers --steps 600 --levels 1,2,4,8,16 --width 15000      # about 10 min
```
