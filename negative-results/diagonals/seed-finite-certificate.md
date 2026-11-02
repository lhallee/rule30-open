---
title: No finite certificate with a bounded potential bounds the seed onsets at every depth unless the white runs of the settled diagonals stay bounded; one step can cost 24 by depth 200,000, the abstractions that keep the periodic pair have no cycle on the pairs that occur, and the pair graphs keep cycle mean 7/3 until the window covers the period
category: diagonals
problems: [2]
status: negative
kind: dead-end
evidence: [computations/seed_certificate.py]
---

# No finite certificate with a bounded potential bounds the seed onsets at every depth unless the white runs of the settled diagonals stay bounded; one step can cost 24 by depth 200,000, the abstractions that keep the periodic pair have no cycle on the pairs that occur, and the pair graphs keep cycle mean 7/3 until the window covers the period

**Question.** Over every *seed* (a row white left of a black cell), the left diagonal $D_j$ settles at its onset
$T_j$, and the conjecture of [seed-uniform onsets](../../findings/diagonals/seed-uniform-onsets.md) is
$T_j \le \lceil 3j/2 \rceil + 5$; with the front $R_j = \max(T_0, \dots, T_j)$ it reads
$R_j \le \lceil 3j/2 \rceil + 5$, and any slope $\gamma < 2$ would feed
[SettledSlope](../../Rule30Open/Diagonals/SettledSlope.md). The searches walk the seeds' cells one depth at a time. A
*finite certificate* would be a finite set of abstract states, a map from every seed at every depth to a state,
transitions covering every step $j \to j + 1$ of every seed, and an integer potential $\Phi$ with
$$R_{j+1} - R_j \le \gamma + \Phi(\text{old}) - \Phi(\text{new})$$
on every transition: the largest cycle mean of the weighted graph is at most $\gamma$. Can one be found, by a window of
the last diagonals near the front, the phase of the settled ones, or a quotient by future behavior?

## The step where it stops: a bounded potential bounds one step

Summing the inequality along a seed from depth $n$ to $n + k$ gives
$$R_{n+k} - R_n \le \gamma k + \max \Phi - \min \Phi$$
for every seed, every $n$ and every $k$: a finite certificate bounds the increments of the front uniformly in the
starting depth. Take for the seed a late row of the single cell, whose diagonals $0, \dots, n$ repeat from time 0 (so
$R_n = 0$), with any cells past $n$. Let $g_n$ be the longest cyclic white run of the periodic part of the single
cell's $D_n$ and $c_n = g_n + 1$ (the cost of the reset bound of SettledSlope). Choose the late row at the phase where
time 0 starts that white run, and the cell $x_{n+1}$ against the periodic continuation of $D_{n+1}$: then $D_{n+1}$
first meets a black cell of $D_n$ at time $g_n$, its defect bit is 1 there, and $T_{n+1} = g_n + 1$ (the front law of
the kit's main branch, `Rule30FrontLaw.D_front_law`; `driven_one_step`, one time at a time, gives $\max T_{n+1} = c_n$ over the
phases and both cells at every $n \le 398$ but the white diagonals 2, 7 and 28). So
$$\max \Phi - \min \Phi \ge c_n - \gamma \quad \text{for every } n.$$
The largest $c_n$ in each period regime of the single cell (the table of SettledSlope, to depth 200,000; `--jumps`) is

| Period of $D_n$ | 4 | 8 | 16 | 32 |
|---|---:|---:|---:|---:|
| Largest $c_n$ | 4 | 8 | 16 | 24 |

so to depth 200,000 a certificate with $\gamma < 2$ needs a potential of range more than 22, and a certificate for
every $j$ needs $\sup_n c_n < \infty$: a bound on the white runs of the settled left side at every depth. The periods
are unbounded (the kit's main branch, `Rule30LeftUnbounded`), at periods 8 and 16 some diagonal has a single black cell
per period, and the mean of $c_n$ rises by 0.8 to 0.9 at each doubling ([FrontWalker](../../Rule30Open/Diagonals/FrontWalker.md)).
Nothing here proves the white runs unbounded, but no argument in the repository bounds them, and a finite certificate
would have to.

Over several depths the late rows cost less. A beam search over the cells past $n$ (512 rows kept per depth, every
phase; with 256 rows it equals the exhaustive `driven_max` for $k \le 16$ at $n = 40$ and 80) finds, for $n = 60, 120, 200, 240$ and $k \le 150$,
largest $N_{n,k} - \lceil 3k/2 \rceil$ of 8, 4, 8 and 9, with $N_{n,150}$ = 187, 185, 197, 211 (1.23 to 1.41 per
depth). These are lower bounds, so they show only that the beam finds no costly late row past the first steps:
the increments it finds stay near slope $3/2$ or below in this range, a heuristic, not a bound; the obstruction
is the single step, whose cost is set by the settled side.

## The abstractions tried

**Keeping the periodic pair.** The window abstraction of [seed window bounds](../../findings/diagonals/seed-window-bounds.md)
keeps the pair $(D_{j-1}, D_j)$ for a period after the front and $h$ times before it. It is sound and its bound has
slope about 1.5 at $h = 8$, but its periodic words are those of the single cell shifted in time, which never repeat
up to a shift ([linear settling leads](linear-settling-leads.md), lead 3). Started from depth 0, its reachable states
form a graph without a cycle below depth 53,207, where the single cell's pairs at depths 1 to 53,207 are distinct up
to a time shift (past it the abstract words at a depth number 32 to 64, more than the 16 rotations of one pair, and
lead 3 does not cover them): the certificate it gives is the computation depth by depth, to the depth computed.

**Every pair word of one period.** To get cycles the graph must hold pair words that occur at no depth. The pair graph
of period $P$ (`pair_graph`) takes every pair word of period $P$, every age and every window of width $h$, with the
transitions of the window abstraction (which needs no fact about the skeleton, only that the periods divide $P$), and
`max_cycle_mean` finds its largest cycle mean by policy iteration; `check_certificate` then verifies an integer
potential on every edge.

| $P$ | Window $h$ | States | Largest cycle mean |
|---:|---:|---:|---:|
| 4 | 0, 1, 2, 3 | 43 to 1,717 | 7/3 |
| 4 | 4, 5 | 5,494 and 20,586 | 5/3 |
| 8 | 0, 1, 2 | 16,043 to 333,914 | 7/3 |

The cycle of mean 7/3 is the same in every row: three pair words of period 4,
$(A, B) = (1101, 1100) \to (1001, 0001) \to (0001, 0111)$ read from the front, where the free cell is set against the
continuation at each step and the increments are 1, 4 and 2: the front walk of
[FrontWalker](../../Rule30Open/Diagonals/FrontWalker.md) with its defect bit 1 every time, on a pair map that returns
in three depths. No seed meets these words below depth 53,207: the single cell's pairs of period 4 (depths 8 to 28)
are none of them at any common rotation, and below that depth every seed's periodic parts are the single cell's
shifted in time ([DrivenSkeleton](../../Rule30Open/Diagonals/DrivenSkeleton.md)). A window of 4 times breaks the cycle
at $P = 4$ (the best cycle then has increments 1, 4, 0, 3, 0, 2), but the graph is then sound only where every period
divides 4, below depth 29. At $P = 8$, sound below depth 399, the graph has $4^8$ words and $4^h$ windows per age, and
widths past 2 were not built.

**Forgetting the periodic part.** Without the periodic word the next black cell of $D_j$ after the front is not
known, and the transition must allow the longest white run of any settled diagonal, the $c_n$ above. Even with the
white runs bounded, the defect bit compares $D_{j+1}$ with itself one period later, so without the periodic word the
transition must allow the defect 1 at every step: the front walk, whose steps average about 2
([FrontWalker](../../Rule30Open/Diagonals/FrontWalker.md)).

## What it means

The search's states cannot be closed into a finite certificate for every depth by any of these quotients: a finite
potential bounds the one-step cost of a late row, which is the white-run cost $c_n$ of the settled side, so a proof for
every $j$ needs a bound on those white runs (or a certificate whose potential grows with them). Within a fixed period
regime the obstruction is absent, and there the depth-by-depth computation of the window abstraction already gives
slope about 3/2 ([seed window bounds](../../findings/diagonals/seed-window-bounds.md)). This is the finite-state side of
the stops recorded in [seed-uniform induction](seed-uniform-induction.md) (route 1 there is the uniform increment
$N_{n,k}$ for $k \le 16$) and [linear settling leads](linear-settling-leads.md); for black runs of the driven left half
the analogous barrier is [finite-state slopes](finite-state-slopes.md).

## Reproduce

```bash
python -m computations.seed_certificate --graph 4 --widths 0,1,2,3,4,5        # about 2 s
python -m computations.seed_certificate --graph 8 --widths 0,1,2              # about 1.5 min, 0.4 GB
python -m computations.seed_certificate --beam 60,120,200,240 --k 150 --beam-width 512   # about 30 s
python -m computations.seed_certificate --jumps 200000                        # the largest c_n by period, about 3 min
```
