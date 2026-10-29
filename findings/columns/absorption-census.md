---
title: Every right half of up to 20 cells enters the kit's ether-and-wall family
category: columns
problems: [1]
status: computed
formalization: wanted
evidence: [computations/absorption.py]
---

# Every right half of up to 20 cells enters the kit's ether-and-wall family

The kit reduces least period 4 for the center column to one open statement per word,
[`Rule30Ether.Absorption`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Ether.lean):
every finitely supported right half, driven by a center that repeats $0001$, $0011$ or $0111$ from any phase,
eventually enters the ether-and-wall family, a set of states that the driven rule never leaves and on which masked Jen
gives a contradiction (`least_period_four_of_absorption`). For each of the three words and each of the four phases,
all $2^{20}$ right halves of at most 20 cells enter, within 1,034 steps for $0001$, 1,959 for $0011$ and 787 for
$0111$. So do 2,000 random infinite halves per word and phase, the 31 sample starts of
[the locking finding](period-four-locking.md), and every periodic half of period at most 11 except those that are,
or within two steps become, the pure ether.
Finite and random halves wait for entry alike, and the latest entry grows about linearly with the number of cells.

## The family

Bit $j$ of a right half is column $j + 1$, and the center applied from $t$ to $t + 1$ is $w[(t + \varphi) \bmod 4]$,
as in the kit's `drv`. The ether repeats the columns $B_1 B_2 B_3 B_4 B_5\,c\,c$ with period 4 in time, and each word
is ether column $j_0$ shifted by $s$ in time, for the kit's alignments: $(5, 0)$ and $(6, 0)$ for $0001$; $(0, 0)$,
$(1, 3)$ and $(4, 0)$ for $0011$; $(2, 2)$ for $0111$. A half is in the family at time $t$ (`InFamily`) when, for one
alignment and some $k$ with $j_0 + k \equiv 2 \pmod 7$, columns 1 to $k$ are ether columns $j_0 + 1$ to $j_0 + k$ at
ether phase $t + s + \varphi$, so that column $k$ is a $B_3$, and columns $k + 1$ to $k + 13$ are a wall state at that
phase. The census checks $k \le 51$, so it can only undercount entry.

The wall is computed, not read. The greatest set of 13-cell strips right of a $B_3$ column, one set per phase, that
the rule maps into itself for both values of the cell beyond, with the first cell equal to $B_4$ wherever $B_3$ is
white, has 433, 533, 344 and 605 states at phases 0 to 3. Exactly one of its strongly connected components has no
move out; it has 26, 29, 27 and 27 states and is the kit's `wallStates`, state for state. Two certificates are members
of the family, both with $k = 3$:

- the core certificate of $0001$ at width 16 in [the certificate finding](period-four-certificate.md) is
  $B_1 B_2 B_3$ followed by the greatest set;
- the kit's certified trap `S0001` is $B_1 B_2 B_3$ followed by the kit's wall.

The deeper members, with the ether running past column 3, are what a window of fixed width misses. The kit's
`never_enters_S0001` is a half that stays in a deeper member forever, and the four starts that enter no certificate in
[the certificate finding](period-four-certificate.md#the-starts-that-do-not-enter) all enter the family from phase 0:
start 4 under $0001$ at step 142, start 24 under $0011$ at step 28, and starts 8 and 18 under $0111$ at steps 29 and
108.

## Census

The latest entry over all right halves of at most $n$ cells, searched for 4,000 steps. Every one of the $2^{20}$ halves
enters in each of the 12 runs.

| word | phase | $n = 4$ | 8 | 12 | 16 | 20 |
|---|---|---|---|---|---|---|
| $0001$ | 0 | 117 | 355 | 544 | 732 | 1,032 |
| | 1 | 142 | 354 | 543 | 731 | 1,001 |
| | 2 | 141 | 546 | 734 | 780 | 1,034 |
| | 3 | 153 | 298 | 733 | 792 | 1,033 |
| $0011$ | 0 | 203 | 521 | 980 | 1,627 | 1,957 |
| | 1 | 336 | 639 | 814 | 1,626 | 1,895 |
| | 2 | 335 | 519 | 977 | 1,430 | 1,959 |
| | 3 | 334 | 479 | 976 | 1,047 | 1,958 |
| $0111$ | 0 | 295 | 295 | 416 | 544 | 787 |
| | 1 | 131 | 294 | 547 | 547 | 763 |
| | 2 | 297 | 297 | 468 | 546 | 762 |
| | 3 | 296 | 296 | 417 | 545 | 765 |

## Infinite halves

- **Random.** 2,000 halves per word and phase, with 4,070 random cells, which is the whole half as far as 4,000 steps
  can see (`numpy.random.default_rng(30)`). All enter, the latest at step 670 for $0001$, 1,151 for $0011$ and 524
  for $0111$, over the four phases.
- **Periodic.** Every half that repeats a word of at most 11 cells, in every rotation, is 4,012 halves per word and
  phase. All enter within 1,322 steps except one to four per word and phase, all of period 7, and each of those is the
  ether aligned with the drive at step 0 or becomes it at step 1 or 2. Under $0001$ at phase 0 they are $0001000$ and
  $0010000$; at phase 1, $1110110$ becomes the ether two steps later. The aligned ether repeats with period 4 and is
  in the family at none of its phases, so it never enters. Absorption fails for infinite halves, and in these runs
  only through the ether itself.

## Long ether segments

A long ether segment next to the center keeps itself. Take a right half with the aligned ether on columns 1 to 120 and
random cells beyond: in 300 such halves per word and phase, every one of the 3,600 is in a member of the family within
497 steps, with $k$ from 49 to 128 (median 107 to 114 by word and phase), mostly past the 64 columns the census window
sees. The first column off the ether moves toward the center by 10 to 14 columns on average and by 71 at most, then
stops at the wall: a disturbance on the right does not eat into the ether. For the ether of period three the kit
proves the opposite, that a finite perturbation always eats into it, at an average speed of at least 2/5 column per
step once in its wake
([`Rule30EtherThreeErosion`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30EtherThreeErosion.lean)),
which is why no wall exists there. So for period four, absorption comes down to an ether segment forming next to the
center at all; holding it is quick.

## Entry times

How long halves wait, at phase 0 (the other phases give means within 5% of these, and tails of the same shape):

| word | halves | mean entry | outside after 100 steps | 200 | 300 | 400 |
|---|---|---|---|---|---|---|
| $0001$ | all of at most 16 cells | 95.1 | 0.39 | 0.085 | 0.019 | 0.0043 |
| | 2,000 random | 93.4 | 0.37 | 0.096 | 0.019 | 0.005 |
| $0011$ | all of at most 16 cells | 95.1 | 0.33 | 0.14 | 0.053 | 0.02 |
| | 2,000 random | 98.7 | 0.35 | 0.14 | 0.065 | 0.024 |
| $0111$ | all of at most 16 cells | 58.7 | 0.15 | 0.023 | 0.0036 | 0.00063 |
| | 2,000 random | 57.7 | 0.14 | 0.025 | 0.003 | 0.001 |

Heuristic: past 200 steps the fraction outside falls by a roughly steady factor per 100 steps, about 4.5 for $0001$,
2.6 for $0011$ and 6 for $0111$, as for an event that happens at a steady rate. The largest of $2^n$ such waiting times
grows linearly in $n$, and the census's latest entries grow by about 55, 100 and 30 steps per cell. A half of 16 cells
waits like a random infinite one. Nothing here suggests that entry comes from clearing the support or from the ether
advancing a column at a time.

## What it means

- **For the kit's conjecture.** The census is evidence for `Absorption` for all three words. The kit states it as open
  and proves that its certified traps of widths 16 and 14 do not suffice (`never_enters_S0001` and its two
  siblings). The window certificates of [the certificate finding](period-four-certificate.md) are the family's member
  at $k = 3$, and they miss halves that the family catches.
- **For each half it covers.** Entry is a finite computation, and Lean's `no_finite_of_family`
  ([EmptyRight.md](../../Rule30Open/Columns/EmptyRight.md)) turns entry of one right half into a proof that no finite
  configuration with that right half, whatever its left half, has a center repeating the word from then on. Lean
  checks the entry of every right half of at most six cells, by step 521 for every word and phase, and of every half
  with at most two black cells among its first 623 to 1,359 cells, whatever lies beyond
  ([SparseRight.md](../../Rule30Open/Columns/SparseRight.md)); for the other halves the computation is the proof.
- **For a proof.** Entry looks like a chance event at a steady rate, so a proof cannot bound the entry time by a
  function of a bounded window
  ([the certificate finding](period-four-certificate.md#attraction-is-open),
  [Jen's theorem on farther columns](../../negative-results/columns/jen-farther-columns.md)). The pure ether shows
  that it must use finiteness, since some infinite halves never enter. For $0001$,
  [EtherDomain.md](../../Rule30Open/Columns/EtherDomain.md) states the matching condition on the left half, a positive
  integer whose held-map orbit reads $0001$ with the no-11 check: the ether's left half satisfies it as a 2-adic
  integer, and no integer below $2^{24}$ does.

## Reproduce

```bash
python -m computations.absorption census --cells 20 --steps 4000
python -m computations.absorption census --cells 16 --steps 4000
python -m computations.absorption infinite --count 2000 --steps 4000 --max-period 11
python -m computations.absorption starts --steps 12000
python -m computations.absorption shield --count 300 --steps 3000
```

[computations/absorption.py](../../computations/absorption.py) runs them in about 7 min, 17 s, 31 s, 1 s and 30 s.
The tests check the census against integer rows stepped one at a time with the family checked column by column, the wall
against the kit's source, the pure ether by direct stepping, and the family at any depth against wall states read
from the kit's source.
