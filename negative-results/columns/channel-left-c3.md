---
title: The right channel cuts the free reading of the kit's C3 for 0001 to 0.35 bit per period and no left half of up to 180 cells meets the constrained statement, but the search does not close
category: columns
problems: [1]
status: negative
kind: dead-end
evidence: [computations/channel_left.py, computations/channel_ladder.py]
---

# The right channel cuts the free reading of the kit's C3 for 0001 to 0.35 bit per period and no left half of up to 180 cells meets the constrained statement, but the search does not close

**Question.** The kit's `C3 w0001` (`Rule30PeriodFourSkeleton.C3`) asks that no finite left half, run with the white
effective boundary, keep column $-1$ on the pattern $(0, *, 0, 1)$ at phases 0 to 3 from some time on: one free reading
in four, 1 bit per period. At phase 1 of $0001$ the center is white now and next, so column $-1$ there is column 1, a
reading of the right channel of [the channel ladder](channel-ladder.md). Beside a center that repeats $0001$, the
window of columns 1 to $W$ lies in the channel's limit set after finitely many periods, and from then on column 1 reads
the labels of a path of that set. So a left half that meets `C3` beside a real right half has, from some time on,
free readings that the channel's automaton accepts. How far does this constraint lower the entropy of the free
reading, and does the left-half search then close, or reach farther than the searches of
[the left-half statements](../../findings/columns/left-half-c3.md) and [the constrained left
halves](constrained-left-halves.md)?

**Outcome.** The constraint is strong: it leaves 0.354 bit per period at width 24 of the 1 bit `C3` leaves free, and
the number of left halves to follow at depth $M$ grows as $2^{0.088 M}$ instead of $2^{M/4}$ (15,196 over the four
phases at $M = 100$, against $2^{27}$), so every half of up to 180 cells fails the constrained statement, in every
phase. It changes nothing in kind: the latest failure keeps growing with the half's length, by margins of the size
fair coins predict, and the constrained statement still has infinite solutions (the readings
allowed form a sofic shift of positive entropy). Settled for bounded classes only.

## The automaton

`channel_dfa` determinizes the readings of column 1 at the white phases along every path of the step graph of the
limit set at width $W$, from the whole limit set at each phase, one state per set of windows at one phase; `minimize`
merges states with the same future (Moore's refinement). The census then reads column $-1$ against the kit's pattern
and, at the white phases, column 1 (column $-1$ xor the next center cell) against the automaton. The entropy is the
growth of the column $-1$ sequences that the pattern and the automaton allow together, $\log_2$ of the Perron root of
the product graph (Collatz-Wielandt bounds within $10^{-7}$):

| $W$ | automaton states | minimal | bits per period | share of the free reading |
|---:|---:|---:|---:|---:|
| 16 | 3,477 | 2,192 | 0.4608 | 0.461 |
| 17 | 4,558 | 2,965 | 0.4506 | 0.451 |
| 18 | 6,762 | 4,605 | 0.4280 | 0.428 |
| 19 | 9,255 | 6,881 | 0.4153 | 0.415 |
| 20 | 15,269 | 11,356 | 0.3985 | 0.398 |
| 21 | 21,884 | 15,342 | 0.3833 | 0.383 |
| 22 | 28,718 | 19,871 | 0.3759 | 0.376 |
| 23 | 42,178 | 30,723 | 0.3641 | 0.364 |
| 24 | 57,279 | 38,480 | 0.3535 | 0.354 |

At every width these equal the entropy of the whole channel (the largest component of [the ladder](channel-ladder.md)),
and reading column 1 at phase 1 alone gives the same numbers at widths 10 to 22: the free reading of `C3` carries all
the entropy of the channel, and the pins of the pattern at phases 0 and 2 cost nothing. The share is far below 0.8 of
the free reading, and below the kit's `no11_0001` (the free reading never black in two consecutive periods, the check
of [EtherDomain](../../Rule30Open/Columns/EtherDomain.md)), which leaves $\log_2$ of the golden ratio, 0.694 bit per
period; adding `no11_0001` to the automaton at width 24 changes no count of the census below for $M \le 100$.

## The census

`tree_failures` is the search of `constrained_left.tree_failures` with the automaton's state in place of the history:
cell $-1$ at step $t$ is bit $t$ of the half xor a function of its lower bits, so the halves of at most $M$ cells that
keep the condition through step $M - 1$ are as many as the allowed words of $M$ values of column $-1$, and each is
followed with white cells beyond $-M$ until it fails. The step count starts at a time from which both the pattern
holds and the window of columns 1 to $W$ lies in the limit set, with the automaton in its state for the whole limit
set at that phase; a half that lies within depth $M$ at that time is covered, as in the other left-half searches,
and the unconstrained `C3` is settled only as far as [the left-half
statements](../../findings/columns/left-half-c3.md) take it. Every half of at most $M$ cells fails, in each of the
four phases; the latest first failure over the halves of exactly $M$ cells, the four phases together, with the number
of halves of at most $M$ cells that keep the condition through step $M - 1$:

| $M$ | `C3`, latest (halves) | channel $W = 16$, latest (halves) | channel $W = 24$, latest (halves) |
|---:|---:|---:|---:|
| 20 | 27 (128) | 25 (44) | 25 (43) |
| 40 | 49 (4,096) | 46 (216) | 46 (205) |
| 60 | 75 (131,072) | 68 (1,140) | 68 (990) |
| 80 | 105, from the margin 25 of [the C3 search](../../findings/columns/left-half-c3.md) | 90 (5,672) | 90 (4,051) |
| 100 | | 115 (28,238) | 115 (15,196) |
| 120 | | 143 (139,812) | 134 (53,485) |
| 140 | | 155 (691,218) | 155 (183,397) |
| 150 | | 176 (1,569,001) | 169 (342,610) |
| 160 | | 178 (3,414,786) | 176 (627,427) |
| 180 | | 202 (16,867,048) | 198 (2,143,154) |

The largest margin past $M$ is 22 at $M = 171$ with the channel at width 24 and 26 at $M = 150$ at width 16; the
fair-coin margin $hM/(1 - h)$ of [every block](../../findings/columns/left-half-every-block.md), for the entropy $h$ in
bits per step, is 17.5 and 23.4 at $M = 180$, and $M/3$ for `C3` (21.3 at $M = 64$, against an observed 21). With the
kit's check alone, the integer search of [the left-half statements](../../findings/columns/left-half-c3.md) has
margins 15 at $M = 100$ and 26 at $M = 140$ at phase 0, with 196,418 branches at $M = 100$; the channel at width 24 has
the same margin 15 at $M = 100$ with 15,196 halves over the four phases, and 15 at $M = 140$.

## Where it stops

The constraint is a smaller exponent, not a terminating search. The halves that keep the constrained condition forever
are in bijection with the allowed sequences of column $-1$ (the triangular structure of section 3 of [the constrained
left halves](constrained-left-halves.md)), a sofic shift of positive entropy at every width computed, and each
periodic allowed sequence gives a half that is periodic in space, never finite. A wider channel lowers the exponent a
little more per cell (0.461 to 0.354 bit per period from width 16 to 24) and shortens the longest-lived halves at some
lengths (143 to 134 at $M = 120$, 176 to 169 at $M = 150$), but the margins at both widths grow with $M$ at about the
rate the coin model gives. Finiteness of the half enters only as "white beyond depth $M$", one $M$ at a time, as for
$001$ and $011$. A proof would need the channel's entropy to reach 0 (then [the ladder](channel-ladder.md)'s class test
would already exclude the word) or an argument that uses the finite support.

## Reproduce

```bash
python -m computations.channel_left --word 0001 --projection 16-24           # the table of entropies, about 7 min
python -m computations.channel_left --word 0001 --width 24 --tree 180        # about 8 min (4 min to build)
python -m computations.channel_left --word 0001 --width 16 --tree 180        # about 20 min
python -m computations.channel_left --word 0001 --width 24 --tree 100 --no11 # with the kit's no11_0001
python -m computations.channel_left --word 0001 --tree 64 --free             # the kit's C3 alone, 10 s
python -m computations.channel_ladder --block 0001 --widths 10-22 --reads 1  # column 1 at phase 1 alone
```

The times are on a loaded machine with four cores, one thread each. `tests/test_channel_ladder.py`
checks the census at width 9 against a cell-by-cell run of every half of up to 8 cells in each phase, with and
without the channel and with `no11_0001`, the branch counts against the allowed words, the minimal automaton against
the unminimized one, the entropy at width 9 against the per-period construction of the ladder, and that the product
with `no11_0001` never reads 1 at phase 1 in two consecutive periods.
