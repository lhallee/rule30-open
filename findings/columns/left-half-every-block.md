---
title: No small left half meets the left-half statement of any block of period 3, 5, 6, 7 or 9
category: columns
problems: [1]
status: computed
formalization: partial
evidence: [computations/left_halves.py]
---

# No small left half meets the left-half statement of any block of period 3, 5, 6, 7 or 9

[LeftLatch](../../Rule30Open/Columns/LeftLatch.md) reduces every eventual period of the center column to one open
statement about the left half. No window lock reaches periods 2, 3, 5, 6, 7 and 9 ([window
locks](../../negative-results/columns/window-locks.md)), and period 2 is the held column's problem ([the left half
alone](../period-two/left-half-alone.md)). For each of the 91 primitive blocks of period 3, 5, 6, 7 or 9 that have a
black phase, in each phase, no left half of at most $M$ cells meets the statement, with $M$ from 37 to 100 by the
block, and none meets its checks alone, with $M$ from 18 to 100. Past its length a half fails about as late as fair
coins would let it, so the searches settle bounded cases only.

## The condition

A block $b$ repeated by the center from some time on asks three things of the left half and of the cell right of the
center, in the orbit of every row (`Keeps` in [LeftLatch](../../Rule30Open/Columns/LeftLatch.md)): the half follows
`held`, kicked next to the center where the block reads 1 at two steps in a row; at a 1 of the block, cell $-1$ is
the negation of the block's next value (the check); and at a 0 of the block the reading of cell $-1$ shows the cell
right of the center, which, while black, is followed by the negation of the center (the latch). The checks alone
are the kit's statements `Q001` for $001$ and `C3w` for $011$. The latch adds readings only after a 0 of the block
that is not followed by two 1s; for $011$, $01111$ and the other blocks whose 0s are each followed by two 1s it adds
nothing.

## The search

Cell $-1$ at step $t$ is bit $t$ of the starting half XOR a function of its lower bits, so the first $M$ readings fix
the half's lowest $M$ cells ([the C3 search](left-half-c3.md)). The search follows the tree of readings the condition
allows, each branch with white cells beyond cell $-M$ until it fails. The halves of at most $M$ cells that keep the
condition through step $M - 1$ are as many as the sequences of $M$ readings that it allows, about $2^{hM}$ for its
entropy $h$: $w/P$ for the checks alone, for a block with $w$ white phases in $P$, and with the latch at most 0.4309
for every block of period up to 14, the largest for $0001$, and over the blocks of period $P$ at least $1/P$, for
$01^{P-1}$. Each survey takes
$M = 16/h$, at most 100, so that about $2^{16}$ branches remain at the last level. The tests check the tree against
stepping every half of up to 9 cells directly, the count of its branches against the automaton of the condition, and
the latch against real orbits.

## Result

For each block the search reports the latest first failure over the halves of exactly $M$ cells, as a margin past
$M$, at its largest $M$. Over the blocks of each period:

| period | blocks | checks alone: $M$ | largest margin | margin over fair coins | with the latch: $M$ | largest margin | margin over fair coins |
|---|---|---|---|---|---|---|---|
| 3 | 2 | 24 to 48 | 61, $001$ | 0.83 to 1.27 | 37 to 48 | 24, $001$ | 0.83 to 0.88 |
| 5 | 6 | 20 to 80 | 91, $00001$ | 0.74 to 1.14 | 38 to 80 | 28, $00101$ | 0.95 to 1.12 |
| 6 | 9 | 19 to 96 | 82, $000001$ | 0.86 to 1.21 | 40 to 96 | 30, $000001$ | 0.88 to 1.20 |
| 7 | 18 | 18 to 100 | 92, $0000001$ | 0.78 to 1.27 | 37 to 100 | 29, $0001001$ | 0.83 to 1.16 |
| 9 | 56 | 18 to 100 | 120, $000000001$ | 0.79 to 1.31 | 37 to 100 | 33, $000001101$ | 0.83 to 1.40 |

The last column of each half is the margin divided by the fair-coin margin of the next section, over the period's
blocks.

Without the latch, blocks with few black phases outlast their length by far: one reading in nine is checked for
$000000001$, and its halves of 18 cells last up to 120 steps more. The latch checks the white phases as well: with
it the halves of $000000001$ last at most 29 steps past their length, for $M$ up to 47, and no half of any block more
than 35 steps, for $000001101$ at $M = 40$.

## Fair coins

Heuristic: if the readings past a half's length were fair coins, a sequence of $n$ more readings would be allowed with
probability about $2^{-(1-h)n}$, and the longest-lived of the $2^{hM}$ branches would last about $hM/(1 - h)$ steps past
$M$. Over the 91 blocks the margin at the largest $M$ is 0.74 to 1.31 times $hM/(1 - h)$, 1.00 on average, for the
checks alone, and 0.83 to 1.40 times, 1.03 on average, with the latch. The margins grow with $M$ at that rate, as they
do for the kit's C3 ([the C3 search](left-half-c3.md)), so nothing here suggests a finite certificate.

## Wider windows on the right

The latch is what a window of one cell right of the center sees. A window of $W$ cells, with cell $W + 1$ free,
allows fewer sequences of readings, and the entropy falls slowly with $W$ without reaching 0 by $W = 10$:

| block | checks alone | $W = 1$ (latch) | 2 | 4 | 6 | 8 | 10 |
|---|---|---|---|---|---|---|---|
| $001$ | 0.667 | 0.424 | 0.424 | 0.231 | 0.231 | 0.189 | 0.127 |
| $00001$ | 0.800 | 0.417 | 0.417 | 0.264 | 0.235 | 0.207 | 0.184 |
| $000001$ | 0.833 | 0.396 | 0.396 | 0.250 | 0.209 | 0.186 | 0.152 |
| $0000001$ | 0.857 | 0.375 | 0.375 | 0.143 | 0.116 | 0.105 | 0.091 |
| $000000001$ | 0.889 | 0.336 | 0.336 | 0.214 | 0.184 | 0.161 | 0.128 |
| $00111$ | 0.400 | 0.317 | 0.254 | 0.221 | 0.200 | 0.153 | 0.130 |
| $0110111$ | 0.286 | 0.286 | 0.207 | 0.207 | 0.176 | 0.151 | 0.138 |

This is the right channel of [the period-two finding](../period-two/right-channel.md), about 0.16 bit per step there,
seen through the readings of cell $-1$, and it agrees with [the window
locks](../../negative-results/columns/window-locks.md): a locked window would fix the readings at some phase, and none
of up to 18 cells does at these periods.

## What it means

Each statement `LeftLatch b` is open. The condition has infinite solutions for every block, every infinite branch of
the tree being one, so a proof has to use that the half is finite. The searches settle halves of at most $M$ cells,
which for the single cell are the times up to $M$, far inside the bound $T + P \ge 65{,}518$ of
[LongWindow](../../Rule30Open/Columns/LongWindow.md). Their value is as evidence: every block of the periods that no
window lock reaches behaves, on its left half, like the words of period four and two, whose statements the kit
states and which no small half meets either.

## Reproduce

```bash
python -m computations.left_halves --periods 3,5,6,7,9 --budget 16
python -m computations.left_halves --periods 3,5,6,7,9 --budget 16 --latch
python -m computations.left_halves --entropies 14
python -m computations.left_halves --blocks 001,00001,000001,0000001,000000001,00111,0110111 --window 10
```

[computations/left_halves.py](../../computations/left_halves.py) runs the first two in about 4 and 5 min on four
workers, the third in about 10 s and the fourth in about 15 s.
