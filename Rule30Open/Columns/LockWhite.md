---
title: Once the center repeats one of 22 blocks, a column near it is never white for long
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.LockWhite
headline: [center_white_run, whiteRuns_check, center_white_runs, not_eventually_white_runs]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/locks.py]
---

# Once the center repeats one of 22 blocks, a column near it is never white for long

For 22 blocks of period 8 to 12, a run of white cells in a column near the center forces the lock of
[LockBlocks](LockBlocks.md): once the center column of the single cell repeats the block, in any rotation, column
$W + 1$ is black at least once in every $L$ consecutive steps, for a window of $W$ cells and a run of $L$ given below
(`center_white_runs`). The shortest run is 27, in column 8, for $000011111111$. So if column $W + 1$ has $L$ white
cells in a row at arbitrarily late times, the center column does not eventually repeat the block
(`not_eventually_white_runs`). Four of the 22 blocks have no run of more than four equal values.

## Statement

A `WhiteRun` entry is a block `wordOf P bits`, a width $W$, a length $L$ and the windows where $L$ white values of
column $W + 1$ leave the windows started at each phase. Its check is `lockCheckB` of [LockBlocks](LockBlocks.md) with
the white sequence, so `center_white_run` follows from `center_lockBlock`: if the check passes and the center column
repeats the block from time $T$, read from phase $s$, then for every $t_0 \ge T$ some cell of column $W + 1$ at the times
$t_0, \dots, t_0 + L - 1$ is black. `whiteRuns` lists 22 entries and `whiteRuns_check` says each check passes:

| Block | Longest run | Column | White run |
|---|---:|---:|---:|
| $00000101$ | 5 | 13 | 130 |
| $00111101$ | 4 | 10 | 85 |
| $00111111$ | 6 | 13 | 66 |
| $0001111111$ | 7 | 13 | 92 |
| $0011111101$ | 6 | 10 | 86 |
| $00000011101$ | 6 | 10 | 44 |
| $00001101011$ | 4 | 11 | 111 |
| $00001111111$ | 7 | 10 | 72 |
| $00011111111$ | 8 | 14 | 161 |
| $000000001011$ | 8 | 13 | 36 |
| $000000010001$ | 7 | 13 | 119 |
| $000000011101$ | 7 | 9 | 52 |
| $000000110011$ | 6 | 9 | 67 |
| $000001001101$ | 5 | 13 | 302 |
| $000001101011$ | 5 | 13 | 125 |
| $000010010001$ | 4 | 11 | 88 |
| $000011011011$ | 4 | 13 | 142 |
| $000011111111$ | 8 | 8 | 27 |
| $001011111011$ | 5 | 8 | 82 |
| $001100111111$ | 6 | 13 | 120 |
| $001111111101$ | 8 | 8 | 41 |
| $011101111111$ | 7 | 8 | 72 |

## Argument

1. **White alone.** While column $W + 1$ is white, the window of $W$ cells beside the repeating column is a closed
   system: the cell next to column $W + 1$ steps as $x_{t+1}(W) = x_t(W - 1) \oplus x_t(W)$. With the block's phase it
   is a function on the nodes of the finite game, and `constant_steering` in
   [computations/locks.py](../../computations/locks.py) finds the least $L$ after which every node has reached a locked
   node, as the largest distance to the locked nodes backward along that function.
2. **The width.** Moving the column changes the system, and the least $L$ is not monotone in $W$: for $000000001011$
   it is 54, 39, 55, 44, 36 and 82 at widths 8 to 13. `white_run` takes the width from 4 to 16 with the least $L$.
3. **Lean.** The kernel runs `lockCheckB` on each entry, which runs every window of every start phase through the white
   run as bit slices, matches the result against the listed windows, and checks that their forward closure is closed
   and fixes column $-1$ at each phase; `center_lockBlock` and Jen's theorem on adjacent columns do the rest.

The module builds in about 70 seconds with a peak near 1.6 GB.

## Seven more by computation

Seven more of the 49 blocks of [LockBlocks11](LockBlocks11.md) and [LockBlocks12](LockBlocks12.md) are steered by white
alone only at widths 14 to 16: $00011111$ (column 16, 200 values), $00000000101$ (column 15, 169),
$00111111101$ (column 17, 167), $000101011111$ (column 17, 396), $001001101111$ (column 16, 300), $010101010111$
(column 17, 496) and $010111111011$ (column 17, 228). At these widths the kernel's tables hold $P \cdot 2^{W+2}$ bits
and the check went past 12 GB, so they are left to the computation. The other 20 of the 49 are steered by white at no
width from 4 to 16.

## What it means

These are sufficient conditions of the kind [the steerable locks](../../findings/columns/steerable-locks.md) give, with
the simplest sequence: a column that has every finite pattern at arbitrarily late times has white runs of every length,
so it would exclude all 22 blocks, and so would much less, a white run of 27 in column 8 at arbitrarily late times for
$000011111111$. A run of $L$ white cells in a column of a random-looking row occurs about once in $2^{L+1}$ steps, so
runs this long are far beyond what a computation of the true row can show, and the condition is open.

## Relation to the kit

The kit's results on white runs exclude center words with long white runs, such as $0^r 1 1$ for $r \ge 8$
(`Rule30WhiteRunEight`), and its white-pulse lemmas follow a black run in the first column right of the center
(`Rule30WhitePulse`). It has no statement that ties white runs in a column beside the center to a repeating center.
