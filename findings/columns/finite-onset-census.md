---
title: Against a right half of at most 11 to 14 cells, no left half of fewer than 1,000 cells keeps the center on a block of period 2, 3, 5, 6, 7 or 9
category: columns
problems: [1]
status: computed
formalization: wanted
evidence: [computations/finite_onset.py, computations/coupled.py]
---

# Against a right half of at most 11 to 14 cells, no left half of fewer than 1,000 cells keeps the center on a block of period 2, 3, 5, 6, 7 or 9

An eventually periodic center column of a finite configuration repeats its block from time 0 in the row at its onset,
and that row is finite on both sides. The kit states this as one open question per periodic column,
[`Rule30Coupled.CQ`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Coupled.lean)
(`CQ_iff_no_finite_config`: no finite configuration has that center column). The finite game reaches no block of period
2, 3, 5, 6, 7 or 9 ([the roadmap](../../ROADMAP.md)). For each of the 92 primitive blocks of those periods, in every
phase, and every right half of at most $k$ cells ($k = 14$ at periods 2, 3 and 5, 13 at 6, 12 at 7 and 11 at 9;
2,613,248 cases), the one left half that keeps the center on the block, computed to depth 1,024, has a black cell at
depth 1,000 or beyond and no white run longer than 28. So **every finite row whose center repeats one of these blocks
from time 0, whose right half has at most $k$ cells and whose left half lies within depth $W < 1{,}000$ leaves the block
by time $W + 29$**. No case has a white tail, the sign a finite onset row would leave. Of the 3,190 candidates that
repeat over depths 513 to 1,024, the 915 that still repeat at depth 4,096 are all of the alternating block, where [the
gate census](../period-two/gate-census.md) finds locks; for the other blocks the repetition breaks, so it is not a trap.

## The one candidate

Fix the block $b$, a phase, and the right half $R$ at time 0. The right half evolves as the half driven by the
center, so its column 1 is known; the center's update forces column $-1$; and Rule 30 is permutive in its left input,
so columns 0 and $-1$ rebuild every column to the left. The row at time 0 that results, $\Psi_b(R)$, is the only left
half that keeps the center on $b$ against $R$, and a left half that first differs from it at depth $d$ keeps the
center on $b$ through time $d - 1$ and leaves it at time $d$. For the alternating block these are the kit's `Psi`,
`Psi_unique` and `exact_death_center` (`Rule30PeriodTwoSideways`); the argument uses only left permutivity, and
[coupled.py](../../computations/coupled.py) computes $\Psi_b$ for any word ([the white right
half](../period-two/white-right-half.md)). A finite onset row with right half $R$ exists exactly when $\Psi_b(R)$ is
white beyond some depth. A left half of width $W$ below the last black depth of $\Psi_b(R)$ differs from it by the
first black depth past $W$, at most $W + r + 1$ where $r$ is the longest white run.

## Result

[finite_onset.py](../../computations/finite_onset.py) computes $\Psi_b(R)$ for all right halves of a block at once as
bit slices and sorts each case: *locked* when its outer half (depths 513 to 1,024) repeats with a period of at most
128, *white tail* when its outer half is white, and otherwise *aperiodic*. Of the 2,613,248 cases, 3,190 are locked,
none has a white tail, and 2,610,058 are aperiodic. Over every case of each block, the longest white run (ending in a
black cell) and the least last black depth:

| block | run | last | block | run | last | block | run | last | block | run | last |
|---|---|---|---|---|---|---|---|---|---|---|---|
| $01$ | 22 | 1,010 | $001$ | 24 | 1,011 | $011$ | 25 | 1,008 | $00001$ | 22 | 1,009 |
| $00011$ | 23 | 1,007 | $00101$ | 26 | 1,010 | $00111$ | 24 | 1,009 | $01011$ | 24 | 1,009 |
| $01111$ | 25 | 1,000 | $000001$ | 22 | 1,011 | $000011$ | 23 | 1,008 | $000101$ | 21 | 1,007 |
| $000111$ | 23 | 1,010 | $001011$ | 22 | 1,012 | $001101$ | 22 | 1,010 | $001111$ | 21 | 1,009 |
| $010111$ | 24 | 1,011 | $011111$ | 20 | 1,007 | $0000001$ | 20 | 1,009 | $0000011$ | 25 | 1,011 |
| $0000101$ | 24 | 1,010 | $0000111$ | 23 | 1,010 | $0001001$ | 22 | 1,012 | $0001011$ | 20 | 1,011 |
| $0001101$ | 24 | 1,011 | $0001111$ | 22 | 1,011 | $0010011$ | 28 | 1,011 | $0010101$ | 23 | 1,012 |
| $0010111$ | 20 | 1,011 | $0011011$ | 23 | 1,011 | $0011101$ | 21 | 1,010 | $0011111$ | 23 | 1,008 |
| $0101011$ | 24 | 1,010 | $0101111$ | 27 | 1,013 | $0110111$ | 21 | 1,010 | $0111111$ | 20 | 1,011 |
| $000000001$ | 24 | 1,012 | $000000011$ | 21 | 1,011 | $000000101$ | 22 | 1,011 | $000000111$ | 23 | 1,011 |
| $000001001$ | 22 | 1,013 | $000001011$ | 19 | 1,012 | $000001101$ | 21 | 1,011 | $000001111$ | 21 | 1,013 |
| $000010001$ | 24 | 1,010 | $000010011$ | 22 | 1,012 | $000010101$ | 21 | 1,012 | $000010111$ | 21 | 1,011 |
| $000011001$ | 20 | 1,010 | $000011011$ | 21 | 1,014 | $000011101$ | 24 | 1,013 | $000011111$ | 20 | 1,012 |
| $000100011$ | 26 | 1,012 | $000100101$ | 23 | 1,010 | $000100111$ | 21 | 1,006 | $000101001$ | 23 | 1,013 |
| $000101011$ | 25 | 1,011 | $000101101$ | 24 | 1,011 | $000101111$ | 21 | 1,011 | $000110011$ | 21 | 1,011 |
| $000110101$ | 20 | 1,012 | $000110111$ | 22 | 1,013 | $000111001$ | 21 | 1,009 | $000111011$ | 20 | 1,013 |
| $000111101$ | 21 | 1,009 | $000111111$ | 24 | 1,012 | $001001011$ | 23 | 1,010 | $001001101$ | 25 | 1,011 |
| $001001111$ | 20 | 1,010 | $001010011$ | 22 | 1,010 | $001010101$ | 22 | 1,010 | $001010111$ | 22 | 1,013 |
| $001011011$ | 24 | 1,012 | $001011101$ | 24 | 1,013 | $001011111$ | 23 | 1,009 | $001100111$ | 22 | 1,012 |
| $001101011$ | 21 | 1,009 | $001101101$ | 22 | 1,009 | $001101111$ | 21 | 1,012 | $001110101$ | 21 | 1,012 |
| $001110111$ | 24 | 1,012 | $001111011$ | 22 | 1,006 | $001111101$ | 22 | 1,012 | $001111111$ | 20 | 1,009 |
| $010101011$ | 21 | 1,012 | $010101111$ | 21 | 1,011 | $010110111$ | 28 | 1,012 | $010111011$ | 19 | 1,008 |
| $010111111$ | 21 | 1,012 | $011011111$ | 20 | 1,008 | $011101111$ | 22 | 1,011 | $011111111$ | 21 | 1,007 |

By period, the longest white runs are 22 (period 2), 24 to 25 (3), 22 to 26 (5), 20 to 24 (6), 20 to 28 (7) and 19 to
28 (9), and the least last black depths 1,010, 1,008 to 1,011, 1,000 to 1,010, 1,007 to 1,012, 1,008 to 1,013 and
1,006 to 1,014.

Heuristic: among $n$ fair coin flips the longest run of tails is about $\log_2 n$, here 24 to 26 for the cells of one
block's cases and 31 for all of them, against 19 to 28 per block and 28 overall. The candidates look random.

## The locked cases are not traps, except for the alternating block

A locked case is followed to depth 4,096: it persists if $\Psi_b(R)$ still repeats there and column 1 repeats over the
outer half of the times too, and otherwise the depth at which its repetition first fails is recorded.

| block | locked | periods | persist | repetition fails at depth |
|---|---|---|---|---|
| $01$ | 915 | 7, 14, 28 | 915 | |
| $00011$ | 29 | 64 | 0 | 1,036 to 1,336 |
| $0000001$ | 70 | 15 | 0 | 1,027 to 1,630 |
| $0000011$ | 16 | 15 | 0 | 1,049 to 1,127 |
| $0000101$ | 24 | 15 | 0 | 1,037 to 1,570 |
| $0001001$ | 16 | 15 | 0 | 1,034 to 1,456 |
| $0001011$ | 385 | 15 | 0 | 1,025 to 2,198 |
| $0001101$ | 237 | 15 | 0 | 1,025 to 2,947 |
| $0001111$ | 23 | 15 | 0 | 1,042 to 1,598 |
| $0010011$ | 3 | 15 | 0 | 1,187 to 1,188 |
| $0010101$ | 13 | 15 | 0 | 1,099 to 1,460 |
| $0011011$ | 5 | 15 | 0 | 1,043 to 1,311 |
| $0011101$ | 456 | 15, 84 | 0 | 1,028 to 4,026 |
| $0011111$ | 42 | 15 | 0 | 1,033 to 1,595 |
| $0101011$ | 450 | 15 | 0 | 1,025 to 2,193 |
| $0101111$ | 261 | 15 | 0 | 1,025 to 2,954 |
| $0110111$ | 143 | 15 | 0 | 1,028 to 1,949 |
| $0111111$ | 102 | 15 | 0 | 1,029 to 2,204 |

For $01$ the right half has settled, as far as depth 4,096 shows: column 1 repeats over the outer half of the times to
4,096, and $\Psi$ repeats with period 7, 14 or 28. Every right half of up to 20 cells enters the gap trap, the kit's
ether family or a lock of period seven ([the gate census](../period-two/gate-census.md)), and the last two leave column
1 periodic and exclude the half for every finite left half, the lock in Lean
([SevenLock](../../Rule30Open/PeriodTwo/SevenLock.md)); the census does not check which of them each locked case is in.
For the blocks of periods 5 and 7 the candidate only passes through a stretch that repeats, mostly with period 15, for a
few hundred to a few thousand cells, and then leaves it; 15 is also the spatial period of Rule 30's backgrounds of
temporal period 7 ([space-time backgrounds](space-time-backgrounds.md)), though the census does not check that the
stretches are such backgrounds. A repeating stretch at depth 1,024 is therefore no evidence of a trap.

For $001$ no case locks, although every right half of at most ten cells enters the kit's trap `t001` ([the t001
census](t001-census.md)) and the white one is excluded in Lean ([EmptyRight](../../Rule30Open/Columns/EmptyRight.md)):
in `t001` what repeats is column 1 at the center's white times, which need not make $\Psi$ repeat, and
$\Psi_{001}(\emptyset)$ shows no repetition to depth 32,768 either.

## The white right half alone

$\Psi_b(\emptyset)$ to depth 32,768 (`empty`): for $011$ its longest white runs by phase are 15, 13 and 13 and its last
black depths 32,768, 32,764 and 32,768, so a finite configuration with a white right half and a left half within depth
$W < 32{,}764$ leaves $011$ by time $W + 16$. For $001$ the runs are 12, 12 and 13, beside the proof of EmptyRight.

## What it means

This settles bounded cases only. For each block, the open statement is that $\Psi_b(R)$ is not eventually white for
any finite $R$, the same kind of statement as the kit's `CQ01Empty` for $01$, and the census finds nothing that could
prove it: the candidates have the statistics of coin flips, and their repeating stretches break. The census also covers
only rows whose right half is small at the onset. The single black cell's row at time $T_0$ has $T_0$ cells on each
side, so for the prize problem itself it reaches only onsets $T_0 \le 14$, far below the $T + P \ge 262{,}125$ of
[WideWindow](../../Rule30Open/Columns/WideWindow.md); its content is the finite-row form of Problem 1. The same question
from the other side, with the right half free, is [the left-half statement of every
block](left-half-every-block.md); with both halves free and the onset later than time 0 it is [late
onsets](../../negative-results/columns/late-onset.md).

A formal step within reach is [WhiteRightHalf](../../Rule30Open/PeriodTwo/WhiteRightHalf.md) for $011$: computing
$\Psi_{011}(\emptyset)$ in the kernel to depth 32,768 and checking that every 16 consecutive depths hold a black cell
would show that every finite configuration with a white right half and a left half within depth $W < 32{,}752$ leaves
$011$ within 16 steps past its width.

## Reproduce

```bash
python -m computations.finite_onset census --depth 1024 --more 2   # the census above, about 3 min
python -m computations.finite_onset census --depth 1024            # k two cells smaller, 653,312 cases, 30 s
python -m computations.finite_onset block 0011101 --cells 12 --depth 1024
python -m computations.finite_onset empty 011 --depth 32768        # 1 s
```

The tests check the bit slices against `coupled.psi`, the best left half of up to eight cells against direct runs of
every whole finite row, the census's statistics against `coupled.white_runs`, a white tail on a row finite by
construction, and the persistence and failure of locks against the big-integer $\Psi$.
