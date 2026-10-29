---
title: Every right half of up to eight cells enters the kit's trap for 001, some only after 10^5 steps
category: columns
problems: [1]
status: computed
formalization: partial
evidence: [computations/period_three.py]
---

# Every right half of up to eight cells enters the kit's trap for 001, some only after 10^5 steps

For the word $001$ of least period three the kit has a trap for the driven right half
([`Rule30EtherThreeTrap`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30EtherThreeTrap.lean),
`t001`): 815 states of a strip of 47 columns, of which the first 38 repeat with period 21 and the last 9 absorb every
input. Once a right half is in it, column 1 at the center's white times repeats, which masked Jen forbids in a finite
configuration, so $001$ is excluded if every finite right half enters (`AbsorptionT t001`, open). In Lean the white
half enters at step 1,270, 1,269 or 1,268 by phase ([EmptyRight](../../Rule30Open/Columns/EmptyRight.md)), and so does
every half white on its first 1,317 cells ([HighThree](../../Rule30Open/Columns/HighThree.md)). The kit reports by
computation that 18,258 tested halves entered, the slowest after about $2 \cdot 10^5$ steps. Here every right half of
at most eight cells is tested, exactly, in each phase.

## Census

Each half is stepped with the center repeating $001$ from the given phase, and is in the trap at the first step at which
its columns 1 to 47 are a state of `t001` whose label agrees with the drive's phase; the trap is closed, so it stays.

| phase | halves | entered | by step 1,300 | by 10,000 | by 50,000 | by 100,000 | median | latest |
|---|---|---|---|---|---|---|---|---|
| 0 | 256 | 256 | 23 | 80 | 237 | 251 | 16,808 | 172,529 |
| 1 | 256 | 256 | 19 | 74 | 234 | 255 | 17,330 | 110,529 |
| 2 | 256 | 256 | 16 | 70 | 234 | 254 | 20,307 | 108,771 |

Entry steps come in groups that differ by multiples of 3, such as 1,261, 1,264, 1,267 and 1,270 from phase 0: a half
whose row after three steps is another half of the census enters exactly three steps after that one.

## How entry happens

Within a few hundred steps the columns next to the center repeat with the trap's period 21, but only on at most the
first 17 of them, and disturbances from the disordered region beyond keep breaking that core, which then forms again. A
half enters when the repeating region grows past about 40 columns, where the trap's absorbing columns form. For the half
with column 2 black, from phase 0, the repeating region, sampled every 1,000 steps, reaches at most 17 columns before
step 34,000, often 0 or 1, and 45 columns at step 36,000, after entry at step 35,536 (`periodic_extent`).

## What it means

No small half stays out, so the census supports `AbsorptionT t001` as far as it goes. It also shows why the route is
hard in Lean: entry under $001$ is two orders of magnitude slower and far more spread out than under the words of period
four, where every half of 20 cells enters within 1,959 steps ([the absorption census](absorption-census.md)), and a
kernel check of one slow half costs a computation of the size of [LongWindow](../../Rule30Open/Columns/LongWindow.md).
The light cone of HighThree turns each entry at step $t$ into entry for every half that agrees on cells $1, \dots, t + 47$,
which for the slow halves asks for a white stretch of more than $10^5$ cells.

## Reproduce

```bash
python -m computations.period_three --trap --cells 8 --steps 300000
```

About four minutes. `trap_entries` reads the trap from the kit's source, and `periodic_extent` measures the repeating
region; tests/test_computations.py checks the white half's entry steps against the kit, the trap's closure against rows
stepped one at a time, and one slow entry.
