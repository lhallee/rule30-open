---
title: Every right half of up to ten cells enters the kit's trap for 001, some only after 10^5 steps
category: columns
problems: [1]
status: computed
formalization: partial
evidence: [computations/period_three.py, computations/lock_chain.py, computations/coin_lock.py]
---

# Every right half of up to ten cells enters the kit's trap for 001, some only after 10^5 steps

For the word $001$ of least period three the kit has a trap for the driven right half
([`Rule30EtherThreeTrap`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30EtherThreeTrap.lean),
`t001`): 815 states of a strip of 47 columns, of which the first 38 repeat with period 21 and the last 9 absorb every
input. Once a right half is in it, column 1 at the center's white times repeats, which masked Jen forbids in a finite
configuration, so $001$ is excluded if every finite right half enters (`AbsorptionT t001`, open). In Lean the white
half enters at step 1,270, 1,269 or 1,268 by phase ([EmptyRight](../../Rule30Open/Columns/EmptyRight.md)), and so does
every half white on its first 1,317 cells ([HighThree](../../Rule30Open/Columns/HighThree.md)). The kit reports by
computation that 18,258 tested halves entered, the slowest after about $2 \cdot 10^5$ steps. Here every right half of
at most ten cells is tested, exactly, in each phase.

## Census

Each half is stepped with the center repeating $001$ from the given phase, and is in the trap at the first step at which
its columns 1 to 47 are a state of `t001` whose label agrees with the drive's phase; the trap is closed, so it stays.

| phase | halves | entered | by step 1,300 | by 10,000 | by 50,000 | by 100,000 | median | mean | latest |
|---|---|---|---|---|---|---|---|---|---|
| 0 | 1,024 | 1,024 | 49 | 331 | 938 | 1,008 | 15,914 | 22,570 | 186,490 |
| 1 | 1,024 | 1,024 | 45 | 316 | 931 | 1,008 | 15,806 | 22,533 | 186,489 |
| 2 | 1,024 | 1,024 | 40 | 313 | 933 | 1,012 | 16,863 | 23,028 | 172,527 |

The halves of at most eight cells alone give the same picture: all 256 enter in each phase, the latest at step
172,529, 110,529 and 108,771, with medians 16,808, 17,330 and 20,307.

Entry steps come in groups that differ by multiples of 3, such as 1,258, 1,261, 1,264, 1,267 and 1,270 from phase 0
(2, 5, 8, 10 and 1 halves): a half whose row after three steps is another half of the census enters exactly three
steps after that one.

Heuristic: if a half outside the trap entered with the same small probability at every step after the first 1,260 or
so, entry times past that point would be exponential, and the mean excess over step 1,260 would be $1/\ln 2 \approx
1.44$ times the median excess. The census gives 1.45, 1.46 and 1.40 by phase (`constant_rate`). A constant rate fitted
to the mean leaves 1.0%, 1.0% and 1.1% of the halves out at step 100,000, where 1.6%, 1.6% and 1.2% are: the bulk fits
constant-rate entry, and the tail is somewhat heavier.

Heuristic: a fair coin in place of the cells beyond the trap enters it at about Rule 30's own rate. With cells 1 to 47
started as a half and cell 48 a fresh fair coin at every step, 50 runs of each half of at most eight cells from each
phase enter `t001` at a mean step of 25,735 and a median of 17,945 (`coin_entries`); the halves themselves, under Rule
30, enter at a mean of 22,825 and a median of 17,331 (`cut_entries`). Cut to its first $w$ cells, with the coin in cell
$w + 1$, the trap is entered at the same pace by both, within a factor of 2.1 at every width tried (the table below),
and the coin's exact rate per step, a factor of 0.98714 at 12 cells and 0.99734 at 20 on the chance of staying out
(`t001_coin`), gives mean times of 78 and 376 steps, in line with its runs. A coin conditioned on the phase and on up to
the last 12 cells of a window of 16, 18 or 20 cells, with chances counted over the 16,512,927 steps that the halves of
at most eight cells spend outside the trap within 50,000 steps, changes the rate of entry into the trap cut to the
window by 27% at most (`conditioned_coin`). As far as entry into `t001` goes, the cells beyond the trap behave like fair
coins. This is a heuristic: a finite half is one sequence, and no theorem says its cells behave like coins.

## How entry happens

Within a few hundred steps the columns next to the center repeat with the trap's period 21, but only on at most the
first 17 of them, and disturbances from the disordered region beyond keep breaking that core, which then forms again. A
half enters when the repeating region grows past about 40 columns, where the trap's absorbing columns form. For the half
with column 2 black, from phase 0, the repeating region, sampled every 1,000 steps, reaches at most 17 columns before
step 34,000, often 0 or 1, and 45 columns at step 36,000, after entry at step 35,536 (`periodic_extent`). The first
step at which a half's first $w$ cells are those of a state of `t001` with the right label shows where the time goes,
for the 768 halves of at most eight cells and phases, and for the coin in cell $w + 1$ started from them:

| cells $w$ | 12 | 16 | 20 | 24 | 28 | 30 | 32 | 34 | 36 | 40 | 47 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Rule 30, mean | 119 | 190 | 356 | 1,221 | 2,424 | 9,411 | 12,720 | 21,233 | 21,645 | 22,567 | 22,825 |
| Rule 30, median | 80 | 140 | 250 | 1,040 | 1,883 | 8,710 | 9,270 | 16,457 | 16,725 | 17,324 | 17,331 |
| coin, mean | 87 | 273 | 420 | 1,115 | 4,859 | 8,481 | 9,132 | 23,862 | 32,151 | 33,986 | 25,735 |
| coin, median | 63 | 189 | 305 | 846 | 3,425 | 5,972 | 6,380 | 16,682 | 22,384 | 23,736 | 17,945 |

A half has the trap's first 20 cells within a few hundred steps and its first 34 only after some 20,000: entry is slow
because the trap is wide.

## What it means

No small half stays out, but entry for every finite half, the kit's `AbsorptionT t001`, is false: a half of 52 cells
that starts inside the second trap for $001$ of [WordTraps](../../Rule30Open/Columns/WordTraps.md), with labels modulo
15, stays in it and never enters `t001` ([Traps001](../../Rule30Open/Columns/Traps001.md), in Lean). No half of the
census does that. Two more traps for $001$, of 144 and 304 cells, make entry into one of any three of the four false
too, and the route for $001$ becomes entry into one of the four, or into some trap of $001$, which is open. The census
also shows why the route is hard in Lean: entry under $001$ is two orders of magnitude slower and far more spread out
than under the words of period four, where every half of 20 cells enters within 1,959 steps ([the absorption
census](absorption-census.md)), and a kernel check of one slow half costs a computation of the size of
[LongWindow](../../Rule30Open/Columns/LongWindow.md). The light cone of HighThree turns each entry at step $t$ into
entry for every half that agrees on cells $1, \dots, t + 47$, which for the slow halves asks for a white stretch of more
than $10^5$ cells.

## Reproduce

```bash
python -m computations.period_three --trap --cells 10 --steps 400000
```

```bash
python -m computations.period_three --cut-profile --cells 8 --steps 2000000
```

```bash
python -m computations.period_three --conditioned-coin 20 --cells 8 --steps 50000
```

```bash
python -m computations.lock_chain --t001-coin
```

The census takes about eight minutes; `--cells 8 --steps 300000` takes about four. `trap_entries` reads the trap from
the kit's source, and `periodic_extent` measures the repeating region; tests/test_computations.py checks the white
half's entry steps against the kit, the trap's closure against rows stepped one at a time, one slow entry, and
`constant_rate` against values computed by hand and against the exponential law. The table takes about six minutes;
`test_cut_entries` checks `cut_entries` against halves stepped cell by cell and looked up among the cut states, and
`test_coin_entries` checks the coin's runs at 10 cells against its exact mean, summed from the chance of staying out.
The conditioned coin takes about 1.5, 3 and 13 minutes at 16, 18 and 20 cells (`--conditioned-coin 16`, `18`, `20`);
`test_beyond_stats` checks its counts against a direct count and `test_biased_rate` its rate. The coin's exact factors
take about a minute and a half; `test_t001_coin` checks them at 8 and 10 cells against the spectral radius of the coin's
step built cell by cell.
