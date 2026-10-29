---
title: Driven by 011, the right half does not settle next to the center
category: columns
problems: [1]
status: negative
kind: no-signal
evidence: [computations/period_three.py]
---

# Driven by 011, the right half does not settle next to the center

**Question.** Least period three has two words, $001$ and $011$. For $001$ the kit has a trap that the driven right
half enters
([`Rule30EtherThreeTrap`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30EtherThreeTrap.lean)):
a strip of 47 columns that repeats with period 21, on which column 1 at the center's white times is a function of the
label. Masked Jen forbids that column to be periodic in a finite configuration, so $001$ is excluded once every finite
half enters (`AbsorptionT t001`, open), and [HighThree](../../Rule30Open/Columns/HighThree.md) proves entry for every
half white on its first 1,317 cells. For $011$ the kit has only a statement about the left half, `C3w`, and no trap.
Does the right half driven by $011$ settle into anything that would give $011$ the same route?

**Method.** Drive right halves with the center repeating the word from each of its three phases, record column 1, and
ask two things: at each phase of the drive, whether column 1 is constant over the second half of the run; and whether
column 1 at the center's white times repeats, over the last third of those samples, with any period that fits. A trap
of the kind of `t001` makes it repeat once entered. The runs are every right half of at most 12 cells for 6,000 steps,
every half of at most 8 cells for 30,000 steps, and the white half with 11 random halves of 24 cells for 100,000 steps.
The same runs for $001$ are the control.

**Outcome.**

| word | halves, steps | column 1 at the white times repeats |
|---|---|---|
| $011$ | 4,096 × 3 phases, 6,000 | none |
| $011$ | 256 × 3 phases, 30,000 | none |
| $011$ | 12 × 3 phases, 100,000 | none |
| $001$ | 4,096 × 3 phases, 6,000 | 2,848, with period 14 samples except 3 |
| $001$ | 256 × 3 phases, 30,000 | 421, all with period 14 samples |
| $001$ | 12 × 3 phases, 100,000 | 35, all with period 14 samples |

Under $011$, at the two black phases column 1 is constant in every run, black at the first and white at the second,
as the kit's `skeleton_011` forces; at the white phase it is black about 82% of the time and never settles. Under
$001$ the period of 14 white samples is the 21 steps of `t001`, and the halves that have not settled are slow, not
different: the kit reports entries after about $2 \cdot 10^5$ steps. The three halves of 12 cells that repeat at first
with periods of 1,378 to 2,448 samples settle into period 14 by step 16,320 and keep it to step 200,000.

**What it means.** Next to the center the right half driven by $011$ never repeats exactly where masked Jen would need
it periodic, at the white phase, while the two black phases force column 1 without giving anything. So the right half
offers $011$ no trap of the kind of `t001` in this range, and the kit's ether-and-wall route is closed for period three
(`Rule30EtherThreeErosion`). The route for $011$ is the left half: `C3w`, for which the kit reports by computation that
every start of width at most 70 fails within 99 steps. The search covers the runs above only: a trap entered after
100,000 steps, or only by larger halves, is not excluded.

**Reproduce.**

```bash
python -m computations.period_three --cells 12 --steps 6000
python -m computations.period_three --cells 8 --steps 30000
python -m computations.period_three --long 100000
python -m computations.period_three --follow 2351:0 3682:2 4033:2 --steps 200000
```

The first three take about three minutes each and the last about 15 seconds.
