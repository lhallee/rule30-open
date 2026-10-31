---
title: A second infinite right half that never enters the kit's family for 0001, a background of 80 cells
category: columns
problems: [1]
status: computed
formalization: partial
evidence: [computations/background_halves.py]
---

# A second infinite right half that never enters the kit's family for 0001, a background of 80 cells

The aligned ether is not the only infinite right half that stays out of the kit's ether-and-wall family. Rule 30 has a
background of period 8 on a ring of 80 cells ([the backgrounds](space-time-backgrounds.md)) with columns that repeat
$0001$. The game for $0001$ fails at every width through this background
([farther columns](../../negative-results/columns/jen-farther-columns.md)), and it is one of the ring orbits that
witness $0001$ ([ring orbits](../../negative-results/columns/ring-orbits.md)). The right half beside such a column,
driven by $0001$, stays in the background forever, so it repeats with period 8 in time. New here is that the half is
in the kit's family at none of its 8 phases. With $B(j, \varphi)$ column $j$ of the background at phase $\varphi$, the
background has a glide symmetry, $B(j + 10, \varphi) = B(j, \varphi + 1)$ on the whole table, so the 8 columns, each
read from 2 phases, give one driven half up to a time shift of 4 steps. Its truncations do enter: the half cut to $n$ cells, white beyond, enters at step $2.5n + 28$ or $2.5n + 61$,
depending on whether the cut is taken at time 0 or time 4 of the half, for $n$ = 80, 160, 320, 640 and 1,280. These
are first entries at a depth $k \le 51$, the depths `absorption.absorb` checks, so they bound the entry time from
above.

Through period 12 these are all the halves of this kind. Among the backgrounds of periods 4, 8 and 12, which
[the backgrounds](space-time-backgrounds.md) lists completely, a column repeats a word of period four only in the ether,
on 7 cells, and in the background of 80 cells, whose columns repeat $0001$ and never $0011$ or $0111$.

## Method

`word_columns` walks each cycle of the leftward column map of `space_time_periodic` and keeps the columns whose word is
a period-four word repeated. For each, `never_enters` reads the half beside the column at every phase of the
background. Membership in the family at depth $k$ needs the ether on columns 1 to $k$, and the half's longest prefix of
aligned ether is below 51 columns at every phase, so `absorption.family_depth`, which reads 64 columns, decides
membership at every depth; the ether's own halves are recognized as the aligned ether over a common period of the ring
and the ether. `entry_time` runs a truncation with `absorption.absorb`.

The statement that the half is in the family at none of its times is proved in Lean
([BackgroundHalves](../../Rule30Open/Columns/BackgroundHalves.md)): the half is the driven half of the kit, and for
every alignment of the ether, not only the kit's, it carries the ether on at most 7 columns, so no wall state
can follow an ether prefix. The entry times of the truncations, the wall search (`wall_set`) and the completeness of the list
of backgrounds are computed only.

## What it means

- **For the roadmap.** [The census](absorption-census.md) found the aligned ether as the only infinite half to stay
  out among those it tries (periodic halves of at most 11 cells, random halves); this background is a second. Any
  description of the infinite halves that never enter has to include this background as well as the ether.
- **For finite halves.** The background has no wall. Beside none of its 80 columns does a strip of 1 to 20 cells exist
  that the rule keeps, with that column on the background, for both values of the cell beyond (`wall_set`, which
  beside the ether's $B_3$ column gives the greatest wall set of `absorption.greatest_wall`, 433, 533, 344 and 605
  strips at phases 0 to 3, whose terminal component is the kit's 109 wall states). Beside the ether `wall_set` finds no
  wall at widths 1 to 12 and walls at widths 13 to 16; beside the stripe of 2 cells it finds walls at every width; the
  two period-8 backgrounds of 4 cells have none at widths 1 to 16. The entry times grow by 2.5 steps per cell for $n$ =
  80 to 1,280, so a disturbance on its right advances at about $2/5$ of a column per step (measured from entry times,
  not proved); the kit proves that a finite perturbation erodes the ether of period three at average speed at least
  $2/5$ (`erosion3_fin` in
  [`Rule30EtherThreeErosion`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30EtherThreeErosion.lean)).
  So it gives slow finite halves, not a counterexample to `Absorption`, and its truncations wait 2.5 steps per cell,
  far below the census's latest entries of about 55 steps per cell for $0001$.
- **For a compactness argument (a heuristic).** The halves that never enter form a closed set: entry at time $t$ and
  depth $k$ depends on finitely many cells of the half, so the set of halves that enter is open. A finite statement of
  the form "every half enters the family or reaches a long ether prefix within $T$ steps" would constrain that closed
  set, though no argument here takes such a statement to `Absorption`. This background is a second point of the closed
  set without an ether prefix, so any such statement needs it as a second target.

## Reproduce

```bash
python -m computations.background_halves 4,8,12 --truncate 80,160,320,640,1280 --steps 4000
python -m computations.background_halves 8 --walls 20
```

[computations/background_halves.py](../../computations/background_halves.py) runs them in about 35 s and 13 min.
[tests/test_background_halves.py](../../tests/test_background_halves.py) checks the ring against `step`, the halves
against direct runs with integer rows, one truncation's entry against a step-by-step run,
and `wall_set` against the ether's wall and a closure computed cell by cell.
