# Catalog

Every result in this repository, by category. `python scripts/catalog.py write` generates this page from the
front matter of the entries; edit the entries, not this page.

25 Lean modules with 119 headline theorems, 19 findings (proved on paper,
computed or conjectured) and 27 negative results. Prize problem 1 asks whether the center column
is eventually periodic, 2 whether its density of black cells tends to 1/2, and 3 whether computing its cell `n`
takes effort of order `n`.

| Category | Lean modules | Findings | Negative results |
|---|---:|---:|---:|
| [Foundations](#foundations) | 3 | 0 | 0 |
| [Seeds](#seeds) | 1 | 1 | 0 |
| [Columns](#columns) | 15 | 6 | 4 |
| [Period two](#period-two) | 2 | 4 | 3 |
| [Diagonals](#diagonals) | 1 | 1 | 0 |
| [Frames and the seed's past](#frames-and-the-seeds-past) | 0 | 3 | 1 |
| [Sibling rules](#sibling-rules) | 2 | 0 | 1 |
| [Dynamics of the two halves](#dynamics-of-the-two-halves) | 0 | 1 | 3 |
| [Hidden structure](#hidden-structure) | 0 | 2 | 5 |
| [Random rows](#random-rows) | 1 | 0 | 1 |
| [Statistics](#statistics) | 0 | 0 | 2 |
| [Learned models](#learned-models) | 0 | 0 | 2 |
| [Complexity](#complexity) | 0 | 1 | 5 |

## Open work

From the findings' front matter. Before starting in a category, read its negative results: each says where an
approach stopped.

**Conjectures to prove or refute**

- [The three words of period four lock the right half](findings/columns/period-four-locking.md): problem 1

**Findings that want a Lean proof**

- [Every window can reach the period-four certificate, so a fair coin beyond it locks the right half](findings/columns/coin-lock.md): problem 1
- [No left half of up to 80 cells meets the kit's C3 for a period-four word](findings/columns/left-half-c3.md): problem 1
- [A width-16 window certifies the period-four lock from most starts](findings/columns/period-four-certificate.md): problem 1
- [Only the stripe and the ether backgrounds give a periodic column](findings/frames/periodic-backgrounds.md): problem 1
- [The single cell has a unique past, and every row of it is periodic](findings/frames/seed-past.md): problem 1
- [No row with its leftmost 1 within 120 cells has an alternating center](findings/period-two/alternating-within-120.md): problem 1
- [Against a white right half, no left half of fewer than a million cells keeps the center alternating](findings/period-two/white-right-half.md): problem 1

**Findings proved in Lean in part**

- [Every right half of up to 20 cells enters the kit's ether-and-wall family](findings/columns/absorption-census.md): problem 1
- [The finite game excludes 197 of the 8,800 blocks up to period 16](findings/columns/game-blocks.md): problem 1
- [Problems 1 and 3 follow from space lower bounds for the center column, and space √n log n suffices](findings/complexity/space-ladder.md): problems 3, 1
- [Where the left diagonals turn white, to depth 100,000](findings/diagonals/left-records.md): problem 1
- [Information reaches the center from the left at speed 1, from the right at about 0.4](findings/dynamics/one-way-valve.md): problems 1, 2
- [Every integer below 2^52 fails the period-two condition, near step 2M](findings/period-two/left-half-alone.md): problem 1
- [No other right extension up to 40 cells keeps the center column](findings/seeds/no-other-extensions.md): problems 1, 2, 3

## Foundations

The definitions every module uses, the bridge to the prize's official statements, and finite windows of a row.

**Proved in Lean**

| Result | Module | Headline theorems | Problems | Kit |
|---|---|---|---|---|
| [Rule 30 from any row, and its one-step facts](Rule30Open/Foundations/Evolve.md) | [`Foundations.Evolve`](Rule30Open/Foundations/Evolve.lean) | `left_cell`, `left_edge`, `left_of_one`, `left_of_alternating` | 1, 2, 3 | extends a kit result |
| [The bridge to the official definitions](Rule30Open/Foundations/Official.md) | [`Foundations.Official`](Rule30Open/Foundations/Official.lean) | `evolve_single_eq_cell`, `evolve_single_center` | 1, 2, 3 | connects to the kit |
| [Finite windows of a row](Rule30Open/Foundations/RightHalf.md) | [`Foundations.RightHalf`](Rule30Open/Foundations/RightHalf.lean) | `driveStep_cells`, `drive_cells`, `mem_allLists` | 1 | independent proof of a kit result |

## Seeds

Initial rows that give exactly the center column of the single black cell.

**Proved in Lean**

| Result | Module | Headline theorems | Problems | Kit |
|---|---|---|---|---|
| [Infinitely many seeds share the center column](Rule30Open/Seeds/SeedExtensions.md) | [`Seeds.SeedExtensions`](Rule30Open/Seeds/SeedExtensions.lean) | `center_sigma`, `center_tau`, `sigma_difference`, `tau_difference`, `center_column` | 1, 2, 3 | independent proof of a kit result |

**Findings**

| Result | Status | Problems | Formalization |
|---|---|---|---|
| [No other right extension up to 40 cells keeps the center column](findings/seeds/no-other-extensions.md) | computed | 1, 2, 3 | partial |

## Columns

What an eventually periodic column forces on its neighbors, and which eventual periods that excludes.

**Proved in Lean**

| Result | Module | Headline theorems | Problems | Kit |
|---|---|---|---|---|
| [No two adjacent columns are eventually periodic](Rule30Open/Columns/AdjacentColumns.md) | [`Columns.AdjacentColumns`](Rule30Open/Columns/AdjacentColumns.lean) | `adjacent_columns`, `no_constant_column`, `center_not_eventually_constant` | 1 | independent proof of a kit result |
| [Against a right half of at most six cells no center column repeats a word of period four](Rule30Open/Columns/EmptyRight.md) | [`Columns.EmptyRight`](Rule30Open/Columns/EmptyRight.lean) | `smallRight_0001`, `smallRight_0011`, `smallRight_0111`, `emptyRight_001`, `no_finite_of_family`, `no_finite_of_ptrap` | 1 | extends a kit result |
| [The word 0001 comes down to the period-two map, and the ether is its domain](Rule30Open/Columns/EtherDomain.md) | [`Columns.EtherDomain`](Rule30Open/Columns/EtherDomain.lean) | `center_period_four_0001_integer`, `period_four_0001_held`, `held_etherLeft`, `ether_fits`, `ether_countdown`, `domainB_repeats` | 1 | extends a kit result |
| [Every truncation of the aligned ether, followed by a short word, enters the ether-and-wall family](Rule30Open/Columns/EtherPrefix.md) | [`Columns.EtherPrefix`](Rule30Open/Columns/EtherPrefix.lean) | `shift7_drv`, `shift7_family`, `prefix_absorption`, `etherPrefix_0001`, `etherPrefix_0011`, `etherPrefix_0111`, `prefixRight_0001`, `prefixRight_0011`, `prefixRight_0111` | 1 | extends a kit result |
| [A finite game rules out repeating blocks](Rule30Open/Columns/FiniteGame.md) | [`Columns.FiniteGame`](Rule30Open/Columns/FiniteGame.lean) | `game_column`, `center_not_01111111`, `center_not_00000011` | 1 | independent proof of a kit result |
| [The finite game, checked in bit masks, excludes 32 more blocks of period at most 14](Rule30Open/Columns/GameBlocks.md) | [`Columns.GameBlocks`](Rule30Open/Columns/GameBlocks.lean) | `mask_column`, `center_not_gameBlocks`, `not_eventually_gameBlocks` | 1 | not in the kit |
| [The finite game, checked in bit masks, excludes 97 more blocks of period 15 and 16](Rule30Open/Columns/GameBlocksLong.md) | [`Columns.GameBlocksLong`](Rule30Open/Columns/GameBlocksLong.lean) | `center_not_gameBlocks16`, `not_eventually_gameBlocks16` | 1 | not in the kit |
| [A right half white on its first 1,317 cells enters the kit's trap for 001](Rule30Open/Columns/HighThree.md) | [`Columns.HighThree`](Rule30Open/Columns/HighThree.lean) | `highRight3_of_entry`, `highRight_001` | 1 | extends a kit result |
| [The kicked form of the left half](Rule30Open/Columns/KickedForm.md) | [`Columns.KickedForm`](Rule30Open/Columns/KickedForm.lean) | `left_kicked_zero`, `left_kicked_succ`, `left_kicked_check`, `period_two_golden` | 1 | extends a kit result |
| [Runs of nine 1s rule out a periodic column](Rule30Open/Columns/LongRuns.md) | [`Columns.LongRuns`](Rule30Open/Columns/LongRuns.lean) | `wall_check`, `long_runs_column`, `center_long_runs` | 1 | independent proof of a kit result |
| [An eventual period of the center column needs T + P of at least 65,518](Rule30Open/Columns/LongWindow.md) | [`Columns.LongWindow`](Rule30Open/Columns/LongWindow.lean) | `center_eq_big`, `factor_new`, `transient_add_period_ge_65518` | 1 | extends a kit result |
| [The cells left of a column count down its runs of 1s](Rule30Open/Columns/RunCountdown.md) | [`Columns.RunCountdown`](Rule30Open/Columns/RunCountdown.lean) | `run_countdown`, `run_bound`, `no_ones_column`, `center_not_eventually_ones` | 1 | extends a kit result |
| [A right half with at most two black cells among its first cells enters the ether-and-wall family](Rule30Open/Columns/SparseRight.md) | [`Columns.SparseRight`](Rule30Open/Columns/SparseRight.lean) | `inFamily_of_fast`, `stateAt_eq`, `two_absorption`, `sparse_0001`, `sparse_0011`, `sparse_0111`, `oneCell_0011`, `oneCell_0111`, `sparseRight_0001`, `sparseRight_0011`, `sparseRight_0111` | 1 | extends a kit result |
| [A right half white past its first ten cells enters the ether-and-wall family, whatever lies beyond the gap](Rule30Open/Columns/TenCells.md) | [`Columns.TenCells`](Rule30Open/Columns/TenCells.lean) | `ten_absorption`, `ten_0001`, `ten_0011`, `ten_0111`, `tenRight_0001`, `tenRight_0011`, `tenRight_0111`, `smallTen_0001`, `smallTen_0011`, `smallTen_0111` | 1 | extends a kit result |
| [A right half white past its first six cells enters the ether-and-wall family, whatever lies beyond the gap](Rule30Open/Columns/WhiteGap.md) | [`Columns.WhiteGap`](Rule30Open/Columns/WhiteGap.lean) | `drv_cone`, `inFamily_of_check_cone`, `gap_absorption`, `gap_0001`, `gap_0011`, `gap_0111`, `gapRight_0001`, `gapRight_0011`, `gapRight_0111`, `high_0011`, `high_0111` | 1 | extends a kit result |

**Findings**

| Result | Status | Problems | Formalization |
|---|---|---|---|
| [Every right half of up to 20 cells enters the kit's ether-and-wall family](findings/columns/absorption-census.md) | computed | 1 | partial |
| [Every window can reach the period-four certificate, so a fair coin beyond it locks the right half](findings/columns/coin-lock.md) | computed | 1 | wanted |
| [The finite game excludes 197 of the 8,800 blocks up to period 16](findings/columns/game-blocks.md) | computed | 1 | partial |
| [No left half of up to 80 cells meets the kit's C3 for a period-four word](findings/columns/left-half-c3.md) | computed | 1 | wanted |
| [A width-16 window certifies the period-four lock from most starts](findings/columns/period-four-certificate.md) | computed | 1 | wanted |
| [The three words of period four lock the right half](findings/columns/period-four-locking.md) | conjecture | 1 | wanted |

**Negative results**

| Result | Kind | Problems |
|---|---|---|
| [Jen's theorem on farther columns does not strengthen the finite game](negative-results/columns/jen-farther-columns.md) | no signal | 1 |
| [Driven by 011, the right half does not settle next to the center](negative-results/columns/period-three-011.md) | no signal | 1 |
| [No row of up to 24 cells has a column that repeats from time 0](negative-results/columns/periodic-from-start.md) | no signal | 1 |
| [A search for slow right halves finds no counterexample and misses the slowest halves](negative-results/columns/slow-half-search.md) | no signal | 1 |

## Period two

The first open period of Prize Problem 1, reduced to a question about one integer map.

**Proved in Lean**

| Result | Module | Headline theorems | Problems | Kit |
|---|---|---|---|---|
| [The alternating domains time the period-two condition](Rule30Open/PeriodTwo/Domains.md) | [`PeriodTwo.Domains`](Rule30Open/PeriodTwo/Domains.lean) | `held_domains_odd`, `held_countdown`, `held_disagree`, `held_agree_stepB` | 1 | independent proof of a kit result |
| [Period two reduces to an integer map](Rule30Open/PeriodTwo/HeldColumn.md) | [`PeriodTwo.HeldColumn`](Rule30Open/PeriodTwo/HeldColumn.lean) | `period_two_held`, `period_two_integer`, `center_period_two_integer`, `heldNat_testBit` | 1 | independent proof of a kit result |

**Findings**

| Result | Status | Problems | Formalization |
|---|---|---|---|
| [No row with its leftmost 1 within 120 cells has an alternating center](findings/period-two/alternating-within-120.md) | computed | 1 | wanted |
| [Every integer below 2^52 fails the period-two condition, near step 2M](findings/period-two/left-half-alone.md) | computed | 1 | partial |
| [Beside an alternating center the right half nearly locks, and slips](findings/period-two/right-channel.md) | computed | 1 | not applicable |
| [Against a white right half, no left half of fewer than a million cells keeps the center alternating](findings/period-two/white-right-half.md) | computed | 1 | wanted |

**Negative results**

| Result | Kind | Problems |
|---|---|---|
| [The ether-and-wall family does not catch the right half beside an alternating center](negative-results/period-two/absorption-route.md) | dead end | 1 |
| [The left half is not a patchwork of ether domains](negative-results/period-two/ether-patchwork.md) | refuted | 1 |
| [No finite certificate settles period two](negative-results/period-two/no-finite-certificate.md) | dead end | 1 |

## Diagonals

The periodic diagonals of the regular left side, and where their periods grow.

**Proved in Lean**

| Result | Module | Headline theorems | Problems | Kit |
|---|---|---|---|---|
| [Left diagonals remember only behind a white diagonal](Rule30Open/Diagonals/LeftMemory.md) | [`Diagonals.LeftMemory`](Rule30Open/Diagonals/LeftMemory.lean) | `D_reset`, `D_periodic_of_black`, `D_period_dichotomy`, `D_period_doubles`, `D_two_white`, `D_three_flips` | 1 | extends a kit result |

**Findings**

| Result | Status | Problems | Formalization |
|---|---|---|---|
| [Where the left diagonals turn white, to depth 100,000](findings/diagonals/left-records.md) | computed | 1 | partial |

## Frames and the seed's past

Rule 30 as a bijection of the 2-adic integers, the center column as a trace, and the rows that lead to the seed.

**Findings**

| Result | Status | Problems | Formalization |
|---|---|---|---|
| [Only the stripe and the ether backgrounds give a periodic column](findings/frames/periodic-backgrounds.md) | computed | 1 | wanted |
| [The single cell has a unique past, and every row of it is periodic](findings/frames/seed-past.md) | proved on paper | 1 | wanted |
| [The center column is the image of 1 under a 2-adic isometry](findings/frames/two-adic-trace.md) | proved on paper | 1 | proved in the kit |

**Negative results**

| Result | Kind | Problems |
|---|---|---|
| [A periodic column does not force a periodic row](negative-results/frames/periodic-column-preperiodic-row.md) | refuted | 1 |

## Sibling rules

Results for Rules 210 and 150 that show which features of Rule 30 a proof has to use.

**Proved in Lean**

| Result | Module | Headline theorems | Problems | Kit |
|---|---|---|---|---|
| [The linear analog of period two is true](Rule30Open/Analogs/Rule150Descent.md) | [`Analogs.Rule150Descent`](Rule30Open/Analogs/Rule150Descent.lean) | `held150_even_steps`, `held150_odd_steps`, `descent150` | 1 | not in the kit |
| [Rule 210 keeps the period-two condition](Rule30Open/Analogs/Rule210.md) | [`Analogs.Rule210`](Rule30Open/Analogs/Rule210.lean) | `rule210_finite_half`, `orbit210_checkerboard` | 1 | not in the kit |

**Negative results**

| Result | Kind | Problems |
|---|---|---|
| [Kopra's width-one argument does not transfer to Rule 30](negative-results/analogs/fractional-multiplication.md) | barrier | 1 |

## Dynamics of the two halves

How information crosses the center column, and reformulations of Problem 1 that did not close.

**Findings**

| Result | Status | Problems | Formalization |
|---|---|---|---|
| [Information reaches the center from the left at speed 1, from the right at about 0.4](findings/dynamics/one-way-valve.md) | computed | 1, 2 | partial |

**Negative results**

| Result | Kind | Problems |
|---|---|---|
| [Bounding the left half by the right channel needs Problem 1 itself](negative-results/dynamics/left-half-complexity.md) | dead end | 1 |
| [Reformulations of Problem 1 that did not close](negative-results/dynamics/reformulations.md) | dead end | 1 |
| [Driven halves never synchronize](negative-results/dynamics/synchronization.md) | no signal | 1 |

## Hidden structure

Exact searches for invariants, coarse-grainings, automata and algebraic relations in the center column.

**Findings**

| Result | Status | Problems | Formalization |
|---|---|---|---|
| [The center cell has degree exactly 2t - 1 over GF(2)](findings/structure/center-degree.md) | proved on paper | 3 | proved in the kit |
| [The center column as a sum over adjacent black pairs](findings/structure/duhamel.md) | proved on paper | 1, 2, 3 | proved in the kit |

**Negative results**

| Result | Kind | Problems |
|---|---|---|
| [Rule 30 has no coarse-graining with blocks of up to 8 cells](negative-results/structure/coarse-graining.md) | no signal | 1, 3 |
| [Rule 30 has no additive conservation law](negative-results/structure/conservation-laws.md) | no signal | 1, 2 |
| [Deforming the rule to Rule 150 gives a polynomial of exponential degree](negative-results/structure/deformation-interpolation.md) | dead end | 3 |
| [No linear relation among subsequences of the center column](negative-results/structure/linear-relations.md) | no signal | 1, 3 |
| [The center cell is a random-looking polynomial](negative-results/structure/polynomial-structure.md) | no signal | 3 |

## Random rows

What holds for a random initial row, and why it does not reach the single cell.

**Proved in Lean**

| Result | Module | Headline theorems | Problems | Kit |
|---|---|---|---|---|
| [A random left window gives a fair center window, for every row](Rule30Open/RandomRows/LeftWindow.md) | [`RandomRows.LeftWindow`](Rule30Open/RandomRows/LeftWindow.lean) | `cone_left_xor`, `count_centerWindow`, `centerWindow_unique`, `count_adapted`, `count_periodic`, `seed_window` | 1, 2 | extends a kit result |

**Negative results**

| Result | Kind | Problems |
|---|---|---|
| [Randomness proves Problems 1 and 2 for almost every row and stops at the single cell](negative-results/random-rows/almost-every-row.md) | barrier | 1, 2, 3 |

## Statistics

Tests of the center column against randomness.

**Negative results**

| Result | Kind | Problems |
|---|---|---|
| [No compressor or Markov model beats one bit per cell](negative-results/statistics/compression.md) | no signal | 3 |
| [The center column passes every randomness test tried](negative-results/statistics/randomness-tests.md) | no signal | 2, 3 |

## Learned models

Whether trained predictors find a shortcut for the center column.

**Negative results**

| Result | Kind | Problems |
|---|---|---|
| [No model maps the digits of t to cell t](negative-results/learned-models/digits-to-cell.md) | no signal | 3 |
| [Transformers do not predict the next cell](negative-results/learned-models/next-cell-transformers.md) | no signal | 3 |

## Complexity

Prize Problem 3, and what an answer either way would imply.

**Findings**

| Result | Status | Problems | Formalization |
|---|---|---|---|
| [Problems 1 and 3 follow from space lower bounds for the center column, and space √n log n suffices](findings/complexity/space-ladder.md) | proved on paper | 3, 1 | partial |

**Negative results**

| Result | Kind | Problems |
|---|---|---|
| [No automaton with fewer than 131,070 states computes the column from the digits of t](negative-results/complexity/automaton-lower-bounds.md) | no signal | 3 |
| [The Unique Games Conjecture and the Exponential Time Hypothesis do not decide Problem 3](negative-results/complexity/hardness-hypotheses.md) | barrier | 3, 1, 2 |
| [The linear complexity is n/2, the most a sequence can have](negative-results/complexity/linear-complexity.md) | no signal | 1, 3 |
| [Probabilistic checking verifies the center cell cheaply, as it does every computation, and does not compute it](negative-results/complexity/probabilistic-checking.md) | barrier | 3, 1, 2 |
| [Problem 3 asks for a lower bound beyond current complexity theory](negative-results/complexity/problem-three-barrier.md) | barrier | 3, 1 |
