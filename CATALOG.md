# Catalog

Every result in this repository, by category. `python scripts/catalog.py write` generates this page from the
front matter of the entries; edit the entries, not this page.

163 Lean modules with 719 headline theorems, 50 findings (proved on paper,
computed or conjectured) and 54 negative results. Prize problem 1 asks whether the center column
is eventually periodic, 2 whether its density of black cells tends to 1/2, and 3 whether computing its cell `n`
takes effort of order `n`.

| Category | Lean modules | Findings | Negative results |
|---|---:|---:|---:|
| [Foundations](#foundations) | 3 | 0 | 0 |
| [Seeds](#seeds) | 1 | 1 | 0 |
| [Columns](#columns) | 133 | 26 | 15 |
| [Period two](#period-two) | 11 | 10 | 7 |
| [Diagonals](#diagonals) | 6 | 4 | 5 |
| [Frames and the seed's past](#frames-and-the-seeds-past) | 2 | 3 | 1 |
| [Sibling rules](#sibling-rules) | 2 | 0 | 1 |
| [Dynamics of the two halves](#dynamics-of-the-two-halves) | 0 | 1 | 3 |
| [Hidden structure](#hidden-structure) | 0 | 2 | 7 |
| [Random rows](#random-rows) | 1 | 0 | 1 |
| [Statistics](#statistics) | 0 | 0 | 4 |
| [Learned models](#learned-models) | 0 | 0 | 2 |
| [Complexity](#complexity) | 4 | 3 | 8 |

## Open work

From the findings' front matter. Before starting in a category, read its negative results: each says where an
approach stopped.

**Conjectures to prove or refute**

- [The three words of period four lock the right half](findings/columns/period-four-locking.md): problem 1
- [Whatever the center column, the left half it drives allows a black run from time t of at most 0.13t to 0.18t and a white run of at most 0.15t to 0.28t for t from 75 to 175, far below the kit's slopes 3/5 and 1](findings/diagonals/driven-left-runs.md): problem 2
- [Over every row white left of a black cell, the left diagonal j settles by time ceil(3j/2) + 5 for j up to 76, exactly; from depth 9 to 76 the worst row is the single cell delayed by 6 to 8 steps, and the bound is conjectured for every j](findings/diagonals/seed-uniform-onsets.md): problem 2
- [A linear settling time of the left diagonals with periods o(j) would cut the slope of center-column runs to 3/13 (black) and 1/3 (white) at settling time 3j/2; depths 8 to 7,999 repeat with period 16 from time 3j/2 to time 12,583](findings/diagonals/settled-runs.md): problem 2

**Findings that want a Lean proof**

- [Beside 0001, column 1 moves in blocks of four along a graph of 13 edges, and a repeated block forces the ether](findings/columns/column-one-blocks.md): problem 1
- [Windows of 14 cells followed through the column's whole history exclude every tail of up to six cells but 10101 after 22 white cells, and 1,672 blocks of period at most 22](findings/columns/limit-windows.md): problem 1
- [Locked windows of 20 or 22 cells give traps that pass both tests to 14 blocks whose other traps all fail](findings/columns/own-locks.md): problem 1
- [A random right half driven by a period-four word, the exact law of its row and a zero-one reduction of entry](findings/columns/random-halves.md): problem 1
- [Only the stripe and the ether backgrounds give a periodic column](findings/frames/periodic-backgrounds.md): problem 1
- [No row with its leftmost 1 within 120 cells has an alternating center](findings/period-two/alternating-within-120.md): problem 1
- [Rows of radius up to 26 keep an alternating center from time 0 for at most 36 steps, with no law like the constant center's radius plus 2](findings/period-two/condrey-carryover.md): problem 1

**Findings proved in Lean in part**

- [Every right half of up to 20 cells enters the kit's ether-and-wall family](findings/columns/absorption-census.md): problem 1
- [A second infinite right half that never enters the kit's family for 0001, a background of 80 cells](findings/columns/background-halves.md): problem 1
- [The game with cyclic classes closes ten blocks of period 13 to 16, eight of period 17 and fifteen of period 18 that nothing else excludes](findings/columns/class-blocks.md): problem 1
- [The game with cyclic classes at 16 cells excludes 000000001011, a block of period 12 nothing else excludes](findings/columns/class-game.md): problem 1
- [Every window can reach the period-four certificate, so a fair coin beyond it locks the right half](findings/columns/coin-lock.md): problem 1
- [Against a right half of at most 11 to 14 cells, no left half of fewer than 1,000 cells keeps the center on a block of period 2, 3, 5, 6, 7 or 9](findings/columns/finite-onset-census.md): problem 1
- [The finite game excludes 261 of the 22,242 blocks of period 17 and 18](findings/columns/game-blocks-18.md): problem 1
- [The finite game excludes 508 of the 79,971 blocks of period 19 and 20](findings/columns/game-blocks-20.md): problem 1
- [The finite game excludes 434 of the 99,858 blocks of period 21](findings/columns/game-blocks-21.md): problem 1
- [The finite game excludes 197 of the 8,800 blocks up to period 16](findings/columns/game-blocks.md): problem 1
- [No left half of up to 80 cells meets the kit's C3 for a period-four word](findings/columns/left-half-c3.md): problem 1
- [No small left half meets the left-half statement of any block of period 3, 5, 6, 7 or 9](findings/columns/left-half-every-block.md): problem 1
- [Locks carried leftward from a few seeds give every locked window of 13 cells up to period 12, both of the kit's traps, and locked windows for a block of every period from 2 to 9](findings/columns/lock-chains.md): problem 1
- [Driven right halves settle into traps for 27 of the 99 blocks of period 10, 51 of the 186 of period 11 and 75 of the 335 of period 12](findings/columns/natural-traps.md): problem 1
- [A width-16 window certifies the period-four lock from most starts](findings/columns/period-four-certificate.md): problem 1
- [Beside a center that repeats a block, column 1 falls into a set of words of low entropy, from every state for 15 blocks of period 3 to 7](findings/columns/reading-constraints.md): problem 1
- [Every background of Rule 30 periodic in time, to period 14, and the traps at their edges](findings/columns/space-time-backgrounds.md): problem 1
- [For 72 blocks of period at most 12, every window of 13 cells can be steered into a lock](findings/columns/steerable-locks.md): problem 1
- [Every right half of up to ten cells enters the kit's trap for 001, some only after 10^5 steps](findings/columns/t001-census.md): problem 1
- [An alternating left half fixes the center cell whatever the right half is, so the left half of the cone is not incompressible](findings/complexity/cone-screening.md): problem 3
- [Problems 1 and 3 follow from space lower bounds for the center column, and space √(n log n) suffices](findings/complexity/space-ladder.md): problems 3, 1
- [The center column is computed in space √(n log n), and each simulation sets a threshold that a space lower bound must pass](findings/complexity/space-thresholds.md): problems 3, 1
- [Where the left diagonals turn white, to depth 100,000](findings/diagonals/left-records.md): problem 1
- [Information reaches the center from the left at speed 1, from the right at about 0.4](findings/dynamics/one-way-valve.md): problems 1, 2
- [The single cell has a unique past, and every row of it is periodic](findings/frames/seed-past.md): problem 1
- [Every defect of up to 20 cells on the ether settles, so (R) holds for those ether tails; a potential on top windows fails even along one real orbit](findings/period-two/ether-defect-census.md): problem 1
- [Beside an alternating center every right half of up to 20 cells enters a gap trap, the kit's ether family or a lock of period seven](findings/period-two/gate-census.md): problem 1
- [Every integer below 2^52 fails the period-two condition, near step 2M](findings/period-two/left-half-alone.md): problem 1
- [The period-two condition is a full 2-shift whose periodic points are domains, and its rational points are preperiodic as far as tried](findings/period-two/shift-model.md): problem 1
- [Beyond the stripes and the ether, every periodic tail of up to 12 cells falls onto a background where the tops of most defects run away, and no head of up to 16 cells on one of them is in K](findings/period-two/tail-census.md): problem 1
- [Against a white right half, no left half of fewer than a million cells keeps the center alternating](findings/period-two/white-right-half.md): problem 1
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
| [Entry into 48 traps that pass the tests of reach is false, refuted by a wider trap of the same block](Rule30Open/Columns/ApartTraps.md) | [`Columns.ApartTraps`](Rule30Open/Columns/ApartTraps.lean) | `natw00001111111_not_absorption_apart`, `pair_00001111111_excludes`, `fw1_106_not_absorption_apart`, `nat0000110111001_not_absorption_apart` | 1 | not in the kit |
| [The right half beside a 0001 column of the 80-cell background is in the ether-and-wall family at no time](Rule30Open/Columns/BackgroundHalves.md) | [`Columns.BackgroundHalves`](Rule30Open/Columns/BackgroundHalves.lean) | `background_half_not_inFamily`, `background_half_not_absorbed`, `background_half_8`, `drv_eq`, `prefix_short` | 1 | not in the kit |
| [The game decided in the kernel and the window-set check exclude 99 more blocks of period 17](Rule30Open/Columns/BitBlocks17.md) | [`Columns.BitBlocks17`](Rule30Open/Columns/BitBlocks17.lean) | `center_not_blocks17`, `not_eventually_blocks17`, `center_not_wallBlocks17` | 1 | not in the kit |
| [The game decided in the kernel and the window-set check exclude 122 more blocks of period 18](Rule30Open/Columns/BitBlocks18.md) | [`Columns.BitBlocks18`](Rule30Open/Columns/BitBlocks18.lean) | `center_not_blocks18`, `not_eventually_blocks18`, `center_not_wallBlocks18` | 1 | not in the kit |
| [The game decided in the kernel and the window-set check exclude 133 more blocks of period 19](Rule30Open/Columns/BitBlocks19.md) | [`Columns.BitBlocks19`](Rule30Open/Columns/BitBlocks19.lean) | `center_not_blocks19`, `not_eventually_blocks19`, `center_not_wallBlocks19` | 1 | not in the kit |
| [The game decided in the kernel excludes 57 more blocks of period 19 that need 7 to 12 cells](Rule30Open/Columns/BitBlocks19Wide.md) | [`Columns.BitBlocks19Wide`](Rule30Open/Columns/BitBlocks19Wide.lean) | `center_not_blocks19Wide`, `not_eventually_blocks19Wide` | 1 | not in the kit |
| [The game decided in the kernel and the window-set check exclude 160 more blocks of period 20](Rule30Open/Columns/BitBlocks20.md) | [`Columns.BitBlocks20`](Rule30Open/Columns/BitBlocks20.lean) | `center_not_blocks20`, `not_eventually_blocks20`, `center_not_wallBlocks20` | 1 | not in the kit |
| [The game decided in the kernel excludes 55 more blocks of period 20 that need 7 or 8 cells](Rule30Open/Columns/BitBlocks20Mid.md) | [`Columns.BitBlocks20Mid`](Rule30Open/Columns/BitBlocks20Mid.lean) | `center_not_blocks20Mid`, `not_eventually_blocks20Mid` | 1 | not in the kit |
| [The game decided in the kernel excludes 44 more blocks of period 20 that need 9 to 12 cells](Rule30Open/Columns/BitBlocks20Wide.md) | [`Columns.BitBlocks20Wide`](Rule30Open/Columns/BitBlocks20Wide.lean) | `center_not_blocks20Wide`, `not_eventually_blocks20Wide` | 1 | not in the kit |
| [The game decided in the kernel and the window-set check exclude 220 more blocks of period 21](Rule30Open/Columns/BitBlocks21.md) | [`Columns.BitBlocks21`](Rule30Open/Columns/BitBlocks21.lean) | `center_not_blocks21`, `not_eventually_blocks21`, `center_not_wallBlocks21` | 1 | not in the kit |
| [The game decided in the kernel excludes 97 more blocks of period 21 that need 7 to 8 cells](Rule30Open/Columns/BitBlocks21Mid.md) | [`Columns.BitBlocks21Mid`](Rule30Open/Columns/BitBlocks21Mid.lean) | `center_not_blocks21Mid`, `not_eventually_blocks21Mid` | 1 | not in the kit |
| [The game decided in the kernel excludes 62 more blocks of period 21 that need 9 to 12 cells](Rule30Open/Columns/BitBlocks21Wide.md) | [`Columns.BitBlocks21Wide`](Rule30Open/Columns/BitBlocks21Wide.lean) | `center_not_blocks21Wide`, `not_eventually_blocks21Wide` | 1 | not in the kit |
| [The finite game, decided in the kernel without a certificate, excludes seven blocks of period 14 to 16 that need 12 to 14 cells](Rule30Open/Columns/BitGame.md) | [`Columns.BitGame`](Rule30Open/Columns/BitGame.lean) | `bitGame_column`, `center_not_bitGame`, `bitGame_not_eventuallyWord`, `center_not_restBlocks`, `not_eventually_restBlocks` | 1 | not in the kit |
| [The game decided phase by phase in the kernel excludes the 14 blocks of period 17 and 18 that need 13 or 14 cells](Rule30Open/Columns/BitPhases.md) | [`Columns.BitPhases`](Rule30Open/Columns/BitPhases.lean) | `phases_column`, `center_not_phases`, `phases_not_eventuallyWord`, `center_not_blocksPhases18`, `not_eventually_blocksPhases18` | 1 | not in the kit |
| [The game decided phase by phase in the kernel excludes the 11 blocks of period 19 that need 13 or 14 cells](Rule30Open/Columns/BitPhases19.md) | [`Columns.BitPhases19`](Rule30Open/Columns/BitPhases19.lean) | `center_not_blocksPhases19`, `not_eventually_blocksPhases19` | 1 | not in the kit |
| [The game decided phase by phase in the kernel excludes the 15 blocks of period 20 that need 13 or 14 cells](Rule30Open/Columns/BitPhases20.md) | [`Columns.BitPhases20`](Rule30Open/Columns/BitPhases20.lean) | `center_not_blocksPhases20`, `not_eventually_blocksPhases20` | 1 | not in the kit |
| [The game decided phase by phase in the kernel excludes the 35 blocks of period 21 that need 13 or 14 cells](Rule30Open/Columns/BitPhases21.md) | [`Columns.BitPhases21`](Rule30Open/Columns/BitPhases21.lean) | `center_not_blocksPhases21`, `not_eventually_blocksPhases21` | 1 | not in the kit |
| [Traps for 124 more blocks of period 13, from every locked window of 16 cells carried leftward](Rule30Open/Columns/CensusTraps13.md) | [`Columns.CensusTraps13`](Rule30Open/Columns/CensusTraps13.lean) | `censusTraps13_check`, `censusTraps13_blocks`, `census13_absorption_excludes` | 1 | not in the kit |
| [Traps for 232 more blocks of period 14, from every locked window of 16 cells carried leftward](Rule30Open/Columns/CensusTraps14.md) | [`Columns.CensusTraps14`](Rule30Open/Columns/CensusTraps14.lean) | `censusTraps14_check`, `censusTraps14_blocks`, `census14_absorption_excludes` | 1 | not in the kit |
| [Traps for 569 blocks of period 15, from every locked window of 16 cells carried leftward](Rule30Open/Columns/CensusTraps15.md) | [`Columns.CensusTraps15`](Rule30Open/Columns/CensusTraps15.lean) | `censusTraps15_check`, `censusTraps15_blocks`, `census15_absorption_excludes` | 1 | not in the kit |
| [Traps for 22 more blocks of periods 13 and 14, from locked windows of 16 cells, checked in parts](Rule30Open/Columns/CensusTrapsLarge.md) | [`Columns.CensusTrapsLarge`](Rule30Open/Columns/CensusTrapsLarge.lean) | `censusTrapsLarge_check`, `censusTrapsLarge_blocks`, `censusLarge_absorption_excludes` | 1 | not in the kit |
| [Traps for 24 more blocks of period 15, from locked windows of 16 cells, checked in parts](Rule30Open/Columns/CensusTrapsLarge15.md) | [`Columns.CensusTrapsLarge15`](Rule30Open/Columns/CensusTrapsLarge15.lean) | `censusTrapsLarge15_check`, `censusTrapsLarge15_blocks`, `censusLarge15_absorption_excludes` | 1 | not in the kit |
| [The game with cyclic classes excludes four blocks of period 15 and 16 that nothing else excludes](Rule30Open/Columns/ClassBlocks.md) | [`Columns.ClassBlocks`](Rule30Open/Columns/ClassBlocks.lean) | `column_not_000000001101001`, `center_not_000000001101001`, `not_eventually_000000001101001`, `column_not_0000000001101001`, `center_not_0000000001101001`, `not_eventually_0000000001101001`, `column_not_0011110011111111`, `center_not_0011110011111111`, `not_eventually_0011110011111111`, `column_not_0000000011011001`, `center_not_0000000011011001`, `not_eventually_0000000011011001` | 1 | not in the kit |
| [The game with cyclic classes excludes two blocks of period 13 that nothing else excludes](Rule30Open/Columns/ClassBlocks13.md) | [`Columns.ClassBlocks13`](Rule30Open/Columns/ClassBlocks13.lean) | `column_not_0000001011011`, `center_not_0000001011011`, `not_eventually_0000001011011`, `column_not_0001011111011`, `center_not_0001011111011`, `not_eventually_0001011111011` | 1 | not in the kit |
| [The game with cyclic classes excludes 00100101111111, which nothing else excludes](Rule30Open/Columns/ClassBlocks14.md) | [`Columns.ClassBlocks14`](Rule30Open/Columns/ClassBlocks14.lean) | `column_not_00100101111111`, `center_not_00100101111111`, `not_eventually_00100101111111` | 1 | not in the kit |
| [The game with cyclic classes excludes two blocks of period 16 that nothing else excludes](Rule30Open/Columns/ClassBlocks16.md) | [`Columns.ClassBlocks16`](Rule30Open/Columns/ClassBlocks16.lean) | `column_not_0000001101111011`, `center_not_0000001101111011`, `not_eventually_0000001101111011`, `column_not_0110110111111111`, `center_not_0110110111111111`, `not_eventually_0110110111111111` | 1 | not in the kit |
| [The game with cyclic classes excludes 0001101111111001, which nothing else excludes](Rule30Open/Columns/ClassBlocks16Wide.md) | [`Columns.ClassBlocks16Wide`](Rule30Open/Columns/ClassBlocks16Wide.lean) | `column_not_0001101111111001`, `center_not_0001101111111001`, `not_eventually_0001101111111001` | 1 | not in the kit |
| [The game with cyclic classes excludes 00000000011111001, 00011011111111001 and 00000000010010001, of period 17, which nothing else excludes](Rule30Open/Columns/ClassBlocks17.md) | [`Columns.ClassBlocks17`](Rule30Open/Columns/ClassBlocks17.lean) | `column_not_00000000011111001`, `center_not_00000000011111001`, `not_eventually_00000000011111001`, `column_not_00011011111111001`, `center_not_00011011111111001`, `not_eventually_00011011111111001`, `column_not_00000000010010001`, `center_not_00000000010010001`, `not_eventually_00000000010010001` | 1 | not in the kit |
| [The game with cyclic classes at 17 cells excludes 01010111111111111, which nothing else excludes](Rule30Open/Columns/ClassBlocks17Cells.md) | [`Columns.ClassBlocks17Cells`](Rule30Open/Columns/ClassBlocks17Cells.lean) | `column_not_01010111111111111`, `center_not_01010111111111111`, `not_eventually_01010111111111111` | 1 | not in the kit |
| [The game with cyclic classes excludes 00000011011111011, of period 17, which nothing else excludes](Rule30Open/Columns/ClassBlocks17Mid.md) | [`Columns.ClassBlocks17Mid`](Rule30Open/Columns/ClassBlocks17Mid.lean) | `column_not_00000011011111011`, `center_not_00000011011111011`, `not_eventually_00000011011111011` | 1 | not in the kit |
| [The game with cyclic classes at 17 cells excludes 00011111111110101 and 01111011111111111, which nothing else excludes](Rule30Open/Columns/ClassBlocks17Split.md) | [`Columns.ClassBlocks17Split`](Rule30Open/Columns/ClassBlocks17Split.lean) | `column_not_00011111111110101`, `center_not_00011111111110101`, `not_eventually_00011111111110101`, `column_not_01111011111111111`, `center_not_01111011111111111`, `not_eventually_01111011111111111` | 1 | not in the kit |
| [The heights of the certificate of 00011111111110101 at widths 1 to 15, checked in Lean](Rule30Open/Columns/ClassBlocks17SplitA1.md) | [`Columns.ClassBlocks17SplitA1`](Rule30Open/Columns/ClassBlocks17SplitA1.lean) | `cls00011111111110101W15_levels` | 1 | not in the kit |
| [The heights of the certificate of 00011111111110101 at widths 16 and 17, checked in Lean](Rule30Open/Columns/ClassBlocks17SplitA2.md) | [`Columns.ClassBlocks17SplitA2`](Rule30Open/Columns/ClassBlocks17SplitA2.lean) | `cls00011111111110101W17_levels` | 1 | not in the kit |
| [The classes of the certificate of 00011111111110101 at 17 cells, checked in Lean](Rule30Open/Columns/ClassBlocks17SplitA3.md) | [`Columns.ClassBlocks17SplitA3`](Rule30Open/Columns/ClassBlocks17SplitA3.lean) | `cls00011111111110101_f` | 1 | not in the kit |
| [The heights of the certificate of 01111011111111111 at widths 1 to 15, checked in Lean](Rule30Open/Columns/ClassBlocks17SplitB1.md) | [`Columns.ClassBlocks17SplitB1`](Rule30Open/Columns/ClassBlocks17SplitB1.lean) | `cls01111011111111111W15_levels` | 1 | not in the kit |
| [The heights of the certificate of 01111011111111111 at widths 16 and 17, checked in Lean](Rule30Open/Columns/ClassBlocks17SplitB2.md) | [`Columns.ClassBlocks17SplitB2`](Rule30Open/Columns/ClassBlocks17SplitB2.lean) | `cls01111011111111111W17_levels` | 1 | not in the kit |
| [The classes of the certificate of 01111011111111111 at 17 cells, checked in Lean](Rule30Open/Columns/ClassBlocks17SplitB3.md) | [`Columns.ClassBlocks17SplitB3`](Rule30Open/Columns/ClassBlocks17SplitB3.lean) | `cls01111011111111111_f` | 1 | not in the kit |
| [The game with cyclic classes excludes 00000000001000001, of period 17, which nothing else excludes](Rule30Open/Columns/ClassBlocks17Wide.md) | [`Columns.ClassBlocks17Wide`](Rule30Open/Columns/ClassBlocks17Wide.lean) | `column_not_00000000001000001`, `center_not_00000000001000001`, `not_eventually_00000000001000001` | 1 | not in the kit |
| [The game with cyclic classes excludes 001111111111011101, 001001101111111111 and 000000000100000001, of period 18, which nothing else excludes](Rule30Open/Columns/ClassBlocks18.md) | [`Columns.ClassBlocks18`](Rule30Open/Columns/ClassBlocks18.lean) | `column_not_001111111111011101`, `center_not_001111111111011101`, `not_eventually_001111111111011101`, `column_not_001001101111111111`, `center_not_001001101111111111`, `not_eventually_001001101111111111`, `column_not_000000000100000001`, `center_not_000000000100000001`, `not_eventually_000000000100000001` | 1 | not in the kit |
| [The game with cyclic classes excludes 000000000010010011, of period 18, which nothing else excludes](Rule30Open/Columns/ClassBlocks18Mid.md) | [`Columns.ClassBlocks18Mid`](Rule30Open/Columns/ClassBlocks18Mid.lean) | `column_not_000000000010010011`, `center_not_000000000010010011`, `not_eventually_000000000010010011` | 1 | not in the kit |
| [The game with cyclic classes excludes ten more blocks of period 18, which nothing else excludes](Rule30Open/Columns/ClassBlocks18Split.md) | [`Columns.ClassBlocks18Split`](Rule30Open/Columns/ClassBlocks18Split.lean) | `column_not_001010100111111111`, `center_not_001010100111111111`, `not_eventually_001010100111111111`, `column_not_001111001111111111`, `center_not_001111001111111111`, `not_eventually_001111001111111111`, `column_not_011110111111111111`, `center_not_011110111111111111`, `not_eventually_011110111111111111`, `column_not_000000000011000101`, `center_not_000000000011000101`, `not_eventually_000000000011000101`, `column_not_000011111111111101`, `center_not_000011111111111101`, `not_eventually_000011111111111101`, `column_not_000000000011111001`, `center_not_000000000011111001`, `not_eventually_000000000011111001`, `column_not_000000000001000001`, `center_not_000000000001000001`, `not_eventually_000000000001000001`, `column_not_000010111111111001`, `center_not_000010111111111001`, `not_eventually_000010111111111001`, `column_not_001011111111110111`, `center_not_001011111111110111`, `not_eventually_001011111111110111`, `column_not_000000011011111001`, `center_not_000000011011111001`, `not_eventually_000000011011111001` | 1 | not in the kit |
| [The heights of the certificate of 001010100111111111 at widths 1 to 14, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitA1.md) | [`Columns.ClassBlocks18SplitA1`](Rule30Open/Columns/ClassBlocks18SplitA1.lean) | `cls001010100111111111W14_levels` | 1 | not in the kit |
| [The classes of the certificate of 001010100111111111 at 14 cells, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitA2.md) | [`Columns.ClassBlocks18SplitA2`](Rule30Open/Columns/ClassBlocks18SplitA2.lean) | `cls001010100111111111_f` | 1 | not in the kit |
| [The heights of the certificate of 001111001111111111 at widths 1 to 15, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitB1.md) | [`Columns.ClassBlocks18SplitB1`](Rule30Open/Columns/ClassBlocks18SplitB1.lean) | `cls001111001111111111W15_levels` | 1 | not in the kit |
| [The classes of the certificate of 001111001111111111 at 15 cells, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitB2.md) | [`Columns.ClassBlocks18SplitB2`](Rule30Open/Columns/ClassBlocks18SplitB2.lean) | `cls001111001111111111_f` | 1 | not in the kit |
| [The heights of the certificate of 011110111111111111 at widths 1 to 15, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitC1.md) | [`Columns.ClassBlocks18SplitC1`](Rule30Open/Columns/ClassBlocks18SplitC1.lean) | `cls011110111111111111W15_levels` | 1 | not in the kit |
| [The classes of the certificate of 011110111111111111 at 15 cells, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitC2.md) | [`Columns.ClassBlocks18SplitC2`](Rule30Open/Columns/ClassBlocks18SplitC2.lean) | `cls011110111111111111_f` | 1 | not in the kit |
| [The heights of the certificate of 000000000011000101 at widths 1 to 15, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitD1.md) | [`Columns.ClassBlocks18SplitD1`](Rule30Open/Columns/ClassBlocks18SplitD1.lean) | `cls000000000011000101W15_levels` | 1 | not in the kit |
| [The classes of the certificate of 000000000011000101 at 15 cells, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitD2.md) | [`Columns.ClassBlocks18SplitD2`](Rule30Open/Columns/ClassBlocks18SplitD2.lean) | `cls000000000011000101_f` | 1 | not in the kit |
| [The heights of the certificate of 000011111111111101 at widths 1 to 15, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitE1.md) | [`Columns.ClassBlocks18SplitE1`](Rule30Open/Columns/ClassBlocks18SplitE1.lean) | `cls000011111111111101W15_levels` | 1 | not in the kit |
| [The classes of the certificate of 000011111111111101 at 15 cells, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitE2.md) | [`Columns.ClassBlocks18SplitE2`](Rule30Open/Columns/ClassBlocks18SplitE2.lean) | `cls000011111111111101_f` | 1 | not in the kit |
| [The heights of the certificate of 000000000011111001 at widths 1 to 15, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitF1.md) | [`Columns.ClassBlocks18SplitF1`](Rule30Open/Columns/ClassBlocks18SplitF1.lean) | `cls000000000011111001W15_levels` | 1 | not in the kit |
| [The heights of the certificate of 000000000011111001 at width 16, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitF2.md) | [`Columns.ClassBlocks18SplitF2`](Rule30Open/Columns/ClassBlocks18SplitF2.lean) | `cls000000000011111001W16_levels` | 1 | not in the kit |
| [The classes of the certificate of 000000000011111001 at 16 cells, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitF3.md) | [`Columns.ClassBlocks18SplitF3`](Rule30Open/Columns/ClassBlocks18SplitF3.lean) | `cls000000000011111001_f` | 1 | not in the kit |
| [The heights of the certificate of 000000000001000001 at widths 1 to 15, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitG1.md) | [`Columns.ClassBlocks18SplitG1`](Rule30Open/Columns/ClassBlocks18SplitG1.lean) | `cls000000000001000001W15_levels` | 1 | not in the kit |
| [The heights of the certificate of 000000000001000001 at width 16, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitG2.md) | [`Columns.ClassBlocks18SplitG2`](Rule30Open/Columns/ClassBlocks18SplitG2.lean) | `cls000000000001000001W16_levels` | 1 | not in the kit |
| [The classes of the certificate of 000000000001000001 at 16 cells, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitG3.md) | [`Columns.ClassBlocks18SplitG3`](Rule30Open/Columns/ClassBlocks18SplitG3.lean) | `cls000000000001000001_f` | 1 | not in the kit |
| [The heights of the certificate of 000010111111111001 at widths 1 to 15, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitH1.md) | [`Columns.ClassBlocks18SplitH1`](Rule30Open/Columns/ClassBlocks18SplitH1.lean) | `cls000010111111111001W15_levels` | 1 | not in the kit |
| [The heights of the certificate of 000010111111111001 at width 16, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitH2.md) | [`Columns.ClassBlocks18SplitH2`](Rule30Open/Columns/ClassBlocks18SplitH2.lean) | `cls000010111111111001W16_levels` | 1 | not in the kit |
| [The classes of the certificate of 000010111111111001 at 16 cells, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitH3.md) | [`Columns.ClassBlocks18SplitH3`](Rule30Open/Columns/ClassBlocks18SplitH3.lean) | `cls000010111111111001_f` | 1 | not in the kit |
| [The heights of the certificate of 001011111111110111 at widths 1 to 15, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitI1.md) | [`Columns.ClassBlocks18SplitI1`](Rule30Open/Columns/ClassBlocks18SplitI1.lean) | `cls001011111111110111W15_levels` | 1 | not in the kit |
| [The heights of the certificate of 001011111111110111 at width 16, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitI2.md) | [`Columns.ClassBlocks18SplitI2`](Rule30Open/Columns/ClassBlocks18SplitI2.lean) | `cls001011111111110111W16_levels` | 1 | not in the kit |
| [The classes of the certificate of 001011111111110111 at 16 cells, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitI3.md) | [`Columns.ClassBlocks18SplitI3`](Rule30Open/Columns/ClassBlocks18SplitI3.lean) | `cls001011111111110111_f` | 1 | not in the kit |
| [The heights of the certificate of 000000011011111001 at widths 1 to 15, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitJ1.md) | [`Columns.ClassBlocks18SplitJ1`](Rule30Open/Columns/ClassBlocks18SplitJ1.lean) | `cls000000011011111001W15_levels` | 1 | not in the kit |
| [The heights of the certificate of 000000011011111001 at width 16, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitJ2.md) | [`Columns.ClassBlocks18SplitJ2`](Rule30Open/Columns/ClassBlocks18SplitJ2.lean) | `cls000000011011111001W16_levels` | 1 | not in the kit |
| [The classes of the certificate of 000000011011111001 at 16 cells, checked in Lean](Rule30Open/Columns/ClassBlocks18SplitJ3.md) | [`Columns.ClassBlocks18SplitJ3`](Rule30Open/Columns/ClassBlocks18SplitJ3.lean) | `cls000000011011111001_f` | 1 | not in the kit |
| [The game with cyclic classes excludes 000000000000111011, of period 18, which nothing else excludes](Rule30Open/Columns/ClassBlocks18Wide.md) | [`Columns.ClassBlocks18Wide`](Rule30Open/Columns/ClassBlocks18Wide.lean) | `column_not_000000000000111011`, `center_not_000000000000111011`, `not_eventually_000000000000111011` | 1 | not in the kit |
| [The game with cyclic classes, checked width by width, excludes 000000001011 in Lean](Rule30Open/Columns/ClassGame.md) | [`Columns.ClassGame`](Rule30Open/Columns/ClassGame.lean) | `class_column`, `center_not_class`, `class_not_eventuallyWord`, `column_not_000000001011`, `center_not_000000001011`, `not_eventually_000000001011` | 1 | not in the kit |
| [A certificate of the game with cyclic classes can be checked over several modules](Rule30Open/Columns/ClassSplit.md) | [`Columns.ClassSplit`](Rule30Open/Columns/ClassSplit.lean) | `ClassCert.tri_append`, `ClassCert.levelOk_append` | 1 | not in the kit |
| [A periodic column and any observable that closes the strip to its right](Rule30Open/Columns/ClosingObservable.md) | [`Columns.ClosingObservable`](Rule30Open/Columns/ClosingObservable.lean) | `closing_observable`, `affine_observable`, `center_xor`, `center_masked_two`, `center_parity` | 1 | extends a kit result |
| [Counts of black cells move left by at most a factor of three](Rule30Open/Columns/ColumnTransfer.md) | [`Columns.ColumnTransfer`](Rule30Open/Columns/ColumnTransfer.lean) | `transfer`, `transfer_white`, `iterate`, `transfer_right`, `transfer_right_white`, `iterate_right`, `center_lower` | 2 | not in the kit |
| [For 001 the left half only has to fail for free bits whose runs of 0s have length at least 2 and runs of 1s at least 3](Rule30Open/Columns/ConstrainedLeft001.md) | [`Columns.ConstrainedLeft001`](Rule30Open/Columns/ConstrainedLeft001.lean) | `not_eventually_001_of_C3r`, `center_not_eventually_001_of_C3r`, `c3r_of_c3s` | 1 | extends a kit result |
| [Traps for 57 of the 186 blocks of period 11, from walls of period eleven carried leftward](Rule30Open/Columns/ElevenTraps.md) | [`Columns.ElevenTraps`](Rule30Open/Columns/ElevenTraps.lean) | `elevenTraps_check`, `elevenTraps_blocks`, `eleven_absorption_excludes` | 1 | not in the kit |
| [Against a right half of at most six cells no center column repeats a word of period four](Rule30Open/Columns/EmptyRight.md) | [`Columns.EmptyRight`](Rule30Open/Columns/EmptyRight.lean) | `smallRight_0001`, `smallRight_0011`, `smallRight_0111`, `emptyRight_001`, `no_finite_of_family`, `no_finite_of_ptrap` | 1 | extends a kit result |
| [The word 0001 comes down to the period-two map, and the ether is its domain](Rule30Open/Columns/EtherDomain.md) | [`Columns.EtherDomain`](Rule30Open/Columns/EtherDomain.lean) | `center_period_four_0001_integer`, `period_four_0001_held`, `held_etherLeft`, `ether_fits`, `ether_countdown`, `domainB_repeats` | 1 | extends a kit result |
| [Every truncation of the aligned ether, followed by a short word, enters the ether-and-wall family](Rule30Open/Columns/EtherPrefix.md) | [`Columns.EtherPrefix`](Rule30Open/Columns/EtherPrefix.lean) | `shift7_drv`, `shift7_family`, `prefix_absorption`, `etherPrefix_0001`, `etherPrefix_0011`, `etherPrefix_0111`, `prefixRight_0001`, `prefixRight_0011`, `prefixRight_0111` | 1 | extends a kit result |
| [Every truncation of the aligned ether, followed by any word of up to six cells, enters the ether-and-wall family](Rule30Open/Columns/EtherPrefixSix.md) | [`Columns.EtherPrefixSix`](Rule30Open/Columns/EtherPrefixSix.lean) | `prefix_of_tails_len`, `etherPrefixSix_0001`, `etherPrefixSix_0011`, `etherPrefixSix_0111`, `prefixSixRight_0001`, `prefixSixRight_0011`, `prefixSixRight_0111` | 1 | extends a kit result |
| [Traps for 12 more blocks of period 12, from the wall of the background of 60 cells carried past 40 columns](Rule30Open/Columns/FarWalls.md) | [`Columns.FarWalls`](Rule30Open/Columns/FarWalls.lean) | `farWalls_check`, `farWalls_blocks`, `far_absorption_excludes` | 1 | not in the kit |
| [Traps for 86 blocks of period 15, from two walls wider than 16 cells carried leftward](Rule30Open/Columns/FifteenWalls.md) | [`Columns.FifteenWalls`](Rule30Open/Columns/FifteenWalls.lean) | `fifteenWalls_check`, `fifteenWalls_blocks`, `fifteen_absorption_excludes` | 1 | not in the kit |
| [A finite game rules out repeating blocks](Rule30Open/Columns/FiniteGame.md) | [`Columns.FiniteGame`](Rule30Open/Columns/FiniteGame.lean) | `game_column`, `center_not_01111111`, `center_not_00000011` | 1 | independent proof of a kit result |
| [A right half white past its first fourteen cells enters the ether-and-wall family, whatever lies beyond the gap](Rule30Open/Columns/FourteenCells.md) | [`Columns.FourteenCells`](Rule30Open/Columns/FourteenCells.lean) | `fourteen_absorption`, `fourteen_0001`, `fourteen_0011`, `fourteen_0111`, `fourteenRight_0001`, `fourteenRight_0011`, `fourteenRight_0111`, `smallFourteen_0001`, `smallFourteen_0011`, `smallFourteen_0111` | 1 | extends a kit result |
| [Traps for 101 of the 1,161 blocks of period 14, from a wall of period fourteen carried leftward](Rule30Open/Columns/FourteenTraps.md) | [`Columns.FourteenTraps`](Rule30Open/Columns/FourteenTraps.lean) | `fourteenTraps_check`, `fourteenTraps_blocks`, `fourteen_absorption_excludes` | 1 | not in the kit |
| [The finite game, checked in bit masks, excludes 32 more blocks of period at most 14](Rule30Open/Columns/GameBlocks.md) | [`Columns.GameBlocks`](Rule30Open/Columns/GameBlocks.lean) | `mask_column`, `center_not_gameBlocks`, `not_eventually_gameBlocks` | 1 | not in the kit |
| [The finite game, checked in bit masks, excludes 97 more blocks of period 15 and 16](Rule30Open/Columns/GameBlocksLong.md) | [`Columns.GameBlocksLong`](Rule30Open/Columns/GameBlocksLong.lean) | `center_not_gameBlocks16`, `not_eventually_gameBlocks16` | 1 | not in the kit |
| [The game at 15 or 16 cells excludes 00110011111111, 0000000000111011 and 0000101111111001, which nothing else excludes](Rule30Open/Columns/GameBlocksWide.md) | [`Columns.GameBlocksWide`](Rule30Open/Columns/GameBlocksWide.lean) | `column_not_00110011111111`, `center_not_00110011111111`, `not_eventually_00110011111111`, `column_not_0000000000111011`, `center_not_0000000000111011`, `not_eventually_0000000000111011`, `column_not_0000101111111001`, `center_not_0000101111111001`, `not_eventually_0000101111111001` | 1 | not in the kit |
| [A right half white on its first 1,317 cells enters the kit's trap for 001](Rule30Open/Columns/HighThree.md) | [`Columns.HighThree`](Rule30Open/Columns/HighThree.lean) | `highRight3_of_entry`, `highRight_001` | 1 | extends a kit result |
| [The kicked form of the left half](Rule30Open/Columns/KickedForm.md) | [`Columns.KickedForm`](Rule30Open/Columns/KickedForm.lean) | `left_kicked_zero`, `left_kicked_succ`, `left_kicked_check`, `period_two_golden` | 1 | extends a kit result |
| [No left half within depth 88 keeps the kit's left-half pattern for 0001](Rule30Open/Columns/LeftHalf0001.md) | [`Columns.LeftHalf0001`](Rule30Open/Columns/LeftHalf0001.lean) | `c3_0001_bounded`, `c3_0001_small`, `c3_0001_depth`, `c3_0001_of_checks` | 1 | extends a kit result |
| [No left half within depth 88 keeps the kit's left-half pattern for 0011 or 0111](Rule30Open/Columns/LeftHalfDriven.md) | [`Columns.LeftHalfDriven`](Rule30Open/Columns/LeftHalfDriven.lean) | `c3_0011_bounded`, `c3_0111_bounded`, `c3_0011_small`, `c3_0111_small`, `c3G_of_checks`, `history_eq_reconB` | 1 | extends a kit result |
| [Every eventual period comes down to one statement about the left half](Rule30Open/Columns/LeftLatch.md) | [`Columns.LeftLatch`](Rule30Open/Columns/LeftLatch.lean) | `column_not_eventually_of_leftLatch`, `not_eventually_of_leftLatch`, `kickOrbit_eq`, `leftLatch_one` | 1 | extends a kit result |
| [One sequence in one column forces a lock of the finite game, for a block of any period](Rule30Open/Columns/LockBlocks.md) | [`Columns.LockBlocks`](Rule30Open/Columns/LockBlocks.lean) | `lockBlock_column`, `center_lockBlock`, `center_lock_steered`, `not_eventually_steered` | 1 | not in the kit |
| [Once the center repeats one of 26 blocks of period 4 to 11, column 14 never reads that block's steering sequence](Rule30Open/Columns/LockBlocks11.md) | [`Columns.LockBlocks11`](Rule30Open/Columns/LockBlocks11.lean) | `steered11_check`, `center_lock_steered11`, `not_eventually_steered11` | 1 | not in the kit |
| [Once the center repeats one of 23 blocks of period 12, column 14 never reads that block's steering sequence](Rule30Open/Columns/LockBlocks12.md) | [`Columns.LockBlocks12`](Rule30Open/Columns/LockBlocks12.lean) | `steered12_check`, `center_lock_steered12`, `not_eventually_steered12` | 1 | not in the kit |
| [Once the center repeats one of 22 blocks, a column near it is never white for long](Rule30Open/Columns/LockWhite.md) | [`Columns.LockWhite`](Rule30Open/Columns/LockWhite.lean) | `center_white_run`, `whiteRuns_check`, `center_white_runs`, `not_eventually_white_runs` | 1 | not in the kit |
| [One word in a column beside the center forces the period-four lock, for each of the three words](Rule30Open/Columns/LockWord.md) | [`Columns.LockWord`](Rule30Open/Columns/LockWord.lean) | `lockWord_column`, `family_contra`, `lock_0001`, `lock_0011`, `lock_0111`, `center_lock_0001`, `center_lock_0011`, `center_lock_0111`, `center_not_0001_of_word`, `center_not_0011_of_word`, `center_not_0111_of_word` | 1 | not in the kit |
| [Runs of nine 1s rule out a periodic column](Rule30Open/Columns/LongRuns.md) | [`Columns.LongRuns`](Rule30Open/Columns/LongRuns.lean) | `wall_check`, `long_runs_column`, `center_long_runs` | 1 | independent proof of a kit result |
| [An eventual period of the center column needs T + P of at least 65,518](Rule30Open/Columns/LongWindow.md) | [`Columns.LongWindow`](Rule30Open/Columns/LongWindow.lean) | `center_eq_big`, `factor_new`, `transient_add_period_ge_65518` | 1 | extends a kit result |
| [Seven checked traps of periods 13 to 15 that some finitely supported right half never enters](Rule30Open/Columns/MissedTraps.md) | [`Columns.MissedTraps`](Rule30Open/Columns/MissedTraps.lean) | `not_absorption`, `not_absorption_wide`, `missedTraps_check`, `missedTraps_not_absorption` | 1 | not in the kit |
| [Traps for 34 more blocks of periods 10 to 12, the closed sets that driven right halves settle into](Rule30Open/Columns/NaturalTraps.md) | [`Columns.NaturalTraps`](Rule30Open/Columns/NaturalTraps.lean) | `naturalTraps_check`, `naturalTraps_blocks`, `natural_absorption_excludes` | 1 | not in the kit |
| [A trap of 61,857 states for the block 00010001011 of period 11, checked in parts](Rule30Open/Columns/NaturalTrapsLarge.md) | [`Columns.NaturalTrapsLarge`](Rule30Open/Columns/NaturalTrapsLarge.lean) | `allRange_cover`, `nat00010001011_check`, `not_eventually_00010001011_of_trap` | 1 | not in the kit |
| [Traps for 70 blocks of periods 13 and 14, the closed sets that driven right halves settle into](Rule30Open/Columns/NaturalTrapsLong.md) | [`Columns.NaturalTrapsLong`](Rule30Open/Columns/NaturalTrapsLong.lean) | `naturalTrapsLong_check`, `naturalTrapsLong_blocks`, `naturalLong_absorption_excludes` | 1 | not in the kit |
| [The natural traps of 12 more blocks of periods 13 and 14, of 3,295 to 18,132 states, checked in parts](Rule30Open/Columns/NaturalTrapsLongLarge.md) | [`Columns.NaturalTrapsLongLarge`](Rule30Open/Columns/NaturalTrapsLongLarge.lean) | `naturalTrapsLongLarge_check`, `naturalTrapsLongLarge_blocks`, `naturalLongLarge_absorption_excludes` | 1 | not in the kit |
| [Natural traps for 60 blocks of periods 10 to 14 whose wall traps fail the test of reach](Rule30Open/Columns/NaturalTrapsWalls.md) | [`Columns.NaturalTrapsWalls`](Rule30Open/Columns/NaturalTrapsWalls.lean) | `naturalTrapsWalls_check`, `naturalTrapsWalls_blocks`, `naturalWalls_absorption_excludes`, `natw00101101111_excludes`, `natw00101101111_0_not_absorption` | 1 | not in the kit |
| [Traps for 22 of the 56 blocks of period 9, from two walls of period nine that driven right halves enter](Rule30Open/Columns/NineTraps.md) | [`Columns.NineTraps`](Rule30Open/Columns/NineTraps.lean) | `nineTraps_check`, `nineTraps_blocks`, `nine_absorption_excludes`, `trap001010011_check`, `not_eventually_001010011_of_absorption` | 1 | not in the kit |
| [Right halves white on their first 91,129 to 201,172 cells enter the walls of period 9](Rule30Open/Columns/NineWhite.md) | [`Columns.NineWhite`](Rule30Open/Columns/NineWhite.lean) | `highRightW_of_entry`, `white_first_wall`, `white_first_wall_eight`, `white_second_wall`, `white_second_wall_zero` | 1 | not in the kit |
| [The period-four certificates are traps, and entry into one excludes its word](Rule30Open/Columns/PeriodFourCertificate.md) | [`Columns.PeriodFourCertificate`](Rule30Open/Columns/PeriodFourCertificate.lean) | `cert0001_check`, `cert0011_check`, `cert0111_check`, `not_eventually_0001_of_certificate`, `not_eventually_0011_of_certificate`, `not_eventually_0111_of_certificate` | 1 | not in the kit |
| [Refuting entry into a trap from the few windows that can reach it](Rule30Open/Columns/ReachRefuted.md) | [`Columns.ReachRefuted`](Rule30Open/Columns/ReachRefuted.lean) | `pre_move`, `not_absorption_back`, `not_absorption_fwd`, `tw0_40_not_absorption_back`, `fo0_46_not_absorption_back` | 1 | not in the kit |
| [Beside a center column repeating one of 15 blocks of period 5 to 7, column 1 at one white step avoids a list of words](Rule30Open/Columns/ReadingWords.md) | [`Columns.ReadingWords`](Rule30Open/Columns/ReadingWords.lean) | `readings_00011`, `readings_00011_evolve`, `readings_00101`, `readings_00101_evolve`, `readings_00111`, `readings_00111_evolve`, `readings_01011`, `readings_01011_evolve`, `readings_000001`, `readings_000001_evolve`, `readings_000011`, `readings_000011_evolve`, `readings_000111`, `readings_000111_evolve`, `readings_001101`, `readings_001101_evolve`, `readings_010111`, `readings_010111_evolve`, `readings_0000001`, `readings_0000001_evolve`, `readings_0000101`, `readings_0000101_evolve`, `readings_0001001`, `readings_0001001_evolve`, `readings_0001011`, `readings_0001011_evolve`, `readings_0011011`, `readings_0011011_evolve`, `readings_0110111`, `readings_0110111_evolve` | 1 | not in the kit |
| [Lean refutations of entry into 102 traps of the trap modules](Rule30Open/Columns/RefutedTraps.md) | [`Columns.RefutedTraps`](Rule30Open/Columns/RefutedTraps.lean) | `refutedTraps_not_absorption`, `nine15_not_absorption`, `tw1_4_not_absorption`, `cen0011111101111_not_absorption` | 1 | not in the kit |
| [The cells left of a column count down its runs of 1s](Rule30Open/Columns/RunCountdown.md) | [`Columns.RunCountdown`](Rule30Open/Columns/RunCountdown.lean) | `run_countdown`, `run_bound`, `no_ones_column`, `center_not_eventually_ones` | 1 | extends a kit result |
| [Under a center column repeating 00001, column 1 at the first white step has isolated 1s and no run of exactly two 0s](Rule30Open/Columns/Runs00001.md) | [`Columns.Runs00001`](Rule30Open/Columns/Runs00001.lean) | `runs_00001`, `runs_00001_evolve`, `no_11_time_00001`, `no_1001_time_00001` | 1 | not in the kit |
| [Entry into the only trap of period 6 is false](Rule30Open/Columns/SixRefuted.md) | [`Columns.SixRefuted`](Rule30Open/Columns/SixRefuted.lean) | `back_trap001011_check`, `trap001011_not_absorption_back` | 1 | not in the kit |
| [A right half with at most two black cells among its first cells enters the ether-and-wall family](Rule30Open/Columns/SparseRight.md) | [`Columns.SparseRight`](Rule30Open/Columns/SparseRight.lean) | `inFamily_of_fast`, `stateAt_eq`, `two_absorption`, `sparse_0001`, `sparse_0011`, `sparse_0111`, `oneCell_0011`, `oneCell_0111`, `sparseRight_0001`, `sparseRight_0011`, `sparseRight_0111` | 1 | extends a kit result |
| [A right half white past its first ten cells enters the ether-and-wall family, whatever lies beyond the gap](Rule30Open/Columns/TenCells.md) | [`Columns.TenCells`](Rule30Open/Columns/TenCells.lean) | `ten_absorption`, `ten_0001`, `ten_0011`, `ten_0111`, `tenRight_0001`, `tenRight_0011`, `tenRight_0111`, `smallTen_0001`, `smallTen_0011`, `smallTen_0111` | 1 | extends a kit result |
| [No finite configuration whose cells 9 to 3,058 are white has a center column that repeats 0000010001](Rule30Open/Columns/TenGap.md) | [`Columns.TenGap`](Rule30Open/Columns/TenGap.lean) | `prefixRightW_of_entry`, `gapRightW_of_entries`, `ten_gap`, `ten_white` | 1 | not in the kit |
| [Traps for 25 blocks of period 10, from one background of period ten whose edge driven right halves enter](Rule30Open/Columns/TenTraps.md) | [`Columns.TenTraps`](Rule30Open/Columns/TenTraps.lean) | `tenTraps_check`, `tenTraps_blocks`, `ten_absorption_excludes` | 1 | not in the kit |
| [Traps for 53 of the 630 blocks of period 13, from a wall of period thirteen carried leftward](Rule30Open/Columns/ThirteenTraps.md) | [`Columns.ThirteenTraps`](Rule30Open/Columns/ThirteenTraps.lean) | `thirteenTraps_check`, `thirteenTraps_blocks`, `thirteen_absorption_excludes` | 1 | not in the kit |
| [Under a center column repeating 001, column 1 at the second white step has 1-runs of length at least 2 and 0-runs of length at least 3](Rule30Open/Columns/ThreeRuns.md) | [`Columns.ThreeRuns`](Rule30Open/Columns/ThreeRuns.lean) | `three_runs`, `three_runs_evolve`, `no_010_time`, `no_101_time`, `no_1001_time` | 1 | not in the kit |
| [Four blocks of periods 13 and 14 reduced to entry into one of two traps](Rule30Open/Columns/TrapPairs.md) | [`Columns.TrapPairs`](Rule30Open/Columns/TrapPairs.lean) | `absorption_some_excludes`, `pair0001101101011_excludes`, `pair0010101111111_excludes` | 1 | not in the kit |
| [Entry into one of several traps for 29 blocks whose sampled halves stay apart from their single traps](Rule30Open/Columns/TrapSets.md) | [`Columns.TrapSets`](Rule30Open/Columns/TrapSets.lean) | `set0001101101011_excludes`, `set0000010101101_excludes`, `set000111111011101_excludes` | 1 | not in the kit |
| [Four traps for 001, pairwise apart, so the kit's AbsorptionT t001 is false and so is entry into one of any three](Rule30Open/Columns/Traps001.md) | [`Columns.Traps001`](Rule30Open/Columns/Traps001.lean) | `not_absorptionT_t001`, `traps001_pair_not_absorption`, `t001W_not_absorption_some`, `traps001_excludes`, `absorption_any_excludes` | 1 | not in the kit |
| [A right half white past its first twelve cells enters the ether-and-wall family, whatever lies beyond the gap](Rule30Open/Columns/TwelveCells.md) | [`Columns.TwelveCells`](Rule30Open/Columns/TwelveCells.lean) | `twelve_absorption`, `twelve_0001`, `twelve_0011`, `twelve_0111`, `twelveRight_0001`, `twelveRight_0011`, `twelveRight_0111`, `smallTwelve_0001`, `smallTwelve_0011`, `smallTwelve_0111` | 1 | extends a kit result |
| [Traps for 83 of the 335 blocks of period 12, from walls of period twelve carried leftward](Rule30Open/Columns/TwelveTraps.md) | [`Columns.TwelveTraps`](Rule30Open/Columns/TwelveTraps.lean) | `twelveTraps_check`, `twelveTraps_blocks`, `twelve_absorption_excludes` | 1 | not in the kit |
| [No finite configuration white on cells 9 to 1,610 has a center repeating 00000011011, nor one white on cells 9 to 2,357 a center repeating 001011100111](Rule30Open/Columns/WallGaps.md) | [`Columns.WallGaps`](Rule30Open/Columns/WallGaps.lean) | `eleven_gap`, `eleven_white`, `twelve_gap`, `twelve_white` | 1 | not in the kit |
| [After nine 1s the next cell stays known through five kinds of segment, excluding infinite families of periods](Rule30Open/Columns/WallSegments.md) | [`Columns.WallSegments`](Rule30Open/Columns/WallSegments.lean) | `center_run_family`, `center_wall_block`, `center_run_segment`, `wall_segments_column`, `run_family_column` | 1 | extends a kit result |
| [After nine 1s, the set of possible three-cell windows excludes every block with nine 1s that the game excludes](Rule30Open/Columns/WallSets.md) | [`Columns.WallSets`](Rule30Open/Columns/WallSets.lean) | `center_wall_set_block`, `center_runs_odd_100`, `center_runs_odd_110`, `center_runs_even_1010`, `wall_sets_column` | 1 | extends a kit result |
| [A right half white past its first six cells enters the ether-and-wall family, whatever lies beyond the gap](Rule30Open/Columns/WhiteGap.md) | [`Columns.WhiteGap`](Rule30Open/Columns/WhiteGap.lean) | `drv_cone`, `inFamily_of_check_cone`, `gap_absorption`, `gap_0001`, `gap_0011`, `gap_0111`, `gapRight_0001`, `gapRight_0011`, `gapRight_0111`, `high_0011`, `high_0111` | 1 | extends a kit result |
| [Against a white right half, no left half within depth 32,751 keeps the center on 011 through 16 steps past its width](Rule30Open/Columns/WhiteRightHalf011.md) | [`Columns.WhiteRightHalf011`](Rule30Open/Columns/WhiteRightHalf011.lean) | `white_right_leaves_011`, `psi011_gaps`, `leaves_by_lc`, `left_eq_lc`, `psiBitsC_spec`, `colC_testBit`, `rh_white` | 1 | extends a kit result |
| [A black run of r ≥ 9 steps rules out every eventual period with a tail of at most 4⌊r/9⌋ steps; nine 1s and then b 0s rule out every tail of at most 4⌊(b - 1)/9⌋ + 2](Rule30Open/Columns/WideWall.md) | [`Columns.WideWall`](Rule30Open/Columns/WideWall.lean) | `center_long_run_tail`, `center_black_white_tail`, `long_run_tail_column`, `black_white_tail_column`, `wide_wall_column`, `stripe_agree`, `black_shield` | 1 | extends a kit result |
| [Walls of 22 cells beside traps carried far along a background's columns, and entry into one of the two](Rule30Open/Columns/WideWalls.md) | [`Columns.WideWalls`](Rule30Open/Columns/WideWalls.lean) | `wideWalls_check`, `widePair_00100100101_excludes`, `el0_33_not_absorption_fwd`, `wide_el0_33_not_absorption` | 1 | not in the kit |
| [An eventual period of the center column needs T + P of at least 262,125](Rule30Open/Columns/WideWindow.md) | [`Columns.WideWindow`](Rule30Open/Columns/WideWindow.lean) | `runRel_fst`, `runRel_snd`, `center_eq_wide`, `wideFactor_new`, `transient_add_period_ge_262125` | 1 | extends a kit result |
| [Traps for blocks of period 2, 3, 5, 6, 7 and 9, by the kit's labelled-trap check for a block of any period](Rule30Open/Columns/WordTraps.md) | [`Columns.WordTraps`](Rule30Open/Columns/WordTraps.lean) | `wtrap_column`, `center_wtrap`, `absorption_excludes`, `not_eventually_01_of_absorption`, `not_eventually_001_of_absorption_fifteen`, `not_eventually_01111_of_absorption`, `not_eventually_001011_of_absorption`, `not_eventually_0011101_of_absorption`, `not_eventually_001011101_of_absorption` | 1 | extends a kit result |

**Findings**

| Result | Status | Problems | Formalization |
|---|---|---|---|
| [Every right half of up to 20 cells enters the kit's ether-and-wall family](findings/columns/absorption-census.md) | computed | 1 | partial |
| [A second infinite right half that never enters the kit's family for 0001, a background of 80 cells](findings/columns/background-halves.md) | computed | 1 | partial |
| [The game with cyclic classes closes ten blocks of period 13 to 16, eight of period 17 and fifteen of period 18 that nothing else excludes](findings/columns/class-blocks.md) | computed | 1 | partial |
| [The game with cyclic classes at 16 cells excludes 000000001011, a block of period 12 nothing else excludes](findings/columns/class-game.md) | computed | 1 | partial |
| [Every window can reach the period-four certificate, so a fair coin beyond it locks the right half](findings/columns/coin-lock.md) | computed | 1 | partial |
| [Beside 0001, column 1 moves in blocks of four along a graph of 13 edges, and a repeated block forces the ether](findings/columns/column-one-blocks.md) | proved on paper | 1 | wanted |
| [Up to period 15, what the exclusions and reductions in Lean reach, period by period](findings/columns/coverage.md) | computed | 1 | not applicable |
| [Against a right half of at most 11 to 14 cells, no left half of fewer than 1,000 cells keeps the center on a block of period 2, 3, 5, 6, 7 or 9](findings/columns/finite-onset-census.md) | computed | 1 | partial |
| [The finite game excludes 261 of the 22,242 blocks of period 17 and 18](findings/columns/game-blocks-18.md) | computed | 1 | partial |
| [The finite game excludes 508 of the 79,971 blocks of period 19 and 20](findings/columns/game-blocks-20.md) | computed | 1 | partial |
| [The finite game excludes 434 of the 99,858 blocks of period 21](findings/columns/game-blocks-21.md) | computed | 1 | partial |
| [The finite game excludes 197 of the 8,800 blocks up to period 16](findings/columns/game-blocks.md) | computed | 1 | partial |
| [The kit's two absorption conjectures pass the test of reach that refutes seven traps found here](findings/columns/kit-absorption-reach.md) | computed | 1 | not applicable |
| [No left half of up to 80 cells meets the kit's C3 for a period-four word](findings/columns/left-half-c3.md) | computed | 1 | partial |
| [No small left half meets the left-half statement of any block of period 3, 5, 6, 7 or 9](findings/columns/left-half-every-block.md) | computed | 1 | partial |
| [Windows of 14 cells followed through the column's whole history exclude every tail of up to six cells but 10101 after 22 white cells, and 1,672 blocks of period at most 22](findings/columns/limit-windows.md) | computed | 1 | wanted |
| [Locks carried leftward from a few seeds give every locked window of 13 cells up to period 12, both of the kit's traps, and locked windows for a block of every period from 2 to 9](findings/columns/lock-chains.md) | computed | 1 | partial |
| [Driven right halves settle into traps for 27 of the 99 blocks of period 10, 51 of the 186 of period 11 and 75 of the 335 of period 12](findings/columns/natural-traps.md) | computed | 1 | partial |
| [Locked windows of 20 or 22 cells give traps that pass both tests to 14 blocks whose other traps all fail](findings/columns/own-locks.md) | computed | 1 | wanted |
| [A width-16 window certifies the period-four lock from most starts](findings/columns/period-four-certificate.md) | computed | 1 | partial |
| [The three words of period four lock the right half](findings/columns/period-four-locking.md) | conjecture | 1 | wanted |
| [A random right half driven by a period-four word, the exact law of its row and a zero-one reduction of entry](findings/columns/random-halves.md) | proved on paper | 1 | wanted |
| [Beside a center that repeats a block, column 1 falls into a set of words of low entropy, from every state for 15 blocks of period 3 to 7](findings/columns/reading-constraints.md) | computed | 1 | partial |
| [Every background of Rule 30 periodic in time, to period 14, and the traps at their edges](findings/columns/space-time-backgrounds.md) | computed | 1 | partial |
| [For 72 blocks of period at most 12, every window of 13 cells can be steered into a lock](findings/columns/steerable-locks.md) | computed | 1 | partial |
| [Every right half of up to ten cells enters the kit's trap for 001, some only after 10^5 steps](findings/columns/t001-census.md) | computed | 1 | partial |

**Negative results**

| Result | Kind | Problems |
|---|---|---|
| [The Conley index of the windows beside a repeating column excludes no block, and over GF(2) it vanishes for a block that a background repeats](negative-results/columns/conley-index.md) | refuted | 1 |
| [Constraining the free bits of column -1 by the right half lowers the entropy of the left-half statements for 001 and 011, and no finite left game closes](negative-results/columns/constrained-left-halves.md) | dead end | 1 |
| [Column words that fix the cell beside the column exclude no block the finite game misses, up to period 20](negative-results/columns/forcing-words.md) | no signal | 1 |
| [Jen's theorem on farther columns, or on periods longer than the block's, does not strengthen the finite game](negative-results/columns/jen-farther-columns.md) | no signal | 1 |
| [From a late onset a small row follows a periodic word no longer than a random one](negative-results/columns/late-onset.md) | no signal | 1 |
| [Entry into 360 of the 1,595 traps of the trap modules is false, so their reductions were empty](negative-results/columns/missed-traps.md) | refuted | 1 |
| [Driven by 011, the right half does not settle next to the center](negative-results/columns/period-three-011.md) | no signal | 1 |
| [No row of up to 24 cells has a column that repeats from time 0](negative-results/columns/periodic-from-start.md) | no signal | 1 |
| [Periodic orbits on rings of up to 25 cells explain the finite game's failure only for the alternating block](negative-results/columns/ring-orbits.md) | no signal | 1 |
| [The sheaf of patches beside a repeating column gives back the finite game, and its cohomology is weaker than the limit windows one cell narrower](negative-results/columns/sheaf-sections.md) | dead end | 1 |
| [A search for slow right halves finds no counterexample and misses the slowest halves](negative-results/columns/slow-half-search.md) | no signal | 1 |
| [Right halves driven by blocks of period 5, 6 and 7 almost never enter a trap](negative-results/columns/trap-entry.md) | no signal | 1 |
| [No window of up to 20 cells locks for any block of period 2, 3, 5, 6, 7 or 9](negative-results/columns/window-locks.md) | no signal | 1 |
| [Windows of up to 16 cells with the column's whole history leave the kit's white-run thresholds where they are](negative-results/columns/window-thresholds.md) | barrier | 1 |
| [Reading lists of entropy 0 fail at up to 16 cells for every block of period 3 to 9 that the game does not exclude, and for 720 of 744 up to period 12](negative-results/columns/zero-entropy-readings.md) | barrier | 1 |

## Period two

The first open period of Prize Problem 1, reduced to a question about one integer map.

**Proved in Lean**

| Result | Module | Headline theorems | Problems | Kit |
|---|---|---|---|---|
| [The period-two condition is invisible at a bounded lag](Rule30Open/PeriodTwo/BoundedLag.md) | [`PeriodTwo.BoundedLag`](Rule30Open/PeriodTwo/BoundedLag.lean) | `held_preimage`, `pull_back`, `complete_window`, `invisible_at_bounded_lag`, `inK_window_invisible`, `invisible_at_bounded_lag_rational` | 1 | not in the kit |
| [The alternating domains time the period-two condition](Rule30Open/PeriodTwo/Domains.md) | [`PeriodTwo.Domains`](Rule30Open/PeriodTwo/Domains.lean) | `held_domains_odd`, `held_countdown`, `held_disagree`, `held_agree_stepB` | 1 | independent proof of a kit result |
| [Every head of up to 12 cells on the ether settles, so (R) holds for every 2-adic rational whose tail from cell 12 on is the ether](Rule30Open/PeriodTwo/EtherCensus.md) | [`PeriodTwo.EtherCensus`](Rule30Open/PeriodTwo/EtherCensus.lean) | `ether_tail_clear`, `ether_tail_eventually_periodic`, `ether_tail_itinerary`, `closedOK_true`, `closed_count`, `stripInv_forever`, `runHead_sound`, `census`, `eventually_periodic_of_clear`, `eth_eq_kit_ether` | 1 | not in the kit |
| [Every head of up to 16 cells on the ether settles, so (R) holds for every 2-adic rational whose tail from cell 16 on is the ether](Rule30Open/PeriodTwo/EtherCensus16.md) | [`PeriodTwo.EtherCensus16`](Rule30Open/PeriodTwo/EtherCensus16.lean) | `ether_tail_clear_16`, `ether_tail_eventually_periodic_16`, `ether_tail_itinerary_16`, `descCensus`, `runDesc_sound`, `descend`, `headsBelow_block`, `headsBelow_chunk`, `headsBelow_12`, `defect_shift` | 1 | not in the kit |
| [Every point of K whose tail from cell 28 on is the ether keeps its defect below cell 28, so (R) holds for it](Rule30Open/PeriodTwo/EtherKTree.md) | [`PeriodTwo.EtherKTree`](Rule30Open/PeriodTwo/EtherKTree.lean) | `ether_k_tail_clear`, `ether_k_tail_eventually_periodic`, `ether_k_tail_itinerary`, `clear_of_etherTree`, `etherLeaf_sound` | 1 | not in the kit |
| [Period two reduces to an integer map](Rule30Open/PeriodTwo/HeldColumn.md) | [`PeriodTwo.HeldColumn`](Rule30Open/PeriodTwo/HeldColumn.lean) | `period_two_held`, `period_two_integer`, `center_period_two_integer`, `heldNat_testBit` | 1 | independent proof of a kit result |
| [No point of K has a tail on the backgrounds with (L, P) = (4, 8), (5, 5), (10, 15) or (12, 3) from cell 12 on](Rule30Open/PeriodTwo/NoKTails.md) | [`PeriodTwo.NoKTails`](Rule30Open/PeriodTwo/NoKTails.lean) | `no_k_tail_48`, `no_k_tail_55`, `no_k_tail_1015`, `no_k_tail_123`, `not_inK_of_tables`, `breakRun_sound`, `column_eq_of_agree`, `ringCell_step` | 1 | not in the kit |
| [No point of K has a tail from cell 16 on equal to a background of the tail census other than the stripes and the ether](Rule30Open/PeriodTwo/NoKTails16.md) | [`PeriodTwo.NoKTails16`](Rule30Open/PeriodTwo/NoKTails16.lean) | `no_k_tail16_L1P1`, `no_k_tail16_L4P8`, `no_k_tail16_L5P5`, `no_k_tail16_L7P63`, `no_k_tail16_L8P40`, `no_k_tail16_L9P72`, `no_k_tail16_L9P171`, `no_k_tail16_L10P15`, `no_k_tail16_L11P17`, `no_k_tail16_L11P154`, `no_k_tail16_L12P3`, `no_k_tail16_L12P102`, `treeWith_sound`, `treeRun_sound`, `not_inK_of_tree`, `colRaw_eq`, `tabOK_spec` | 1 | not in the kit |
| [A lock of period seven beside an alternating center excludes period two for every right half that enters it](Rule30Open/PeriodTwo/SevenLock.md) | [`PeriodTwo.SevenLock`](Rule30Open/PeriodTwo/SevenLock.lean) | `sevenLock_check`, `sevenLock_forever`, `sevenLock_periodic`, `sevenLock_not_finSupp_Psi`, `no_alternating_of_sevenLock`, `no_alternating_sevenLock_example` | 1 | not in the kit |
| [The period-two condition is a full 2-shift on 2-adic halves](Rule30Open/PeriodTwo/ShiftModel.md) | [`PeriodTwo.ShiftModel`](Rule30Open/PeriodTwo/ShiftModel.lean) | `heldOrbit_triangular`, `column_bijective`, `inK_graph`, `itinerary_bijective`, `held_held_two_to_one`, `heldNat_triangular`, `inK_periodic_rational`, `inK_periodic_not_finite`, `positive_integer_not_preperiodic` | 1 | independent proof of a kit result |
| [Against a white right half, no left half within depth 32,755 keeps the center alternating](Rule30Open/PeriodTwo/WhiteRightHalf.md) | [`PeriodTwo.WhiteRightHalf`](Rule30Open/PeriodTwo/WhiteRightHalf.lean) | `white_right_leaves`, `psi_empty_gaps`, `leaves_by_gap`, `psiBits_spec` | 1 | extends a kit result |

**Findings**

| Result | Status | Problems | Formalization |
|---|---|---|---|
| [No row with its leftmost 1 within 120 cells has an alternating center](findings/period-two/alternating-within-120.md) | computed | 1 | wanted |
| [Rows of radius up to 26 keep an alternating center from time 0 for at most 36 steps, with no law like the constant center's radius plus 2](findings/period-two/condrey-carryover.md) | computed | 1 | wanted |
| [Every defect of up to 20 cells on the ether settles, so (R) holds for those ether tails; a potential on top windows fails even along one real orbit](findings/period-two/ether-defect-census.md) | computed | 1 | partial |
| [Beside an alternating center every right half of up to 20 cells enters a gap trap, the kit's ether family or a lock of period seven](findings/period-two/gate-census.md) | computed | 1 | partial |
| [Every integer below 2^52 fails the period-two condition, near step 2M](findings/period-two/left-half-alone.md) | computed | 1 | partial |
| [Beside an alternating center the right half nearly locks, and slips](findings/period-two/right-channel.md) | computed | 1 | not applicable |
| [The period-two condition is a full 2-shift whose periodic points are domains, and its rational points are preperiodic as far as tried](findings/period-two/shift-model.md) | computed | 1 | partial |
| [The slips of the right channel are one front crossing a locked layer, fed from the chaotic region at the leftward speed of Rule 30](findings/period-two/slip-geometry.md) | computed | 1 | not applicable |
| [Beyond the stripes and the ether, every periodic tail of up to 12 cells falls onto a background where the tops of most defects run away, and no head of up to 16 cells on one of them is in K](findings/period-two/tail-census.md) | computed | 1 | partial |
| [Against a white right half, no left half of fewer than a million cells keeps the center alternating](findings/period-two/white-right-half.md) | computed | 1 | partial |

**Negative results**

| Result | Kind | Problems |
|---|---|---|
| [The ether-and-wall family does not catch the right half beside an alternating center](negative-results/period-two/absorption-route.md) | dead end | 1 |
| [Condrey's proof for a constant center does not extend to an alternating center](negative-results/period-two/condrey-mechanism.md) | dead end | 1 |
| [Windows of 5, 8, 10 and 12 cells at the top of a defect on the ether do not bound it, with or without the condition of K](negative-results/period-two/ether-front-windows.md) | barrier | 1 |
| [The left half is not a patchwork of ether domains](negative-results/period-two/ether-patchwork.md) | refuted | 1 |
| [The first twelve forced bits of the period-two condition are dense polynomials of full degree](negative-results/period-two/forced-bits-dense.md) | dead end | 1 |
| [A bounded defect top does not give (R) for the periodic tails of up to 12 cells beyond the stripes and the ether, since the tops run away, provably on 10 of the 12 backgrounds](negative-results/period-two/front-backgrounds.md) | refuted | 1 |
| [No finite certificate settles period two](negative-results/period-two/no-finite-certificate.md) | dead end | 1 |

## Diagonals

The periodic diagonals of the regular left side, and where their periods grow.

**Proved in Lean**

| Result | Module | Headline theorems | Problems | Kit |
|---|---|---|---|---|
| [Every configuration white left of a black cell settles to the single cell's pairs of left diagonals up to a time shift, as long as each white diagonal is followed by a doubling period](Rule30Open/Diagonals/DrivenSkeleton.md) | [`Diagonals.DrivenSkeleton`](Rule30Open/Diagonals/DrivenSkeleton.lean) | `shift_of_black`, `shift_or_flip_of_white`, `skeleton_step`, `skeleton_step_of_flip`, `base_shift` | 2 | not in the kit |
| [A walk that steps down on black cells and down-left on white ones bounds when the left diagonals settle; it advances 2.01 times per depth to depth 200,000, and a walk of slope 2 + o(1) would give black center runs of slope 1/3](Rule30Open/Diagonals/FrontWalker.md) | [`Diagonals.FrontWalker`](Rule30Open/Diagonals/FrontWalker.lean) | `pair_repeats_of_walk`, `black_run_le_of_walk`, `black_run_le_of_steep_walk` | 2 | extends a kit result |
| [Left diagonals remember only behind a white diagonal](Rule30Open/Diagonals/LeftMemory.md) | [`Diagonals.LeftMemory`](Rule30Open/Diagonals/LeftMemory.lean) | `D_reset`, `D_periodic_of_black`, `D_period_dichotomy`, `D_period_doubles`, `D_two_white`, `D_three_flips` | 1 | extends a kit result |
| [Behind a walk through its black cells, a left diagonal of any row white left of a cell forgets the cells past a prefix; this bounds the onsets of every extension of the prefix at once](Rule30Open/Diagonals/PrefixWalk.md) | [`Diagonals.PrefixWalk`](Rule30Open/Diagonals/PrefixWalk.lean) | `agree_of_walk`, `Ld_agree_of_prefix`, `Ld_agree_of_walk`, `Ld_repeats_of_walk` | 2 | extends a kit result |
| [If the left diagonals repeat with period 16 from time 3j/2 to depth J, black center runs have 13L at most 3a + 2400 and white blocks reach left at most (a + 100)/3](Rule30Open/Diagonals/SettledRuns.md) | [`Diagonals.SettledRuns`](Rule30Open/Diagonals/SettledRuns.lean) | `no_alt_pair`, `settled_alt_pair`, `no_white_pair`, `erode_alt`, `black_run_le_of_settled`, `white_block_le_of_settled` | 2 | not in the kit |
| [If the left diagonals repeat from time 3j/2 with any periods and no settled pair alternates in antiphase more than A times, black center runs have 13L at most 3a + 130A + 260; the reset bound reduces the settling to the white runs of the settled diagonals](Rule30Open/Diagonals/SettledSlope.md) | [`Diagonals.SettledSlope`](Rule30Open/Diagonals/SettledSlope.lean) | `altBound_of_repeats`, `altBound_of_period_le`, `black_run_window`, `black_run_le_of_settling`, `black_run_le_of_fast_settling`, `pair_repeats_of_white_runs`, `black_run_le_of_white_runs` | 2 | not in the kit |

**Findings**

| Result | Status | Problems | Formalization |
|---|---|---|---|
| [Whatever the center column, the left half it drives allows a black run from time t of at most 0.13t to 0.18t and a white run of at most 0.15t to 0.28t for t from 75 to 175, far below the kit's slopes 3/5 and 1](findings/diagonals/driven-left-runs.md) | conjecture | 2 | wanted |
| [Where the left diagonals turn white, to depth 100,000](findings/diagonals/left-records.md) | computed | 1 | partial |
| [Over every row white left of a black cell, the left diagonal j settles by time ceil(3j/2) + 5 for j up to 76, exactly; from depth 9 to 76 the worst row is the single cell delayed by 6 to 8 steps, and the bound is conjectured for every j](findings/diagonals/seed-uniform-onsets.md) | conjecture | 2 | wanted |
| [A linear settling time of the left diagonals with periods o(j) would cut the slope of center-column runs to 3/13 (black) and 1/3 (white) at settling time 3j/2; depths 8 to 7,999 repeat with period 16 from time 3j/2 to time 12,583](findings/diagonals/settled-runs.md) | conjecture | 2 | partial |

**Negative results**

| Result | Kind | Problems |
|---|---|---|
| [Three routes to a run slope below 3/5 over every driven left half stop at the settling time of the left diagonals, which over every driver is the single cell's open problem with a transient added](negative-results/diagonals/driven-run-slopes.md) | dead end | 2 |
| [A finite automaton over the center column certifies no slope for black runs of the driven left half unless those runs are bounded](negative-results/diagonals/finite-state-slopes.md) | barrier | 2 |
| [Direct comparison with a true strip of the pattern near the left edge of any fixed depth leaves the slope of black center runs at 3/5](negative-results/diagonals/fixed-depth-strips.md) | barrier | 2 |
| [Three leads to linear settling of the single cell's left diagonals stop, to depth 200,000, at the transient or at a law of large numbers for the settled left side; the onset phases are uniform, the front shows nothing at the white diagonals, and no settled pair repeats up to a time shift](negative-results/diagonals/linear-settling-leads.md) | dead end | 2 |
| [A seed-uniform induction on the onsets of the left diagonals stops at slope 2; the later row is a seed whose settled prefix leaves the rest free, the fresh-seed subadditivity fails at one diagonal, and the single cell is the worst seed up to a delay of 8 at every depth to 76 but not at depth 139](negative-results/diagonals/seed-uniform-induction.md) | dead end | 2 |

## Frames and the seed's past

Rule 30 as a bijection of the 2-adic integers, the center column as a trace, and the rows that lead to the seed.

**Proved in Lean**

| Result | Module | Headline theorems | Problems | Kit |
|---|---|---|---|---|
| [Every row of the single cell's past is eventually periodic to the left](Rule30Open/Frames/SeedPast.md) | [`Frames.SeedPast`](Rule30Open/Frames/SeedPast.lean) | `phiF_phiInv`, `phiInv_phiF`, `past_unique`, `phiInv_evPer`, `rho_evPer`, `frame_step`, `past_evPer` | 1 | extends a kit result |
| [The periods of the single cell's past grow without bound](Rule30Open/Frames/SeedPastPeriods.md) | [`Frames.SeedPastPeriods`](Rule30Open/Frames/SeedPastPeriods.lean) | `phiF_topAt`, `rho_not_evZero`, `rho_iter`, `agree_of_period`, `pigeonhole`, `rho_period_bound`, `rho_no_short_period` | 1 | extends a kit result |

**Findings**

| Result | Status | Problems | Formalization |
|---|---|---|---|
| [Only the stripe and the ether backgrounds give a periodic column](findings/frames/periodic-backgrounds.md) | computed | 1 | wanted |
| [The single cell has a unique past, and every row of it is periodic](findings/frames/seed-past.md) | proved on paper | 1 | partial |
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
| [No small algebraic equation for the center column, and no Rule 30 signal in the cut ranks of the cone](negative-results/structure/hidden-algebra.md) | no signal | 1, 3 |
| [No linear relation among subsequences of the center column](negative-results/structure/linear-relations.md) | no signal | 1, 3 |
| [The single cell's pattern has no periodic domains of short spatial period, so it has no ether walls whose slopes or holonomy could be read](negative-results/structure/pattern-domains.md) | no signal | 1 |
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
| [No linear or learned projection tells the chaotic region of the single cell from the invariant measure](negative-results/statistics/patch-projections.md) | no signal | 2 |
| [Persistent homology does not tell the single cell's center from random rows](negative-results/statistics/persistent-homology.md) | no signal | 1, 2 |
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

**Proved in Lean**

| Result | Module | Headline theorems | Problems | Kit |
|---|---|---|---|---|
| [An alternating left half fixes the center cell whatever the right half is](Rule30Open/Complexity/ConeScreening.md) | [`Complexity.ConeScreening`](Rule30Open/Complexity/ConeScreening.lean) | `screening_odd`, `screening_even`, `stripe`, `pair_back`, `evo_local`, `front_xor`, `flip_center`, `center_decomp`, `decomp_local`, `four_words` | 3 | extends a kit result |
| [A one-tape machine computes the center column in 2n² + 2n log n + O(n) steps, so the kit's Problem 3 asks for the exponent between 1 and 2](Rule30Open/Complexity/QuadraticTime.md) | [`Complexity.QuadraticTime`](Rule30Open/Complexity/QuadraticTime.lean) | `simulator_time`, `simulator_computes`, `center_computes_quadratic` | 3 | not in the kit |
| [A decision tree for the center cell from an arbitrary row spends exactly one query on the leftmost cell, so with the kit's degree bound it reads at least 2t cells; computation gives all 2t + 1 for t ≤ 17](Rule30Open/Complexity/QueryDepth.md) | [`Complexity.QueryDepth`](Rule30Open/Complexity/QueryDepth.lean) | `depth_restrict_succ_le`, `eval_restrict`, `tree_drop_of_flip`, `center_tree_drop`, `center_tree_lift` | 3 | extends a kit result |
| [The center never depends on all three rightmost cone cells at one row, so its certificate complexity is at most 2t](Rule30Open/Complexity/RightCorner.md) | [`Complexity.RightCorner`](Rule30Open/Complexity/RightCorner.lean) | `right_corner`, `right_corner_certificate`, `corner_white`, `strip_one`, `strip_two`, `strip_three` | 3 | not in the kit |

**Findings**

| Result | Status | Problems | Formalization |
|---|---|---|---|
| [An alternating left half fixes the center cell whatever the right half is, so the left half of the cone is not incompressible](findings/complexity/cone-screening.md) | proved on paper | 3 | partial |
| [Problems 1 and 3 follow from space lower bounds for the center column, and space √(n log n) suffices](findings/complexity/space-ladder.md) | proved on paper | 3, 1 | partial |
| [The center column is computed in space √(n log n), and each simulation sets a threshold that a space lower bound must pass](findings/complexity/space-thresholds.md) | proved on paper | 3, 1 | partial |

**Negative results**

| Result | Kind | Problems |
|---|---|---|
| [No automaton with fewer than 131,070 states computes the column from the digits of t](negative-results/complexity/automaton-lower-bounds.md) | no signal | 3 |
| [The Unique Games Conjecture and the Exponential Time Hypothesis do not decide Problem 3](negative-results/complexity/hardness-hypotheses.md) | barrier | 3, 1, 2 |
| [The linear complexity is n/2, the most a sequence can have](negative-results/complexity/linear-complexity.md) | no signal | 1, 3 |
| [Crossing sequences prove at most time (log n)² for the center column, and need a spectral hypothesis that implies Problem 1](negative-results/complexity/one-tape-crossing.md) | barrier | 3, 1 |
| [Probabilistic checking verifies the center cell cheaply, as it does every computation, and does not compute it](negative-results/complexity/probabilistic-checking.md) | barrier | 3, 1, 2 |
| [Problem 3 asks for a lower bound beyond current complexity theory](negative-results/complexity/problem-three-barrier.md) | barrier | 3, 1 |
| [Sensitivity, certificates, fixed answers and one-step lifting do not show that the center needs its whole cone](negative-results/complexity/query-depth-routes.md) | barrier | 3 |
| [Restricted models give the center cell no new lower bound for every n; past reading the digits they imply Problem 1, and spacetime bounds hold for Rule 90](negative-results/complexity/restricted-models.md) | barrier | 3, 1 |
