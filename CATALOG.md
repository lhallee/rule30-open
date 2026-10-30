# Catalog

Every result in this repository, by category. `python scripts/catalog.py write` generates this page from the
front matter of the entries; edit the entries, not this page.

65 Lean modules with 305 headline theorems, 27 findings (proved on paper,
computed or conjectured) and 31 negative results. Prize problem 1 asks whether the center column
is eventually periodic, 2 whether its density of black cells tends to 1/2, and 3 whether computing its cell `n`
takes effort of order `n`.

| Category | Lean modules | Findings | Negative results |
|---|---:|---:|---:|
| [Foundations](#foundations) | 3 | 0 | 0 |
| [Seeds](#seeds) | 1 | 1 | 0 |
| [Columns](#columns) | 52 | 14 | 8 |
| [Period two](#period-two) | 3 | 4 | 3 |
| [Diagonals](#diagonals) | 1 | 1 | 0 |
| [Frames and the seed's past](#frames-and-the-seeds-past) | 2 | 3 | 1 |
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

- [Only the stripe and the ether backgrounds give a periodic column](findings/frames/periodic-backgrounds.md): problem 1
- [No row with its leftmost 1 within 120 cells has an alternating center](findings/period-two/alternating-within-120.md): problem 1

**Findings proved in Lean in part**

- [Every right half of up to 20 cells enters the kit's ether-and-wall family](findings/columns/absorption-census.md): problem 1
- [Every window can reach the period-four certificate, so a fair coin beyond it locks the right half](findings/columns/coin-lock.md): problem 1
- [The finite game excludes 261 of the 22,242 blocks of period 17 and 18](findings/columns/game-blocks-18.md): problem 1
- [The finite game excludes 508 of the 79,971 blocks of period 19 and 20](findings/columns/game-blocks-20.md): problem 1
- [The finite game excludes 197 of the 8,800 blocks up to period 16](findings/columns/game-blocks.md): problem 1
- [No left half of up to 80 cells meets the kit's C3 for a period-four word](findings/columns/left-half-c3.md): problem 1
- [No small left half meets the left-half statement of any block of period 3, 5, 6, 7 or 9](findings/columns/left-half-every-block.md): problem 1
- [Locks carried leftward from a few seeds give every locked window of 13 cells up to period 12, both of the kit's traps, and locked windows for a block of every period from 2 to 9](findings/columns/lock-chains.md): problem 1
- [Driven right halves settle into traps for 27 of the 99 blocks of period 10, 51 of the 186 of period 11 and 75 of the 335 of period 12](findings/columns/natural-traps.md): problem 1
- [A width-16 window certifies the period-four lock from most starts](findings/columns/period-four-certificate.md): problem 1
- [For 72 blocks of period at most 12, every window of 13 cells can be steered into a lock](findings/columns/steerable-locks.md): problem 1
- [Every right half of up to ten cells enters the kit's trap for 001, some only after 10^5 steps](findings/columns/t001-census.md): problem 1
- [Problems 1 and 3 follow from space lower bounds for the center column, and space √n log n suffices](findings/complexity/space-ladder.md): problems 3, 1
- [Where the left diagonals turn white, to depth 100,000](findings/diagonals/left-records.md): problem 1
- [Information reaches the center from the left at speed 1, from the right at about 0.4](findings/dynamics/one-way-valve.md): problems 1, 2
- [The single cell has a unique past, and every row of it is periodic](findings/frames/seed-past.md): problem 1
- [Every integer below 2^52 fails the period-two condition, near step 2M](findings/period-two/left-half-alone.md): problem 1
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
| [The game decided in the kernel and the window-set check exclude 99 more blocks of period 17](Rule30Open/Columns/BitBlocks17.md) | [`Columns.BitBlocks17`](Rule30Open/Columns/BitBlocks17.lean) | `center_not_blocks17`, `not_eventually_blocks17`, `center_not_wallBlocks17` | 1 | not in the kit |
| [The game decided in the kernel and the window-set check exclude 122 more blocks of period 18](Rule30Open/Columns/BitBlocks18.md) | [`Columns.BitBlocks18`](Rule30Open/Columns/BitBlocks18.lean) | `center_not_blocks18`, `not_eventually_blocks18`, `center_not_wallBlocks18` | 1 | not in the kit |
| [The game decided in the kernel and the window-set check exclude 133 more blocks of period 19](Rule30Open/Columns/BitBlocks19.md) | [`Columns.BitBlocks19`](Rule30Open/Columns/BitBlocks19.lean) | `center_not_blocks19`, `not_eventually_blocks19`, `center_not_wallBlocks19` | 1 | not in the kit |
| [The game decided in the kernel excludes 57 more blocks of period 19 that need 7 to 12 cells](Rule30Open/Columns/BitBlocks19Wide.md) | [`Columns.BitBlocks19Wide`](Rule30Open/Columns/BitBlocks19Wide.lean) | `center_not_blocks19Wide`, `not_eventually_blocks19Wide` | 1 | not in the kit |
| [The game decided in the kernel and the window-set check exclude 160 more blocks of period 20](Rule30Open/Columns/BitBlocks20.md) | [`Columns.BitBlocks20`](Rule30Open/Columns/BitBlocks20.lean) | `center_not_blocks20`, `not_eventually_blocks20`, `center_not_wallBlocks20` | 1 | not in the kit |
| [The game decided in the kernel excludes 55 more blocks of period 20 that need 7 or 8 cells](Rule30Open/Columns/BitBlocks20Mid.md) | [`Columns.BitBlocks20Mid`](Rule30Open/Columns/BitBlocks20Mid.lean) | `center_not_blocks20Mid`, `not_eventually_blocks20Mid` | 1 | not in the kit |
| [The game decided in the kernel excludes 44 more blocks of period 20 that need 9 to 12 cells](Rule30Open/Columns/BitBlocks20Wide.md) | [`Columns.BitBlocks20Wide`](Rule30Open/Columns/BitBlocks20Wide.lean) | `center_not_blocks20Wide`, `not_eventually_blocks20Wide` | 1 | not in the kit |
| [The finite game, decided in the kernel without a certificate, excludes seven blocks of period 14 to 16 that need 12 to 14 cells](Rule30Open/Columns/BitGame.md) | [`Columns.BitGame`](Rule30Open/Columns/BitGame.lean) | `bitGame_column`, `center_not_bitGame`, `bitGame_not_eventuallyWord`, `center_not_restBlocks`, `not_eventually_restBlocks` | 1 | not in the kit |
| [The game decided phase by phase in the kernel excludes the 14 blocks of period 17 and 18 that need 13 or 14 cells](Rule30Open/Columns/BitPhases.md) | [`Columns.BitPhases`](Rule30Open/Columns/BitPhases.lean) | `phases_column`, `center_not_phases`, `phases_not_eventuallyWord`, `center_not_blocksPhases18`, `not_eventually_blocksPhases18` | 1 | not in the kit |
| [The game decided phase by phase in the kernel excludes the 11 blocks of period 19 that need 13 or 14 cells](Rule30Open/Columns/BitPhases19.md) | [`Columns.BitPhases19`](Rule30Open/Columns/BitPhases19.lean) | `center_not_blocksPhases19`, `not_eventually_blocksPhases19` | 1 | not in the kit |
| [The game decided phase by phase in the kernel excludes the 15 blocks of period 20 that need 13 or 14 cells](Rule30Open/Columns/BitPhases20.md) | [`Columns.BitPhases20`](Rule30Open/Columns/BitPhases20.lean) | `center_not_blocksPhases20`, `not_eventually_blocksPhases20` | 1 | not in the kit |
| [Traps for 57 of the 186 blocks of period 11, from walls of period eleven carried leftward](Rule30Open/Columns/ElevenTraps.md) | [`Columns.ElevenTraps`](Rule30Open/Columns/ElevenTraps.lean) | `elevenTraps_check`, `elevenTraps_blocks`, `eleven_absorption_excludes` | 1 | not in the kit |
| [Against a right half of at most six cells no center column repeats a word of period four](Rule30Open/Columns/EmptyRight.md) | [`Columns.EmptyRight`](Rule30Open/Columns/EmptyRight.lean) | `smallRight_0001`, `smallRight_0011`, `smallRight_0111`, `emptyRight_001`, `no_finite_of_family`, `no_finite_of_ptrap` | 1 | extends a kit result |
| [The word 0001 comes down to the period-two map, and the ether is its domain](Rule30Open/Columns/EtherDomain.md) | [`Columns.EtherDomain`](Rule30Open/Columns/EtherDomain.lean) | `center_period_four_0001_integer`, `period_four_0001_held`, `held_etherLeft`, `ether_fits`, `ether_countdown`, `domainB_repeats` | 1 | extends a kit result |
| [Every truncation of the aligned ether, followed by a short word, enters the ether-and-wall family](Rule30Open/Columns/EtherPrefix.md) | [`Columns.EtherPrefix`](Rule30Open/Columns/EtherPrefix.lean) | `shift7_drv`, `shift7_family`, `prefix_absorption`, `etherPrefix_0001`, `etherPrefix_0011`, `etherPrefix_0111`, `prefixRight_0001`, `prefixRight_0011`, `prefixRight_0111` | 1 | extends a kit result |
| [Every truncation of the aligned ether, followed by any word of up to six cells, enters the ether-and-wall family](Rule30Open/Columns/EtherPrefixSix.md) | [`Columns.EtherPrefixSix`](Rule30Open/Columns/EtherPrefixSix.lean) | `prefix_of_tails_len`, `etherPrefixSix_0001`, `etherPrefixSix_0011`, `etherPrefixSix_0111`, `prefixSixRight_0001`, `prefixSixRight_0011`, `prefixSixRight_0111` | 1 | extends a kit result |
| [A finite game rules out repeating blocks](Rule30Open/Columns/FiniteGame.md) | [`Columns.FiniteGame`](Rule30Open/Columns/FiniteGame.lean) | `game_column`, `center_not_01111111`, `center_not_00000011` | 1 | independent proof of a kit result |
| [A right half white past its first fourteen cells enters the ether-and-wall family, whatever lies beyond the gap](Rule30Open/Columns/FourteenCells.md) | [`Columns.FourteenCells`](Rule30Open/Columns/FourteenCells.lean) | `fourteen_absorption`, `fourteen_0001`, `fourteen_0011`, `fourteen_0111`, `fourteenRight_0001`, `fourteenRight_0011`, `fourteenRight_0111`, `smallFourteen_0001`, `smallFourteen_0011`, `smallFourteen_0111` | 1 | extends a kit result |
| [The finite game, checked in bit masks, excludes 32 more blocks of period at most 14](Rule30Open/Columns/GameBlocks.md) | [`Columns.GameBlocks`](Rule30Open/Columns/GameBlocks.lean) | `mask_column`, `center_not_gameBlocks`, `not_eventually_gameBlocks` | 1 | not in the kit |
| [The finite game, checked in bit masks, excludes 97 more blocks of period 15 and 16](Rule30Open/Columns/GameBlocksLong.md) | [`Columns.GameBlocksLong`](Rule30Open/Columns/GameBlocksLong.lean) | `center_not_gameBlocks16`, `not_eventually_gameBlocks16` | 1 | not in the kit |
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
| [Traps for 34 more blocks of periods 10 to 12, the closed sets that driven right halves settle into](Rule30Open/Columns/NaturalTraps.md) | [`Columns.NaturalTraps`](Rule30Open/Columns/NaturalTraps.lean) | `naturalTraps_check`, `naturalTraps_blocks`, `natural_absorption_excludes` | 1 | not in the kit |
| [A trap of 61,857 states for the block 00010001011 of period 11, checked in parts](Rule30Open/Columns/NaturalTrapsLarge.md) | [`Columns.NaturalTrapsLarge`](Rule30Open/Columns/NaturalTrapsLarge.lean) | `allRange_cover`, `nat00010001011_check`, `not_eventually_00010001011_of_trap` | 1 | not in the kit |
| [Traps for 22 of the 56 blocks of period 9, from two walls of period nine that driven right halves enter](Rule30Open/Columns/NineTraps.md) | [`Columns.NineTraps`](Rule30Open/Columns/NineTraps.lean) | `nineTraps_check`, `nineTraps_blocks`, `nine_absorption_excludes`, `trap001010011_check`, `not_eventually_001010011_of_absorption` | 1 | not in the kit |
| [Right halves white on their first 91,129 to 201,172 cells enter the walls of period 9](Rule30Open/Columns/NineWhite.md) | [`Columns.NineWhite`](Rule30Open/Columns/NineWhite.lean) | `highRightW_of_entry`, `white_first_wall`, `white_first_wall_eight`, `white_second_wall`, `white_second_wall_zero` | 1 | not in the kit |
| [The period-four certificates are traps, and entry into one excludes its word](Rule30Open/Columns/PeriodFourCertificate.md) | [`Columns.PeriodFourCertificate`](Rule30Open/Columns/PeriodFourCertificate.lean) | `cert0001_check`, `cert0011_check`, `cert0111_check`, `not_eventually_0001_of_certificate`, `not_eventually_0011_of_certificate`, `not_eventually_0111_of_certificate` | 1 | not in the kit |
| [The cells left of a column count down its runs of 1s](Rule30Open/Columns/RunCountdown.md) | [`Columns.RunCountdown`](Rule30Open/Columns/RunCountdown.lean) | `run_countdown`, `run_bound`, `no_ones_column`, `center_not_eventually_ones` | 1 | extends a kit result |
| [A right half with at most two black cells among its first cells enters the ether-and-wall family](Rule30Open/Columns/SparseRight.md) | [`Columns.SparseRight`](Rule30Open/Columns/SparseRight.lean) | `inFamily_of_fast`, `stateAt_eq`, `two_absorption`, `sparse_0001`, `sparse_0011`, `sparse_0111`, `oneCell_0011`, `oneCell_0111`, `sparseRight_0001`, `sparseRight_0011`, `sparseRight_0111` | 1 | extends a kit result |
| [A right half white past its first ten cells enters the ether-and-wall family, whatever lies beyond the gap](Rule30Open/Columns/TenCells.md) | [`Columns.TenCells`](Rule30Open/Columns/TenCells.lean) | `ten_absorption`, `ten_0001`, `ten_0011`, `ten_0111`, `tenRight_0001`, `tenRight_0011`, `tenRight_0111`, `smallTen_0001`, `smallTen_0011`, `smallTen_0111` | 1 | extends a kit result |
| [No finite configuration whose cells 9 to 3,058 are white has a center column that repeats 0000010001](Rule30Open/Columns/TenGap.md) | [`Columns.TenGap`](Rule30Open/Columns/TenGap.lean) | `prefixRightW_of_entry`, `gapRightW_of_entries`, `ten_gap`, `ten_white` | 1 | not in the kit |
| [Traps for 25 blocks of period 10, from one background of period ten whose edge driven right halves enter](Rule30Open/Columns/TenTraps.md) | [`Columns.TenTraps`](Rule30Open/Columns/TenTraps.lean) | `tenTraps_check`, `tenTraps_blocks`, `ten_absorption_excludes` | 1 | not in the kit |
| [A right half white past its first twelve cells enters the ether-and-wall family, whatever lies beyond the gap](Rule30Open/Columns/TwelveCells.md) | [`Columns.TwelveCells`](Rule30Open/Columns/TwelveCells.lean) | `twelve_absorption`, `twelve_0001`, `twelve_0011`, `twelve_0111`, `twelveRight_0001`, `twelveRight_0011`, `twelveRight_0111`, `smallTwelve_0001`, `smallTwelve_0011`, `smallTwelve_0111` | 1 | extends a kit result |
| [Traps for 83 of the 335 blocks of period 12, from walls of period twelve carried leftward](Rule30Open/Columns/TwelveTraps.md) | [`Columns.TwelveTraps`](Rule30Open/Columns/TwelveTraps.lean) | `twelveTraps_check`, `twelveTraps_blocks`, `twelve_absorption_excludes` | 1 | not in the kit |
| [No finite configuration white on cells 9 to 1,610 has a center repeating 00000011011, nor one white on cells 9 to 2,357 a center repeating 001011100111](Rule30Open/Columns/WallGaps.md) | [`Columns.WallGaps`](Rule30Open/Columns/WallGaps.lean) | `eleven_gap`, `eleven_white`, `twelve_gap`, `twelve_white` | 1 | not in the kit |
| [After nine 1s the next cell stays known through five kinds of segment, excluding infinite families of periods](Rule30Open/Columns/WallSegments.md) | [`Columns.WallSegments`](Rule30Open/Columns/WallSegments.lean) | `center_run_family`, `center_wall_block`, `center_run_segment`, `wall_segments_column`, `run_family_column` | 1 | extends a kit result |
| [After nine 1s, the set of possible three-cell windows excludes every block with nine 1s that the game excludes](Rule30Open/Columns/WallSets.md) | [`Columns.WallSets`](Rule30Open/Columns/WallSets.lean) | `center_wall_set_block`, `center_runs_odd_100`, `center_runs_odd_110`, `center_runs_even_1010`, `wall_sets_column` | 1 | extends a kit result |
| [A right half white past its first six cells enters the ether-and-wall family, whatever lies beyond the gap](Rule30Open/Columns/WhiteGap.md) | [`Columns.WhiteGap`](Rule30Open/Columns/WhiteGap.lean) | `drv_cone`, `inFamily_of_check_cone`, `gap_absorption`, `gap_0001`, `gap_0011`, `gap_0111`, `gapRight_0001`, `gapRight_0011`, `gapRight_0111`, `high_0011`, `high_0111` | 1 | extends a kit result |
| [A black run of r ≥ 9 steps rules out every eventual period with a tail of at most 4⌊r/9⌋ steps; nine 1s and then b 0s rule out every tail of at most 4⌊(b - 1)/9⌋ + 2](Rule30Open/Columns/WideWall.md) | [`Columns.WideWall`](Rule30Open/Columns/WideWall.lean) | `center_long_run_tail`, `center_black_white_tail`, `long_run_tail_column`, `black_white_tail_column`, `wide_wall_column`, `stripe_agree`, `black_shield` | 1 | extends a kit result |
| [An eventual period of the center column needs T + P of at least 262,125](Rule30Open/Columns/WideWindow.md) | [`Columns.WideWindow`](Rule30Open/Columns/WideWindow.lean) | `runRel_fst`, `runRel_snd`, `center_eq_wide`, `wideFactor_new`, `transient_add_period_ge_262125` | 1 | extends a kit result |
| [Traps for blocks of period 2, 3, 5, 6, 7 and 9, by the kit's labelled-trap check for a block of any period](Rule30Open/Columns/WordTraps.md) | [`Columns.WordTraps`](Rule30Open/Columns/WordTraps.lean) | `wtrap_column`, `center_wtrap`, `absorption_excludes`, `not_eventually_01_of_absorption`, `not_eventually_001_of_absorption_fifteen`, `not_eventually_01111_of_absorption`, `not_eventually_001011_of_absorption`, `not_eventually_0011101_of_absorption`, `not_eventually_001011101_of_absorption` | 1 | extends a kit result |

**Findings**

| Result | Status | Problems | Formalization |
|---|---|---|---|
| [Every right half of up to 20 cells enters the kit's ether-and-wall family](findings/columns/absorption-census.md) | computed | 1 | partial |
| [Every window can reach the period-four certificate, so a fair coin beyond it locks the right half](findings/columns/coin-lock.md) | computed | 1 | partial |
| [Up to period 12, what the exclusions and reductions in Lean reach, period by period](findings/columns/coverage.md) | computed | 1 | not applicable |
| [The finite game excludes 261 of the 22,242 blocks of period 17 and 18](findings/columns/game-blocks-18.md) | computed | 1 | partial |
| [The finite game excludes 508 of the 79,971 blocks of period 19 and 20](findings/columns/game-blocks-20.md) | computed | 1 | partial |
| [The finite game excludes 197 of the 8,800 blocks up to period 16](findings/columns/game-blocks.md) | computed | 1 | partial |
| [No left half of up to 80 cells meets the kit's C3 for a period-four word](findings/columns/left-half-c3.md) | computed | 1 | partial |
| [No small left half meets the left-half statement of any block of period 3, 5, 6, 7 or 9](findings/columns/left-half-every-block.md) | computed | 1 | partial |
| [Locks carried leftward from a few seeds give every locked window of 13 cells up to period 12, both of the kit's traps, and locked windows for a block of every period from 2 to 9](findings/columns/lock-chains.md) | computed | 1 | partial |
| [Driven right halves settle into traps for 27 of the 99 blocks of period 10, 51 of the 186 of period 11 and 75 of the 335 of period 12](findings/columns/natural-traps.md) | computed | 1 | partial |
| [A width-16 window certifies the period-four lock from most starts](findings/columns/period-four-certificate.md) | computed | 1 | partial |
| [The three words of period four lock the right half](findings/columns/period-four-locking.md) | conjecture | 1 | wanted |
| [For 72 blocks of period at most 12, every window of 13 cells can be steered into a lock](findings/columns/steerable-locks.md) | computed | 1 | partial |
| [Every right half of up to ten cells enters the kit's trap for 001, some only after 10^5 steps](findings/columns/t001-census.md) | computed | 1 | partial |

**Negative results**

| Result | Kind | Problems |
|---|---|---|
| [Column words that fix the cell beside the column exclude no block the finite game misses, up to period 20](negative-results/columns/forcing-words.md) | no signal | 1 |
| [Jen's theorem on farther columns, or on periods longer than the block's, does not strengthen the finite game](negative-results/columns/jen-farther-columns.md) | no signal | 1 |
| [Driven by 011, the right half does not settle next to the center](negative-results/columns/period-three-011.md) | no signal | 1 |
| [No row of up to 24 cells has a column that repeats from time 0](negative-results/columns/periodic-from-start.md) | no signal | 1 |
| [Periodic orbits on rings explain the finite game's failure only for the alternating block](negative-results/columns/ring-orbits.md) | no signal | 1 |
| [A search for slow right halves finds no counterexample and misses the slowest halves](negative-results/columns/slow-half-search.md) | no signal | 1 |
| [Right halves driven by blocks of period 5, 6 and 7 almost never enter a trap](negative-results/columns/trap-entry.md) | no signal | 1 |
| [No window of up to 18 cells locks for any block of period 2, 3, 5, 6, 7 or 9](negative-results/columns/window-locks.md) | no signal | 1 |

## Period two

The first open period of Prize Problem 1, reduced to a question about one integer map.

**Proved in Lean**

| Result | Module | Headline theorems | Problems | Kit |
|---|---|---|---|---|
| [The alternating domains time the period-two condition](Rule30Open/PeriodTwo/Domains.md) | [`PeriodTwo.Domains`](Rule30Open/PeriodTwo/Domains.lean) | `held_domains_odd`, `held_countdown`, `held_disagree`, `held_agree_stepB` | 1 | independent proof of a kit result |
| [Period two reduces to an integer map](Rule30Open/PeriodTwo/HeldColumn.md) | [`PeriodTwo.HeldColumn`](Rule30Open/PeriodTwo/HeldColumn.lean) | `period_two_held`, `period_two_integer`, `center_period_two_integer`, `heldNat_testBit` | 1 | independent proof of a kit result |
| [Against a white right half, no left half within depth 32,755 keeps the center alternating](Rule30Open/PeriodTwo/WhiteRightHalf.md) | [`PeriodTwo.WhiteRightHalf`](Rule30Open/PeriodTwo/WhiteRightHalf.lean) | `white_right_leaves`, `psi_empty_gaps`, `leaves_by_gap`, `psiBits_spec` | 1 | extends a kit result |

**Findings**

| Result | Status | Problems | Formalization |
|---|---|---|---|
| [No row with its leftmost 1 within 120 cells has an alternating center](findings/period-two/alternating-within-120.md) | computed | 1 | wanted |
| [Every integer below 2^52 fails the period-two condition, near step 2M](findings/period-two/left-half-alone.md) | computed | 1 | partial |
| [Beside an alternating center the right half nearly locks, and slips](findings/period-two/right-channel.md) | computed | 1 | not applicable |
| [Against a white right half, no left half of fewer than a million cells keeps the center alternating](findings/period-two/white-right-half.md) | computed | 1 | partial |

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
