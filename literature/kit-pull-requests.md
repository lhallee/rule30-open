# Open pull requests to the prize kit

The kit ([Rule30PrizeKit](https://github.com/WolframInstitute/Rule30PrizeKit)) is pinned here at its main branch, commit
932cf8d, so a module merged there is a kit result. On October 30, 2026 the kit merged nine of its 23 open [pull
requests](https://github.com/WolframInstitute/Rule30PrizeKit/pulls) into its main branch, at commit
[a6399ef](https://github.com/WolframInstitute/Rule30PrizeKit/commit/a6399ef15ff409d4dc0c5feb119b289aa31588a4), which
brings its catalog to 168 modules: #36, #43, #45, #46, #49, #51, #53, #54 and #56, each marked *merged* below. This
repository is not yet pinned there, so here they are results of the kit's main branch that the pin does not include, and
the 17 open, with #61 since, are claims. Each pull request adds Lean modules that its author reports as checked by the
kit's `Check.lean`. The summaries below come from the pull request pages and from the module sources at each pull
request's head (`refs/pull/N/head`), and they are grouped by the routes of [the roadmap](../ROADMAP.md).

## Least periods four and three: traps for the right half

- **#17, `Rule30CoupledEmptyRight` and `Rule30ParametricStripCertificates`.** Claims that no finite configuration
  whose right half is white has a center column repeating $0001$, $0011$, $0111$ or $001$, in any phase
  (`no_empty_right_coupled_0001` and the others), and a checker that excludes a whole family $a^r u$, $r \ge r_0$,
  with one strip certificate (`not_eventually_param_word`), which lowers several black-run thresholds of the kit.
  *Here:* the white right half for the same four words is `emptyRight_*` of
  [EmptyRight](../Rule30Open/Columns/EmptyRight.md), which also covers every right half of at most six cells, and
  [WhiteGap](../Rule30Open/Columns/WhiteGap.md) extends it to halves with a white gap.
- **#40, `Rule30TrapPeriod21` and `Rule30PeriodicHalfline`.** Claims that a right half that has entered the kit's trap
  `t001` for the word $001$ cannot have temporal period 21 in every column, and that the adjacent-pair values at any two
  columns of the trap differ at arbitrarily late times. *Here:* exclusion through `t001` needs only entry
  ([EmptyRight](../Rule30Open/Columns/EmptyRight.md), `emptyRight_001`); this concerns the trap's interior.

## Period two

- **#39, `Rule30EmptyAlternating`.** Claims `not_absorption_alt`: the white right half driven by an alternating
  center never enters the ether-and-wall family, for any list of genuine alignments, so the kit's `Absorption` is
  false for the alternating word. The proof combines a kernel-checked invariant (black gate gaps of three or five after
  cycle 146) with a symbolic argument that excludes gate period two. *Here:* it proves that
  [the period-two absorption route](../negative-results/period-two/absorption-route.md) fails, which that entry finds by
  computation: the white half stays out for 20,000 steps.
- **#47 and #52, gate pasts.** The gate is column 1 at the white times of the right half driven by the alternating
  column, from which the kit's `Rule30PeriodTwoSideways` reconstructs the one left row that could keep the center
  alternating. Claims that two legal gate pasts of three to seven bits that share an arbitrary infinite future agree
  beyond a computed depth, the same for every past length along two periodic families of futures, and a conditional
  reduction (`Rule30GateTailReduction`): closing for every past length would leave no finite row of the gate class.
  Closing for every length is stated as open. *Here:* the same left row is the object of
  [the white right half](../findings/period-two/white-right-half.md) and [the held column](../Rule30Open/PeriodTwo/HeldColumn.md);
  no finite certificate in the forms tried settles it ([no certificate](../negative-results/period-two/no-finite-certificate.md)).
- **#60, inverse-cascade closing.** Claims that row closing at every depth reduces to closing finite blocks
  (`physical_block_closes`), and that one staircase cutoff merges every competing inverse stack of any finite height for
  every infinite reference row with recurrent resets, words $0\,1^{3k+1}\,0\,b$ (`exists_reset_schedule`,
  `scheduled_cascade_closes`), with a counterexample when the resets stop. Whether the legal gate rows have recurrent
  resets is stated as open, and the pull request says that no prize problem is proved. *Here:* it extends #47 and #52
  from periodic futures to any future with recurrent resets; the open step is the same left row as in [the white right
  half](../findings/period-two/white-right-half.md).
- **#53, `Rule30ResetFreeThree` and four more modules.** *Merged.* Claims that every nonzero finite row of the kit's
  zero-boundary evolution, beside a column held white, contains a word $0\,1^{3m+1}\,0$ in one of its first three rows,
  with two rows not enough, and that a tail avoiding these words for five rows is eventually of period five. *Here:* no
  route here uses it.

## Births and mismatch budgets

- **#38, `Rule30PhysicalDefects`.** Claims that if the single cell's center column had period $P$ from time $T$, every
  $2P + 1$ consecutive values of column 1 after $T + 2P$ would include one equal to the value $2P$ steps earlier
  (`bounded_mismatch_episode`), and that padded doubling blocks contain at least $2m - 1$ distinct mismatch births
  before $4^m n_0$. An upper budget of births that would contradict this is stated, not proved.
- **#41, `Rule30LocalBirthPotential` and two more modules.** Claims that a column-2 mismatch interval supports at most
  two column-1 births, an orbit with infinite support whose births recur every six steps, and that no integer potential
  of a bounded window pays every birth beside a locally alternating center. *Here:* the last is a negative result of
  the kind of [the conservation laws](../negative-results/structure/conservation-laws.md): a local accounting of the
  pattern does not close.

## Local invariants

- **#58, `Rule30GroupCocycle`.** Claims that every homogeneous one-step, local, group-valued zero-curvature connection
  for Rule 30 is a local vertex gauge of two commuting vacuum constants, for any group, finite or not, commutative or
  not, with the spatial and temporal supports placed independently (`arbitrary_local_supports`); it says that it proves
  no prize problem. *Here:* if correct, it extends [the conservation laws](../negative-results/structure/conservation-laws.md)
  from additive quantities on blocks to ordered transport in any group: Rule 30 carries no local invariant of either
  kind beyond the trivial ones, so neither kind constrains the density of Problem 2.

## Excluding eventual periods by families of blocks

- **#36, `Rule30White17Runs` and `Rule30GrammarRuns`.** *Merged.* Claims that the single cell's center column is not
  eventually a repetition of any word $1^{r_1} 0^{q_1} \cdots 1^{r_k} 0^{q_k}$ with every $q_i \ge 17$, nor of one whose
  blocks fall in four categories ($r = 1, q \ge 10$; $r = 2, q \ge 8$; $r = 4, q \ge 7$; $r \ge 9, q \ge 9$), whatever
  the number of blocks and the transient. The method ranks the strip of fourteen cells right of the center: the blocks
  capture every strip into an envelope of 683 strips (1,791 for the four categories), no block raises the rank, and a
  block that keeps it fixes column 1 along its white run, which masked Jen forbids.
- **#43, `Rule30ResetMixtures`.** *Merged.* Claims the same for repetitions of blocks $1\,0^q$ with every gap at least
  nine and one at least 17.
- *Here:* [the game blocks](../findings/columns/game-blocks.md) exclude single repeating blocks of period at most 14,
  one certificate each; these families exclude unboundedly long words at once, provided their white runs are long.
  Neither reaches the words of least period four, whose white runs are at most three.

## Structure near the edges and of periodic profiles

- **#51, #54 and #55, right diagonals.** *#51 and #54 merged, #55 open.* On the diagonals $D_j(t) = x_t(t - j)$ counted
  from the right edge of a finite seed, claims a shift law for the doubling of their periods (`shift_law`) and a
  universal start: if $m \ge 2$ is the first index, counted left from the seed's rightmost black cell, where two
  adjacent seed cells agree, then $D_{m+1}, \dots, D_{m+6}$ have least periods 4, 8, 8, 16, 32 and 32
  (`universal_start`). With #55, the whole-prefix clock reaches at least 64 by diagonal $m + 15$, sharp for the seed
  47649.
- **#48, `Rule30EdgeClockDrop`.** Claims restrictions on how temporal periods of edge columns can drop, and finite
  observations that imitate a drop for bounded time.
- **#61, `Rule30EdgeClock` and `Rule30DefectClockBudget`.** In the frame of the right edge, for any infinite code with
  a black edge and any starting time, claims that every positive digit $j$ changes within $\lceil j/2 \rceil$ updates,
  sharp at the single cell, and that a first difference at digit $j + 1$ escapes into digit $j + 3$ or $j + 4$ within
  $\lceil j/2 \rceil + 2$ updates, and into $j + 5$ or $j + 6$ within $7(\lceil j/2 \rceil + 1)$, recurrently. The
  pull request reports a partial replay by `Check.lean` and states that neither module proves escape at every width
  or that the center column is not periodic.
- **#50, `Rule30TemporalProfiles`.** Claims facts on periodic profiles linked by the left-diagonal recurrence: a
  periodic driver has exactly one periodic child, and a chain of them that starts white returns to white within
  $2^{2q}$ links.
- **#49, `Rule30PairedColumnRuns`.** *Merged.* Claims that when columns 0 and 1 both have period $P \ge 2$ from time 0
  and column 0 is black at some time, every white run left of column 0 in row 0 has length at most $2P - 2$; the
  hypotheses fail whenever there is a leftmost black cell. *Here:*
  [AdjacentColumns](../Rule30Open/Columns/AdjacentColumns.md) proves the hypotheses impossible with a leftmost black
  cell.
- **#56, `Rule30RingOrbits`.** *Merged.* Claims that spatially periodic configurations that return to themselves after
  $P$ steps shifted by $P$ cells correspond to closed walks of temporal profiles, and that for $P = 2$ these are only
  the white and alternating ones. *Here:* [ring orbits](../negative-results/columns/ring-orbits.md) takes the orbits
  that return without a shift, on rings of up to 25 cells, as witnesses against the finite game; they witness only the
  block $01$.
- **#57, `Rule30DrivenMaskTransport`.** Claims that, for any driving column and any start, the left half evolves the
  same beside the column and beside the kit's effective boundary exactly when cell $-1$ is black at every 1 of the
  column that a 0 follows (`transport_iff_falling`, `consistency_iff`), and that an exclusion of periodic masks would
  imply Problem 1 (`problem1_of_periodic_mask_exclusion`, a conditional; no period is excluded). *Here:* in a true
  orbit that condition always holds, since left of a 1 followed by a 0 the cell is 1
  ([KickedForm](../Rule30Open/Columns/KickedForm.md), `left_kicked_check`); it is why the left half follows one map with
  kicks only at two consecutive 1s.
- **#33, `Rule30FiniteReturnEight`.** Claims that a finite state of the kit's triangular evolution returns to itself
  after eight steps exactly when it returns after two once its three newest cells are dropped.
- **#45, `Rule30ZeroBoundaryStripeStructure`.** *Merged.* Claims structure for the front windows of the kit's
  zero-boundary stripes: a two-step clone map, lifting of certified cycles to wider windows, and a backward dichotomy.
- **#59, `Rule30ZeroBoundaryStripePrimitiveRoots`.** Builds on #45: explicit backward operators for the two-step map of
  the stripe front windows, a trichotomy for the preimages of a window (a clone regime with a white tail, and two
  primitive regimes, with a black tail or with the period-3 NOR wave $(100)^\infty$, `primitive_or_clone_trichotomy`,
  `backward_nor_period_three`), a classification of the primitive roots of 8 cells, and projections of the orbits of
  wider windows onto narrower ones. It states no claim on a prize problem. *Here:* no route here uses the stripe front
  windows.
- **#23, `Rule30RunBoundarySources`.** Claims that the center at time $2^{e+1} - 1$ is 1 plus, modulo 2, the
  contribution of run-boundary sources at depths beyond $e$, from an expansion through Rule 90. *Here:* it is of the same kind as
  [the Duhamel form](../findings/structure/duhamel.md), which writes the center column as a sum over adjacent black
  pairs.
- *Here, for the group:* no route of the roadmap uses these yet. The right-diagonal results describe the regular part of
  a finite pattern near its right edge, while every open case of Problem 1 here turns on the chaotic part near the
  center.

## Runs of the center column

- **#46, `Rule30BlackRunErosion`, `Rule30WhiteSpacing` and five more modules.** *Merged.* Claims that a black run of
  length $L$ starting at time $a \ge 16$ satisfies $5L + 18\,\ell(a) \le 3a + 51$ and a white run starting at $a \ge
  256$ satisfies $L + 6\,\ell(a) \le a + 17$, with $\ell(a) = \lfloor \log_2 \log_2 a \rfloor$; the slope $3/5$ is
  credited to the earlier prize submission R30-20261025-0554f7. *Here:* the roadmap's run bounds for Problem 2; a bound
  linear in $a$ gives no positive density.
