# Open pull requests to the prize kit

The kit ([Rule30PrizeKit](https://github.com/WolframInstitute/Rule30PrizeKit)) is pinned here at its main branch, commit
932cf8d, so a module merged there is a kit result. On October 30, 2026 the kit merged eleven of its open [pull
requests](https://github.com/WolframInstitute/Rule30PrizeKit/pulls) into its main branch: nine at commit
[a6399ef](https://github.com/WolframInstitute/Rule30PrizeKit/commit/a6399ef15ff409d4dc0c5feb119b289aa31588a4), with 168
modules, and #50 and #58 after them, at commit
[7beff71](https://github.com/WolframInstitute/Rule30PrizeKit/commit/7beff71ceb40e67010fd0713b1a9aecdded09ef2), which
brings its catalog to 170 modules. The eleven are #36, #43, #45, #46, #49, #50, #51, #53, #54, #56 and #58, each marked
*merged* below. Thirteen more followed, #17, #59 and #61 to #71, each in a commit of its own (#17 at
[da21aa7](https://github.com/WolframInstitute/Rule30PrizeKit/commit/da21aa7), #71 at
[d41defd](https://github.com/WolframInstitute/Rule30PrizeKit/commit/d41defd)), and the main branch at
[a09f245](https://github.com/WolframInstitute/Rule30PrizeKit/commit/a09f245) had 184 modules. On November 1, 2026 (UTC)
seven more were merged, #72, #73, #74, #77, #78, #75 and #76 (#72 at
[f218d11](https://github.com/WolframInstitute/Rule30PrizeKit/commit/f218d11), #76 at
[cd5466b](https://github.com/WolframInstitute/Rule30PrizeKit/commit/cd5466b)), and the main branch at
[27060a7](https://github.com/WolframInstitute/Rule30PrizeKit/commit/27060a7) has 193 modules, 52 more than the pin; its
equivalent forms (`equivalents/`) have not changed since the pin. Thirteen pull requests were open after these merges:
#23, #33, #38, #39, #40, #41, #47, #48, #52, #55, #57, #60 and #79, the last opened that day. None of the seven merged
on November 1 excludes a block unconditionally (#75 and #76 exclude period two only under open hypotheses), so the
block counts of [what the main branch covers here](#what-the-main-branch-covers-here) are those of a09f245. Four earlier
pull requests were closed without their
modules reaching the main branch: #3 (`Rule30WordExclusions`), #5 (`Rule30Sparse16`), #29
(`Rule30PeriodThirtyTwoShielding`) and #32 (`Rule30XorCollision`, `Rule30XorSharpness`). Two more reached the kit before
the pin in other modules: the tail-13 completion of #15 is the pinned `Rule30ZeroBoundaryStripeFourComplete` with
`Rule30Certificates/StripeTail13Completion`, and the single-cell and high-support absorption of #20 is the pinned
`Rule30EtherSingleCell`, while its two-cell absorption (`Rule30EtherTwoCell`) is in neither. These six are not
summarized below. This repository is not yet pinned there, so here the merged ones are results of the kit's main branch
that the pin does not include; the summaries below that say "claims" were written from the pull request pages before the
merge, and the merged modules state what they claim. The pull requests still open are claims. Each pull request adds
Lean modules that its author reports as checked by the kit's `Check.lean`. The summaries below come from the pull
request pages and from the module sources at each pull request's head (`refs/pull/N/head`), and they are grouped by the
routes of [the roadmap](../ROADMAP.md). [What the main branch covers here](#what-the-main-branch-covers-here) lists the
entries here whose results the main branch now proves in part.

## Least periods four and three: traps for the right half

- **#17, `Rule30CoupledEmptyRight` and `Rule30ParametricStripCertificates`.** *Merged* (da21aa7). Claims that no finite configuration
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

- **#65, `Rule30Ether.Lock` and `Rule30EtherWallWitness`.** *Merged* (d2a091e). Claims a hypothesis weaker than `Absorption`, `Lock w`:
  every finitely supported right half driven by $w$ has column 1 eventually periodic at the white times, or some column
  eventually periodic. For the kit's alignments `Absorption` implies it (`lock_of_absorption`), and it still excludes
  $w$ for every transient (`lock_excludes`), so the locks of $0001$, $0011$ and $0111$ would exclude least period four
  (`least_period_four_of_lock`). It also glues the ether, of spatial period 7, as a left half to a finite right half so
  that the center repeats $w$ from time 0, for the three words and for the alternating one
  (`period_four_left_periodic_right_finite`, `alt_left_periodic_right_finite`), so a proof has to use the finiteness of
  the left half. `Lock` is stated open for the three words. *Here:* entry into any trap of the trap modules, or into one
  of a set of them ([TrapPairs](../Rule30Open/Columns/TrapPairs.md)), implies the block's lock, so `Lock` is the weakest
  hypothesis of the kind the trap modules reduce blocks to; a refuted trap does not refute it, since the closed set that
  refutes a trap can be a lock itself ([what failed](../negative-results/columns/missed-traps.md)). For $001$ that is
  what happens: the kit's `AbsorptionT t001` is false, refuted by a second trap for $001$, and so is entry into one of
  any three of four traps for $001$ pairwise apart, while `Lock` for $001$ stands
  ([Traps001](../Rule30Open/Columns/Traps001.md)).

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
- **#64, `Rule30GateTrap`.** A closed set of 829 windows of 16 cells for the gate of the right half driven by the
  alternating column, under the double step, inside which the black cells of column 1 come 3 or 5 double steps apart;
  the white half enters it at time 293. Claims that a new statement `Q01Gap`, implied by the kit's `Q01`
  (`Q01Gap_of_Q01`), gives `CQ01Empty` (`CQ01Empty_of_Q01Gap`). `Q01Gap` is stated open, and 96% of a sample of random
  finite right halves enter the set, which is not proved. Merged (2d7e9c4), after the commit pinned here. *Here:* the
  white right half's gate is the object of [WhiteRightHalf](../Rule30Open/PeriodTwo/WhiteRightHalf.md); every right half
  of up to 20 cells enters the gap trap (computed as the greatest such set, which holds the 829 windows), the kit's
  ether family or a lock of period seven ([the census](../findings/period-two/gate-census.md),
  [SevenLock](../Rule30Open/PeriodTwo/SevenLock.md)).
- **#66, `Q01_iff_integer`.** *Merged* (01677a0). Restates `Q01` as: every natural number reaches an even number under some iterate of
  $G = F \circ F$, with $F(Y) = (Y \gg 1) \oplus (Y \lor (Y \ll 1))$. *Here:* this is the map $H$ of [the held
  column](../Rule30Open/PeriodTwo/HeldColumn.md), where period two needs some $U > 0$ with $H^{2s+1}(U)$ odd for every
  $s$, and no integer below $2^{52}$ has that property ([the left half alone](../findings/period-two/left-half-alone.md)).
- **#67, `Rule30ZeroBoundaryPeriodLanes`.** *Merged* (276d92c). States `QP P` for every $P$: no start of the zero-driven left half with a
  leftmost black cell keeps column $-1$ black at every $P$th step. Claims that it excludes $(0^{P-1}1)^\infty$ for
  every transient (`not_eventuallyWord_oneBlack_of_QP`), that `QP 2` is the kit's `Q01` and `QP 3` its `Q001`, that
  `QP 4` gives the kit's `C3` for $0001$, and a bit-sliced checker for bounded starts (`qP_of_chunks`); `QP P` is
  stated open for every $P \ge 2$. *Here:* [LeftLatch](../Rule30Open/Columns/LeftLatch.md) states one condition of
  the same kind for every block of every period.
- **#75, `Rule30AlternatingTraceBridge`, `Rule30SurvivalBridge` and `Rule30P2Bridge`.** *Merged* (a498c23);
  credited to D. Condrey. A nonzero finite row whose center satisfies $c(t + 2) = c(t) \ne c(t + 1)$ from time 0
  gives an auxiliary frontier, a finite word over four symbols read from two adjacent anti-diagonals, that passes
  every guard (`immortalFromAlternating`), so that mortality of the frontier would give the kit's `Q01`
  (`Q01_of_mortality`) and exclude an eventual period two of the single cell's center
  (`center_not_eventually_period_two_of_mortality`); a repeat budget is the same as
  mortality (`budget_iff_mortality`); and, for every Boolean sequence, four restatements of density $1/2$ by dyadic
  shell maxima and block energies (`problem2_iff_shellMaxLittleO` and three more), with a sequence showing that the
  weaker hypotheses do not suffice. Mortality is stated open, as is every bound on these quantities for the center
  column. Its control `alternatingCenter_without_finiteSupport` is the row of spatial period 7 with center
  $0101\cdots$, the ether that #65 glues to a finite right half.
- **#76, `Rule30SEPToPeriodTwo` and three more modules.** *Merged* (cd5466b); credited to D. Condrey. Three open
  hypotheses on streams over four symbols, `BWH`, `RW` and `SEP` (no stream with a long binary prefix has a long
  constant wedge, its rotated form, and an orbit separator), are related (`bwh_implies_rw`, which also needs
  `SmallRW`, the six cases of `RW` below length 7; `separator_equivalence`), and each of `SEP`, `RW`, and `BWH` with
  `SmallRW` excludes a nonconstant center of period two from time 0 on every nonzero finite row
  (`sep_implies_period_two`, `rw_implies_period_two`, `bwh_small_implies_period_two`). None of the hypotheses is
  proved in the kit; `SmallRW` is proved here ([WedgeSmall](../Rule30Open/PeriodTwo/WedgeSmall.md)), so the route of
  `BWH` needs only `BWH`, which holds for $7 \le n \le 31$ by search ([forced
  runs](../findings/period-two/wedge-forced-runs.md)). These read the row's right half as well (`actual_endpoint_hardcore`), and the module states no implication
  in either direction between them and `Q01` or mortality. *Here, for #75 and #76:* they add open statements, each
  proved to exclude a center of period two, beside the kit's `Q01`, the gap statement `Q01Gap` of #64 and the integer
  form of #66. The frontier of #75 is read from the left half that the center rebuilds, the open object of [the white
  right half](../findings/period-two/white-right-half.md) and [the held column](../Rule30Open/PeriodTwo/HeldColumn.md);
  the hypotheses of #76 are, by the kit's account, of no known order of strength against it. The Problem 2 forms hold
  for every sequence, as the kit's catalogued restatements do, and bound nothing about the center column.
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

- **#58, `Rule30GroupCocycle`.** *Merged.* Claims that every homogeneous one-step, local, group-valued zero-curvature
  connection for Rule 30 is a local vertex gauge of two commuting vacuum constants, for any group, finite or not,
  commutative or not, with the spatial and temporal supports placed independently (`arbitrary_local_supports`); it says
  that it proves no prize problem. *Here:* it extends [the conservation
  laws](../negative-results/structure/conservation-laws.md) from additive quantities on blocks to ordered transport in
  any group: Rule 30 carries no local invariant of either kind beyond the trivial ones, so neither kind constrains the
  density of Problem 2.

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
- **#61, `Rule30EdgeClock` and `Rule30DefectClockBudget`.** *Merged* (a5ad97f). In the frame of the right edge, for any infinite code with
  a black edge and any starting time, claims that every positive digit $j$ changes within $\lceil j/2 \rceil$ updates,
  sharp at the single cell, and that a first difference at digit $j + 1$ escapes into digit $j + 3$ or $j + 4$ within
  $\lceil j/2 \rceil + 2$ updates, and into $j + 5$ or $j + 6$ within $7(\lceil j/2 \rceil + 1)$, recurrently. The
  pull request reports a partial replay by `Check.lean` and states that neither module proves escape at every width
  or that the center column is not periodic.
- **#62, `Rule30GateClocks`.** *Merged* (6246dcf). Replaces the OR of the right-edge map with any two-input gate at each depth and claims,
  for every choice of gates, that the least period of the first $n$ bits of the edge code is a power of two
  (`prefix_period_iff`), that $2m$ more bits raise its exponent by at most $m$ plus a correction from earlier records
  (`prefix_window_bound`), so the first $n$ bits have a period dividing $2^{B(n)}$, and that with affine gates the
  period divides $2^r$ once $n + 1 \le 2^r$ (`affine_prefix_bound`). It extends the kit's half-rate bound
  `Rule30RightPeriods.per_upper_half` from the OR to every gate, and claims no lower bound.
- **#69, `Rule30EtherGrounding`.** *Merged* (0d1c95e). In the frame of the rightmost black cell, claims that the one-in-four ether cannot
  eventually hold two adjacent columns at fixed distances behind the edge, for every row, depth, spatial and temporal
  phase and starting time, without a common temporal period (`no_moving_ether_pair`, carried through the edge map
  `Rule30FrozenRuler.edge_evol`): a property of the pair closed under going back is carried by a checked local step to
  the edge, whose constant black column contradicts it; `ether_step` checks that the two-sided ether exists. It states
  alternating tails, rigidity at one edge in general and Problem 1 as open. *Here:* the counterpart at the right edge,
  for one pattern, of the rigidity of two adjacent columns at the left edge
  ([AdjacentColumns](../Rule30Open/Columns/AdjacentColumns.md)); the trap modules here need the ether beside the center
  column, not behind the edge.
- **#50, `Rule30TemporalProfiles`.** *Merged.* Claims facts on periodic profiles linked by the left-diagonal
  recurrence: a periodic driver has exactly one periodic child, and a chain of them that starts white returns to white
  within $2^{2q}$ links.
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
- **#59, `Rule30ZeroBoundaryStripePrimitiveRoots`.** *Merged* (9f903cb). Builds on #45: explicit backward operators for the two-step map of
  the stripe front windows, a trichotomy for the preimages of a window (a clone regime with a white tail, and two
  primitive regimes, with a black tail or with the period-3 NOR wave $(100)^\infty$, `primitive_or_clone_trichotomy`,
  `backward_nor_period_three`), a classification of the primitive roots of 8 cells, and projections of the orbits of
  wider windows onto narrower ones. It states no claim on a prize problem.
- **#63, `Rule30ZeroBoundaryStripeCascade`.** *Merged* (cad25c9). Builds on #45 and #59: every primitive root of the first kind reaches the
  NOR wave $(100)^\infty$ at backward step 3, the next step maps it to $(011)^\infty$ and the one after to
  $(000101)^\infty$ (`typeI_step3_nor_wave`, `wave_011_to_period6_step0`); the backward reduction is injective, so
  clone rays from distinct primitive roots never meet (`clone_ray_disjoint_of_primRoot`); and each of sixteen infinite
  clone rays turns its first cell white at an even time at most $m + 45$ (`rowTail_sixteen_rays_all_odd`). It reports a
  partial claim. *Here:* no route here uses the stripe front windows.
- **#74, `Rule30ZeroBoundaryStripeCascade` extended.** *Merged* (5b186b7). Adds to #63 a synchronization of the
  complement waves through the word $010$ (`sync_010_complement_step1`), a period doubling to 6 of the NOR wave under
  two backward steps (`nor_wave_B_shift_period6`), the cascade for the primitive roots of the second kind
  (`typeII_step3_and_step4_cascade`), period-3 waves in the low bits of the windows `win3pow n` at backward steps 3
  and 4, for every $n$ (`bstep1_B_shift_win3pow_low_wave`, `B_shiftIter_two_win3pow_low_wave`), and a shift by 3 of
  these bits from `win3pow (2 + 3m)` to `win3pow 2` = 13 (`B_shiftIter_two_win3pow_mod3_shift_13`). It states no claim
  on a prize problem. *Here:* as for #63.
- **#79, `Rule30ZeroBoundaryStripeCascade` extended again.** Open; its commit is by G.P.J.W. Quint. Claims that the word
  $010$ in a window makes both backward steps forget the bits below it, so that a tail of period $L$ above $010$ keeps
  period $L$ (`bstep1_congr_of_010`, `bstep1_periodic_of_010`); that a tail of period $L \ge 2$ above $00$ gets period
  $2L$ (`bstep1_periodic_two_mul_of_00`); and that every tail of period $L$ gets period $6L$ under one backward step
  (`bstep1_periodic_six_mul`), by collapsing the backward step to a transducer on pairs of bits. *Here:* as for #63.
- **#23, `Rule30RunBoundarySources`.** Claims that the center at time $2^{e+1} - 1$ is 1 plus, modulo 2, the
  contribution of run-boundary sources at depths beyond $e$, from an expansion through Rule 90. *Here:* it is of the same kind as
  [the Duhamel form](../findings/structure/duhamel.md), which writes the center column as a sum over adjacent black
  pairs.
- *Here, for the group:* no route of the roadmap uses these yet. The right-diagonal results describe the regular part of
  a finite pattern near its right edge, while every open case of Problem 1 here turns on the chaotic part near the
  center.

## Left diagonals

- **#73, `Rule30LeftAntiPeriod`.** *Merged* (1e22121); credited to G.P.J.W. Quint and Gemini. The parity of $L$
  consecutive cells of a sequence of period $L$ is eventually constant (`par_const_of_periodic`), so when $D_j$ has
  eventual period $L$ and $D_{j+1}$ is eventually white, $D_{j+2}$ is eventually $L$-periodic or $L$-anti-periodic,
  $D_{j+2}(t + L) = \lnot D_{j+2}(t)$ (`D_period_or_antiperiodic`); an eventually anti-periodic sequence has $L$ black
  cells in every $2L$ consecutive cells after its transient, so density $1/2$ (`halfDensity_of_antiperiodic`); and with
  the unbounded periods of `Rule30LeftUnbounded`, for every $N$ some left diagonal $D_j$, $j > N$, is eventually
  $2^k$-anti-periodic, not $2^k$-periodic, and of density $1/2$ (`D_infinitely_many_halfDensity`). *Here:* these are
  `windowParity_periodic` and the second case of `D_period_dichotomy` of
  [LeftMemory](../Rule30Open/Diagonals/LeftMemory.md) ([below](#what-the-main-branch-covers-here)). The density
  statement is the form of Problem 2 for a sequence that is eventually periodic, where it reduces to counting one
  period; it says nothing about the center column, which is not a left diagonal.
- **#78, `Rule30LeftAntiPeriod` extended.** *Merged* (fba0ae7); credited to G.P.J.W. Quint and Gemini. $D_m$ and
  $D_{m+1}$ have a common eventual period $Q$ exactly when every $D_i$, $i \le m + 1$, has it (`D_evPer_pair_iff_all`),
  by the left-permutive backward step; local laws behind an eventually white diagonal (`D_white_prev_three`,
  `D_post_white_complement`, `D_post_white_no11`); twin anti-periodic diagonals of density $1/2$
  (`D_twin_antiperiodic_of_not_evPer`); the bound that $D_j$ eventually repeats with period $2^{\lfloor(j+5)/6\rfloor}$
  (`D_evPer_pow_div_six`), from the white spacing of #46; and for every $k$ a right diagonal $R_j$, $k < j < 2^{k+1}$,
  that is $2^k$-anti-periodic from time 0 and so of density $1/2$ (`R_infinitely_many_halfDensity`). *Here:* the period
  bound is exponential in $j$ and says nothing about when a diagonal starts to repeat, so it does not bear on [linear
  settling](../findings/diagonals/settled-runs.md), which asks an onset at most $3j/2$ with a period $o(j)$.

## Counts over all rows

- **#77, `Rule30WedgeParity`.** *Merged* (8aefaf6); credited to D. Condrey with Claude. For every left-permutive
  elementary rule $a \oplus g(b, c)$, $g = \gamma \oplus \alpha b \oplus \beta c \oplus \kappa bc$, counts the rows of a
  window of $2n + 1$ cells with a fixed far-left cell, a fixed boundary diagonal on the right and center cell 1 at time
  $n$, by the free word that left-permutivity reconstructs them from (`adm_eq_Y`, `rowOf_adm`), and proves the count
  odd exactly when $\alpha \oplus r = 1$ if $\kappa = 1$ (`wedge_parity_quadratic`), and even from $n = 2$ if
  $\kappa = 0$ (`wedge_parity_affine`); for Rule 30 with white boundary the count, OEIS A400898, is odd for every $n$
  (`rule30_wedge_odd`). The module says that the counts are over all initial rows, so nothing follows for the single
  cell. *Here:* a statement about every row, of the kind [the random-row
  barrier](../negative-results/random-rows/almost-every-row.md) separates from the single cell. The reconstruction is
  the left-permutive step by which a right half and a center column fix the one left half that could carry them, the
  object of [the white right half](../findings/period-two/white-right-half.md).

## Runs of the center column

- **#66, `Rule30BlackRuns`, self-shielded.** *Merged* (01677a0). Sharper forms of the kit's Theorems B and D on the
  black runs of an eventual period: a black run of $9j$ leaves $(01)^j$ in columns 1 to $2j$, which moves right without
  reading the cells beyond and keeps column 1 fixed by the center for $4j$ steps. So a period of $P$ cannot hold a black
  run of $r < P$ followed by a white cell once $9 \lceil (P - r)/4 \rceil \le r$ (`no_long_black_run_quarter`), nor a
  black run of $s \ge 9$, then exactly $r$ white cells and a black cell, with $s + r < P$, once
  $1 + 9 \lfloor (P - s - r + 1)/4 \rfloor \le r$ (`no_black_white_run_quarter`); a word $1^r u$ with $u$ starting white
  is excluded for $r \ge 9$ when $1 \le |u| \le 4$ (`no_black_run_ge9_len_le4`) and for $r \ge 18$ when $|u| \le 8$
  (`no_black_run_ge18_len_le8`). Both conditions are those of
  [WideWall](../Rule30Open/Columns/WideWall.md) for the center column ([below](#what-the-main-branch-covers-here)).
  *Here:* [WallSegments](../Rule30Open/Columns/WallSegments.md)
  and [WideWall](../Rule30Open/Columns/WideWall.md) use runs of nine 1s the same way, through the cells beside the
  column.
- **#46, `Rule30BlackRunErosion`, `Rule30WhiteSpacing` and five more modules.** *Merged.* Claims that a black run of
  length $L$ starting at time $a \ge 16$ satisfies $5L + 18\,\ell(a) \le 3a + 51$ and a white run starting at $a \ge
  256$ satisfies $L + 6\,\ell(a) \le a + 17$, with $\ell(a) = \lfloor \log_2 \log_2 a \rfloor$; the slope $3/5$ is
  credited to the earlier prize submission R30-20261025-0554f7. *Here:* the roadmap's run bounds for Problem 2; a bound
  linear in $a$ gives no positive density.

## The cost of the center cell

- **#68, `Rule30Problem3Bounds`.** Claims, for a deterministic one-tape Turing machine started with its head on cell 0,
  that a run of $t$ steps reads only cells $0, \dots, t - 1$ of the input (`run_eq_of_init_eq_lt`), so a machine that
  computes a function within $k$ steps on an input $n \ge 2^{k-1}$ gives the function the same value at every
  $n + u\,2^k$ (`computes_const_on_dyadic_ray`); with Problem 1, any machine computing the center column takes more than
  $k$ steps on inputs beyond every bound, for every $k$ (`time_unbounded_of_problem1`), and without it, by a computation
  of the first 99 rows, at least $k + 1$ steps on every input $n \ge 2^{k-1}$ for $k \le 4$ and $\log_2 n + 2$ steps for
  $n < 16$ (`log2_succ_succ_le_time_lt_16`). A reviewer's comment proposes the unconditional form for $k \le 13$, not
  yet in the pull request. *Here:* bounds of the order of the input's length, for one model, against the linear bound
  Problem 3 asks; [the barrier](../negative-results/complexity/problem-three-barrier.md) says why the gap is the whole
  problem, and the converse direction, Problem 3 implying Problem 1, is in the kit's equivalent forms. The matching
  upper bound in the same model, a machine that computes the center column in $2n^2 + 2n\ell + O(n)$ steps, is
  [the quadratic-time machine](../Rule30Open/Complexity/QuadraticTime.md).
  *Merged* (aff827e), with the reviewer's form `time_unbounded_le_thirteen`: for every $k \le 13$ every such machine
  takes at least $k + 1$ steps on infinitely many inputs.
- **#70, `Rule30Problem3Bounds` extended.** *Merged* (1053be2). Time at most $k$ on the $2^k$ inputs of the window
  $[2^{k-1}, 2^{k-1} + 2^k)$ already makes the function $2^k$-periodic from $2^{k-1}$ on
  (`period_of_canon_window_time_le`), and for every $k$ some left diagonal needs $k + 1$ steps on some input of that
  window (`diagonal_canon_window_time_ge`). *Here:* for the center column one pair $m \ge 2^{k-1}$ with
  $c(m) \ne c(m + 2^k)$ per $k$ suffices; [restricted models](../negative-results/complexity/restricted-models.md)
  finds the least such pair for $k \le 20$, always within the first six inputs of the window.
- **#72, `Rule30Problem3Bounds`, right-head span.** *Merged* (f218d11). The results of #68 and #70 with the time bound
  replaced by a bound on how far right the head goes: if the head stays below cell $k$ on an input $n \ge 2^{k-1}$,
  every $m \ge 2^{k-1}$ with $m \equiv n \pmod{2^k}$ gets the same value (`computes_eq_of_mod_two_pow_of_scansBelow`); a
  head that eventually stays below cell $k$ forces period $2^k$ from $2^{k-1}$ on (`period_of_eventually_scansBelow`);
  so with Problem 1 every machine computing the center column reaches cell $k$ on inputs beyond every bound
  (`head_unbounded_of_problem1`), and some left diagonal makes every machine reach cell $k$ on the window
  $[2^{k-1}, 2^{k-1} + 2^k)$ (`diagonal_canon_window_head_ge`). The span is at most the time (`rightSpan_le_steps`). A
  head that stays below cell $k$ on the $2^k$ inputs of the window also makes the machine halt on every $m \ge 2^{k-1}$
  within the time it takes on the representative of $m$ in the window, with the same configuration on the cells $i < k$
  at every step (`period_and_halt_of_canon_window_scansBelow`, `run_congr_canonRep_of_canon_window_scansBelow`). *Here:*
  the head must read $k$ input cells to tell residues apart modulo $2^k$, a bound of the order of the input's length, as
  in #68; it does not approach the linear bound Problem 3 asks ([the
  barrier](../negative-results/complexity/problem-three-barrier.md)).
- **#71, `Rule30EtherEpisode`.** *Merged* (d41defd). In the frame of the rightmost black cell, the longest run of
  ticks for which two adjacent depths of a black-edge code follow the one-in-four ether has an exact length,
  $\lfloor 2k/3 \rfloor + 4 - [k \equiv 0, 2 \pmod 6]$ (`episode_max`), a quantitative form of #69. *Here:* no
  route uses the edge frame.

## What the main branch covers here

The entries here state their relation to the kit at the pinned commit. The main branch proves part of what some of them
mark as new or as a refinement.

- **Blocks of period at most 21.** Of the primitive blocks of period at most 21, 133 are excluded by a family that the
  main branch adds and not by the pinned kit: one each of periods 11, 12 and 13, then 11, 14, 15, 15, 15, 16, 20 and 24
  of periods 14 to 21 ([computations/kit_main.py](../computations/kit_main.py), which reads each family's statement as
  a test on the block). The families are the self-shielded Theorems B and D of #66 (68 blocks), the black-run families
  $1^r u$ of #17 (`not_eventually_paramBlackTable`, 60), the new white-padding bounds of `Rule30PaddedWords.no_padded_word`
  for the tails $1011$, $10011$, $11011$, $101111$ (from 9 white cells), $1101$ (11), $1111$ (7) and $1^k$, $k \ge 3$
  (17) (42), the four-category grammar of #36 (14) and the white runs of at least 17 of #36 (3); 53 blocks fall in more
  than one. The reset mixtures of #43 add no block of period at most 21: their blocks there, $1\,0^q$ with $q \ge 17$,
  are the pinned kit's padded words. Every one of the 133 is already excluded
  in Lean here, by a module whose entry is marked `kit: new`: 14 of the 32 blocks of
  [GameBlocks](../Rule30Open/Columns/GameBlocks.md), 29 of the 97 of
  [GameBlocksLong](../Rule30Open/Columns/GameBlocksLong.md), and 15 of the 99 of
  [BitBlocks17](../Rule30Open/Columns/BitBlocks17.md), 15 of the 122 of
  [BitBlocks18](../Rule30Open/Columns/BitBlocks18.md), 16 of the 133 of
  [BitBlocks19](../Rule30Open/Columns/BitBlocks19.md), 17 of the 160 of
  [BitBlocks20](../Rule30Open/Columns/BitBlocks20.md), 2 of the 55 of
  [BitBlocks20Mid](../Rule30Open/Columns/BitBlocks20Mid.md), 1 of the 44 of
  [BitBlocks20Wide](../Rule30Open/Columns/BitBlocks20Wide.md), 21 of the 220 of
  [BitBlocks21](../Rule30Open/Columns/BitBlocks21.md), 2 of the 97 of
  [BitBlocks21Mid](../Rule30Open/Columns/BitBlocks21Mid.md) and 1 of the 62 of
  [BitBlocks21Wide](../Rule30Open/Columns/BitBlocks21Wide.md). The block $01110111111111$ of period 14 also has traps in
  [FourteenTraps](../Rule30Open/Columns/FourteenTraps.md), [NaturalTrapsWalls](../Rule30Open/Columns/NaturalTrapsWalls.md)
  and [ApartTraps](../Rule30Open/Columns/ApartTraps.md). So the main branch adds no block of period at most 21 to those
  that the kit and this repository exclude together; it changes which of them the kit excludes. The block lists here
  come from the literals of each module's Lean source and from the trap and steering reductions of
  [computations/coverage.py](../computations/coverage.py); a block that a module states in another form would be
  missed.
- **[WideWall](../Rule30Open/Columns/WideWall.md)** (`kit: refines`). Its statements 1 and 2 for the center column of
  the single cell are `no_long_black_run_quarter` and `no_black_white_run_quarter` of #66: $9 \lceil x/4 \rceil \le r$
  exactly when $x \le 4 \lfloor r/9 \rfloor$, and $1 + 9 \lfloor (m + 1)/4 \rfloor \le b$ exactly when
  $m \le 4 \lfloor (b - 1)/9 \rfloor + 2$. The kit's forms ask a tail $x \ge 1$ or $m \ge 1$ ending the run, where WideWall
  allows $x = 0$ and $m = 0$; those words, $1^P$ and $1^s 0^b$ with $s \ge 9$, are excluded by the pinned kit's
  theorem on runs of at least nine 1s. Its forms for every column of every row with a leftmost 1
  (`long_run_tail_column`, `black_white_tail_column`, `wide_wall_column`) are not in the kit.
- **[LeftMemory](../Rule30Open/Diagonals/LeftMemory.md)** (`kit: refines`). `Rule30LeftReset` proves its reset
  (`D_period_after_reset`, the same statement as `D_periodic_of_black`), the first half of its dichotomy
  (`D_period_or_white`: the next diagonal has the period, or the middle one is white), the doubling
  (`D_white_double`) and the parity criterion (`D_white_period_iff`), for the single cell's left diagonals, and
  `Rule30LeftAntiPeriod` (#73) proves its constant window parity (`par_const_of_periodic`, as `windowParity_periodic`)
  and the anti-periodic case of its dichotomy (`D_period_or_antiperiodic`).
- **Unbounded left-diagonal periods.** [SettledRuns](../Rule30Open/Diagonals/SettledRuns.md) and [the driven run
  slopes](../negative-results/diagonals/driven-run-slopes.md) cite Nersissian (2026) for them; `Rule30LeftUnbounded`
  proves them in Lean (`D_period_unbounded`, `D_least_period_unbounded`), with infinitely many eventually white left
  diagonals (`D_infinitely_many_white`) and never two adjacent ones (`D_no_two_white`).
- **Not covered.** `Rule30Ether.Lock` of #65 is an open hypothesis on every finitely supported right half, so it does not
  cover [LockWord](../Rule30Open/Columns/LockWord.md) or [LockBlocks](../Rule30Open/Columns/LockBlocks.md), which prove
  for one sequence of one column that the center does not repeat the block once the column reads it; "lock" means
  different things there. [DrivenSkeleton](../Rule30Open/Diagonals/DrivenSkeleton.md) compares the diagonals of two
  configurations, which no module of the main branch does; [QuadraticTime](../Rule30Open/Complexity/QuadraticTime.md) is
  an upper bound, where `Rule30Problem3Bounds` gives lower ones; `Rule30CoupledEmptyRight` of #17 is the white right
  half of [EmptyRight](../Rule30Open/Columns/EmptyRight.md), which also covers every right half of at most six cells.
  The period-two entries [SevenLock](../Rule30Open/PeriodTwo/SevenLock.md),
  [EtherCensus](../Rule30Open/PeriodTwo/EtherCensus.md), [NoKTails](../Rule30Open/PeriodTwo/NoKTails.md) and
  [BoundedLag](../Rule30Open/PeriodTwo/BoundedLag.md) meet `Rule30GateTrap`, `Q01_iff_integer` and
  `Rule30ZeroBoundaryPeriodLanes` in their objects, the gate of the alternating-driven right half and the held map;
  those modules prove reductions to open statements (`Q01Gap`, `QP P`) and a restatement, not the census, the lock of
  period seven, the tails or the lag of these entries.
