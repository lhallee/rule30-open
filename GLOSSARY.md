# Glossary

The terms this repository uses without defining them each time, in alphabetical order. Each definition is taken from
the entry or Lean argument linked beside it, which states it in full. Where the repository uses two words for one
thing, the entry names the one to use and notes the other. Names in code font are Lean or Python identifiers, most of
them the kit's.

**Absorption.** The kit's Lean name for entry (`Rule30Ether.Absorption`, `WTrap.Absorption`). In prose, say
entry. See [MissedTraps](Rule30Open/Columns/MissedTraps.md).

**Apart.** Two traps of one block are apart when no state of the one, cut to the narrower width, is a state of the other
whose label reads the same phase. A right half that starts in the one never enters the other, so entry into either alone
is false ([ApartTraps](Rule30Open/Columns/ApartTraps.md)).

**Background.** A configuration of Rule 30 on the whole line in which every column repeats with a period dividing $P$.
Every background is also periodic in space ([space-time backgrounds](findings/columns/space-time-backgrounds.md)).

**Block.** A finite word that a column repeats forever from some time on, with its length as its period. A block is
excluded when no column of a row with a leftmost 1 repeats it from any time and in any rotation
([FiniteGame](Rule30Open/Columns/FiniteGame.md)).

**BWH.** One of the wedge hypotheses on the kit's main branch. It says that for $n \ge 7$ and $c \in \{2, 3\}$ no binary
word $e_0 \dots e_{2n+1}$ over the symbols 1 and 2 has wedge $W_n e(t) = c$ for all $t < n + 2$
([wedge forced runs](findings/period-two/wedge-forced-runs.md)). Here BWH alone implies the kit's `Q01`, and so
excludes an eventual period two ([WedgeLadderQ01](Rule30Open/PeriodTwo/WedgeLadderQ01.md)). See also RW.

**C3.** The kit's `Rule30PeriodFourSkeleton.C3 w`, one statement for each word $w$ of $0001$, $0011$ and $0111$. It says
that no finitely supported left half, run as Rule 30 left of the center with the center replaced by the effective
boundary $c'_w(t) = w(t) \land w(t + 1)$, keeps cell $-1$ equal to a pattern $P_w$ at three of the four phases for all
large times. The three statements together give least period four for the center column
([the kit's C3](findings/columns/left-half-c3.md)).

**Carried trap.** If column $m$ repeats a block and column $m + 1$ reads a trap's values at its white phases, each
column to the left is a function of the two to its right. Putting the $d$ columns between $m - d + 1$ and $m$ in front
of every state of the trap gives a trap $d$ cells wider for the block of column $m - d$, which is the trap carried $d$
columns ([FarWalls](Rule30Open/Columns/FarWalls.md), [lock chains](findings/columns/lock-chains.md)).

**Chain.** For a lock of a block $s$ in column $m$, the blocks that columns $m - 1$, $m - 2$, and so on then repeat,
each determined by the one to its right and the lock's values. The block at distance $d$ has a locked window $d$ cells
wider ([lock chains](findings/columns/lock-chains.md)).

**Driven half.** A right half run under Rule 30 with the center replaced by a given periodic word from a given phase,
the kit's `drv` ([absorption census](findings/columns/absorption-census.md)). The driven left half is the left half as
a function of column 0 alone, from a white start (the kit's `Rule30DrivenLeft`;
[driven left runs](findings/diagonals/driven-left-runs.md)).

**Driver.** A sequence $c(0) = 1, c(1), c(2), \ldots$ put in column 0 to drive the left half. A driver is admissible
when the driven left half allows it, that is when $c(t + 1)$ is the complement of cell $-1$ at time $t$ whenever
$c(t) = 1$. The single cell's center column is admissible ([driver density](findings/diagonals/driver-density.md)).

**Entry.** For a trap of a block, the statement that every finitely supported right half driven by the block, from any
phase, eventually has its first cells in a state of the trap. A trap reduces its block to entry, and the kit and Lean
call it absorption ([MissedTraps](Rule30Open/Columns/MissedTraps.md), [WordTraps](Rule30Open/Columns/WordTraps.md)).

**Ether.** The kit's ether, a Rule 30 orbit with spatial period 7 and temporal period 4 (`Rule30Ether.ether_rule`),
whose columns repeat $B_1 B_2 B_3 B_4 B_5\,c\,c$. It is the background that the kit's wall ends in
([EtherDomain](Rule30Open/Columns/EtherDomain.md), [absorption census](findings/columns/absorption-census.md)).

**Ether-and-wall family.** The set of states of a right half driven by $0001$, $0011$ or $0111$ that the driven rule
never leaves and on which masked Jen gives a contradiction. A half is in it (`InFamily`) when, for one of the kit's
alignments, columns 1 to $k$ are ether columns ending in a $B_3$ and columns $k + 1$ to $k + 13$ are a wall state at the
same phase. The kit's `Absorption` is entry into it, and `least_period_four_of_absorption` turns that into least period
four ([absorption census](findings/columns/absorption-census.md)). The repository also calls it the kit's family and
the ether family, and ether-and-wall family is the term to use.

**Finite game.** If a column repeats a block, the cells right of it are driven by a known periodic input and learn of
the cells far to the right only through one unknown cell per step. Treating that cell as an adversary gives a finite
game, and a certificate that every play makes the column on the left eventually periodic excludes the block by Jen's
theorem ([FiniteGame](Rule30Open/Columns/FiniteGame.md)).

**Gap trap.** Beside an alternating center, a closed set of windows of columns 1 to 16 on which the black cells of
column 1, at the white steps of the center, come 3 or 5 white steps apart. It is the setting of the kit's open
`Q01Gap` ([gate census](findings/period-two/gate-census.md)).

**Headline theorem.** A theorem that a Lean module's argument lists under `headline` in its front matter, whose
axioms `python scripts/catalog.py audit` checks ([CONTRIBUTING.md](CONTRIBUTING.md)).

**Held column, `held`.** `held` is Rule 30 on the cells left of a column held at 0
([KickedForm](Rule30Open/Columns/KickedForm.md)). Whatever a column reads, the cells left of it follow `held` except for
a flip of the cell next to it when the column reads 1 at two consecutive steps. On integers, with bit $j$ the cell
$j + 1$ places left of the column, `held` is the held map $H(U) = (U \gg 1) \oplus (U \lor (U \ll 1))$, and a center
column that ends in period two gives some $U > 0$ with $H^{2s+1}(U)$ odd for every $s \ge 0$
([HeldColumn](Rule30Open/PeriodTwo/HeldColumn.md)).

**Jen's theorem.** No two adjacent columns of a row with a leftmost 1 are both eventually periodic. Most exclusions in
this repository end by reducing to it ([AdjacentColumns](Rule30Open/Columns/AdjacentColumns.md)).

**K.** The set of 2-adic integers $U$ with $H^t(U)$ odd at every odd $t$, for the held map $H$. The period-two question
is whether $K$ contains a positive integer ([the shift model](findings/period-two/shift-model.md)).

**Kit.** The Rule 30 Prize kit, [Rule30PrizeKit](https://github.com/WolframInstitute/Rule30PrizeKit), which fixes the
prize's formal statements in Lean 4 and collects partial results. This repository depends on it at a pinned commit
([README.md](README.md), [lakefile.toml](lakefile.toml)).

**Left diagonal.** $D_j(t) = a_t(j - t)$, diagonal $j$ of the pattern counted from the left edge $D_0$, the kit's
`Rule30Diagonals.D` ([LeftMemory](Rule30Open/Diagonals/LeftMemory.md)).

**Lock, locked window.** Let column $k$ repeat a block. A window of the cells right of column $k$, at a phase of the
block, is locked when along every continuation, whatever the cell beyond the window does, column $k - 1$ reads one value
at each phase. Jen's theorem forbids a locked window in the true row, so a locked window is a trap
([window locks](negative-results/columns/window-locks.md), [lock chains](findings/columns/lock-chains.md)). The two
words mean the same thing.

**Natural trap.** A trap found where a sampled driven right half settles, as the closure of its window under both values
of the cell beyond ([natural traps](findings/columns/natural-traps.md)).

**Onset.** The onset of a left diagonal is the least time from which it repeats
([seed-uniform onsets](findings/diagonals/seed-uniform-onsets.md)).

**Q01.** The pinned kit's `Rule30PeriodTwo.Q01`. It says that no start of the zero-driven left half (Rule 30 on the
columns left of 0, with column 0 held white) whose leftmost black cell is at $-m$, $m \ge 1$, keeps column $-1$ black at
every even step. It excludes an eventual period two (`not_eventually_period_two_of_Q01`;
[WedgeLadderQ01](Rule30Open/PeriodTwo/WedgeLadderQ01.md)).

**Q01Right(W).** The statement that no finitely supported left half absorbs a word of the exact right channel of $W$
columns beside an alternating center. For every $W \ge 1$ it excludes an eventual period two of the center column with
no hypothesis on where the right half goes, and the kit's `Q01` implies it
([ChannelLanguage](Rule30Open/PeriodTwo/ChannelLanguage.md)).

**(R).** Every rational 2-adic number in $K$ has an eventually periodic itinerary
([the shift model](findings/period-two/shift-model.md)).

**RW.** The rotated form of BWH on the kit's main branch, with a hard-core guard (no 1 after a 1 from position
$n$), lengths $2n + r + 2$ for $r \le 2$, and two fixed symbols. `BWH` with `SmallRW` excludes an eventual period two,
and [WedgeSmall](Rule30Open/PeriodTwo/WedgeSmall.md) proves `SmallRW`
([wedge forced runs](findings/period-two/wedge-forced-runs.md)).

**Seed.** The word has three uses, each fixed by its context. The category [seeds](CATALOG.md#seeds) is about initial
rows that give exactly the center column of the single black cell ([categories.yaml](categories.yaml)), and the seed's
past is the rows that lead to the single cell ([the seed's past](findings/frames/seed-past.md)). Among the left
diagonals, a seed is a row white left of a black cell, with any cells right of it
([seed-uniform onsets](findings/diagonals/seed-uniform-onsets.md)). Among locks, a seed is a block with a bottom
component of its game in which column 1 is not a function of the phase, the start of a chain
([lock chains](findings/columns/lock-chains.md)).

**Stripe.** The alternating background. With white and the kit's ether it is one of the three kinds of background
under whose edge the column was eventually periodic, among the rows white on the right with a period word of up to 9
cells and a prefix of up to 2 ([periodic backgrounds](findings/frames/periodic-backgrounds.md)).

**Stripe relation.** The kit's `StripeRelated x y B` between rows, from its `Rule30StripeMeeting`. Related rows have the
same center column (`stripe_related_same_trace`), and the relation is entered at time 0 or 1 if at all
([center classes](findings/frames/center-classes.md), [StripeClassCount](Rule30Open/Frames/StripeClassCount.md)).

**Test of reach.** Entry into a trap fails when some node of a finite game cannot reach the trap, since the nodes that
cannot reach it form a set that no move leaves. The test checks this in games of a given width
([MissedTraps](Rule30Open/Columns/MissedTraps.md)).

**Trap.** For a block, a set of states of the cells next to a column that repeats it, each a window with a time label
modulo a multiple of the period, that the rule never leaves whatever the cell beyond does, and on which the cell beside
the column is a function of the label at the white phases. A trap reduces its block to entry
([WordTraps](Rule30Open/Columns/WordTraps.md)).

**Wall.** In the kit, the strongly connected component with no move out of the greatest closed set of 13-cell strips
right of a $B_3$ column of the ether, the kit's `wallStates`. A wall state follows the ether in the ether-and-wall
family ([absorption census](findings/columns/absorption-census.md)). The trap modules also call a trap found at the edge
of a background a wall ([FarWalls](Rule30Open/Columns/FarWalls.md),
[space-time backgrounds](findings/columns/space-time-backgrounds.md)).

**White phase, white step.** A white phase of a block $b$ is a phase $q$ with $b_q = 0$
([ReadingWords](Rule30Open/Columns/ReadingWords.md)). Beside an alternating center that is black at the even steps, the
white steps are the odd times ([ChannelLanguage](Rule30Open/PeriodTwo/ChannelLanguage.md)).

**Window.** The $W$ cells right of a column that repeats a block, taken at a phase of the block
([window locks](negative-results/columns/window-locks.md)).
