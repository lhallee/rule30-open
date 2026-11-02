# Roadmap

Where each route toward the three problems stands, which routes look promising, and what to do next.
[CATALOG.md](CATALOG.md) lists every result by category; this page groups them by route. A status says what is
known: **closed** (a negative result records where the route stops and why), **open** (partial results and no known
obstruction), **lead** (open, with a concrete next step). The order of the leads, and every sentence marked
*assessment*, is a judgment rather than a result.

The kit's own status table, in its
[lean/README.md](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/README.md#status-by-period),
summarizes the formal frontier of Problem 1, and agents add to the kit every day
([the literature](literature/rule-30.md#work-on-the-prize-problems-since-2019)). This repository is pinned at the
kit's commit 932cf8d; the kit's main branch has since gained 52 modules (27060a7, November 1), which exclude 133 blocks of
period at most 21 that this repository's Lean already excludes and no block that it does not; its new period-two theorems
each take an open hypothesis (mortality, an orbit separator, RW, or BWH with SmallRW)
([kit pull requests](literature/kit-pull-requests.md)), and moving the pin there, after the build, the audit and the tests pass, is pending.

## At a glance

| Problem | Route | Status | Where it stands |
|---|---|---|---|
| 1 | Rigidity from the left edge | closed on its own | no two adjacent columns are eventually periodic; Rules 90, 150 and 210 share every fact it uses |
| 1 | Excluding eventual periods block by block | open | the finite game excludes 1,400 blocks of period at most 21, all in Lean, and reaches no block of period 2, 3, 5, 6, 7 or 9 |
| 1 | Single blocks through traps | open | 16 of the 56 blocks of period 9, 23 of the 99 of period 10, 53 of the 186 of period 11, 96 of the 335 of period 12, 176 of the 630 of period 13, 334 of the 1,161 of period 14 and 612 of the 2,182 of period 15 come down to entry into some trap of the block, with a trap that every window of 20 cells can reach, in Lean, from walls at the edges of backgrounds periodic in time and space, all of which are known to period 14 and six of period 15, from the closed sets that driven right halves settle into, every block of periods 10 to 14 that a sampled half settles into a trap for (at 13 and 14 with windows of 16 cells), and from every locked window of 16 cells at periods 10 to 15, carried by its chain; for one block each of period 10, 11 and 12 every right half white past its first eight cells, to a bound of 1,610 to 3,058, enters, in Lean, and for two blocks of period 9 every right half white on its first $10^5$ cells or so enters from most phases; one block each of period 5 and 7 has a trap that passes the tests but that small halves almost never enter, and the four traps of the one block of period 6, which share their first 22 cells, fail the test in the game of 22 cells, and none of its windows of up to 22 cells is locked; entry into 360 other traps alone, most of them carried along a background's columns, is false, 184 of them in Lean, among them 48 natural traps that pass the test of reach but that a wider trap of their block is apart from, and the only trap of period 5, and 90 blocks need entry into one of several traps |
| 1 | Least period four through the right half's lock | lead | every right half of up to 20 cells enters the kit's family by computation, up to 14 cells in Lean; open for the rest |
| 1 | Least period four through the left half | open | no left half of up to 80 cells meets the kit's `C3`; depth 88 in Lean |
| 1 | Every period through the left half | open | one statement per block (`LeftLatch`); no left half of up to 37 to 100 cells meets it at the lock-free periods |
| 1 | Period two through the held column | open, hard | a map with the shape of a Collatz problem; every integer below $2^{63}$ fails; the condition is a full 2-shift (Lean), whose rational points are preperiodic when the tail is a stripe (the kit) and in every case tried; on the ether no window at the top of a defect bounds it, with or without the condition (Lean, in part); every right half of up to 20 cells enters the kit's gap trap, where the kit's open `Q01Gap` decides it, or the kit's ether family or a new lock of period seven, which exclude it outright (the lock in Lean) |
| 1 | Least period three | open | $001$ through entry into one of four traps or into some trap, since entry into the kit's alone, or into one of any three, is false (Lean), $011$ through the left half |
| 1 | 2-adic frames and exact reformulations | closed as tried | every form stops at a statement about the chaotic region |
| 1 | Random rows and probabilistic arguments | closed | true for almost every row, silent on the single cell |
| 1 | Counterexamples | no signal for the problem | no small row has a periodic column; no right half found escapes the period-four lock; but 360 trap reductions here had false hypotheses, a closed set of windows apart from each trap, from the finite game, from where sampled halves settle or from another trap of the block, and so does the kit's own reduction of $001$ to its trap `t001` |
| 2 | Invariant measures and random rows | closed | exact for random rows only |
| 2 | Conservation laws | closed | none over four steps |
| 2 | Bounds on runs | open | runs at most linear in their start time |
| 2 | Statistics | no signal | the column passes every test tried |
| 3 | An upper bound | proved in Lean | a one-tape machine of the kit's model computes $c(n)$ in $2n^2 + 2n \log_2 n + O(n)$ steps, so Problem 3 is the question whether the exponent 2 can fall to 1 |
| 3 | A lower bound | closed with present methods | it amounts to an exponential lower bound for one explicit function |
| 3 | A space lower bound | open, as hard | space $O(\sqrt{n \log n})$ suffices; needing more than order $\sqrt{n}$ would give the kit's Problem 3 |
| 3 | A shortcut | no signal | automata, recurrences and learned predictors find none |
| 3 | Restricted models | open | no automaton below 131,070 states on the range searched |

## Problem 1: is the center column eventually periodic?

- **Rigidity from the left edge.** *Closed as a route on its own; every other route ends with it.* Two adjacent
  columns are never both eventually periodic, and no column is eventually constant
  ([AdjacentColumns](Rule30Open/Columns/AdjacentColumns.md)). More generally, an eventually periodic column and any
  sequence that, with the cells between, closes the strip to its right are never both eventually periodic: the center
  column and column 1 xor column 2, or the parity of columns 1 to $k$ for any $k$, in Lean
  ([ClosingObservable](Rule30Open/Columns/ClosingObservable.md)). The kit proves that Rules 90, 150 and 210 share every
  fact this argument uses and have eventually constant center columns, so it cannot imply Problem 1 alone.
- **Excluding eventual periods block by block.** *Open.* Each block needs its own certificate outside a few families,
  and the share of blocks covered falls with the period. [The coverage](findings/columns/coverage.md) counts, period by
  period up to 15, the blocks excluded, reduced to entry into a trap that passes the two tests entry needs, reduced by
  steering, or not reached: at periods 5 to 7 one block each is reached, and from period 9 about a quarter to three
  tenths have traps that pass.
  - *Excluded.* Finite games, strip certificates and padding families exclude 197 of the 8,800 blocks of period at most
    16, all 136 beyond the kit in Lean ([game blocks](findings/columns/game-blocks.md),
    [BitGame](Rule30Open/Columns/BitGame.md)), 261 of the 22,242 of period 17 and 18, 508 of the 79,971 of period 19 and
    20 and 434 of the 99,858 of period 21, all in Lean, those that need 13 or 14 cells one phase at a time ([periods 17
    and 18](findings/columns/game-blocks-18.md), [periods 19 and 20](findings/columns/game-blocks-20.md), [period
    21](findings/columns/game-blocks-21.md), [BitPhases](Rule30Open/Columns/BitPhases.md)); the game with cyclic
    classes at 16 cells excludes $000000001011$, of period 12, in Lean through a certificate of local checks that
    holds for any block ([class game](findings/columns/class-game.md), [ClassGame](Rule30Open/Columns/ClassGame.md)), and ten blocks of
    period 13 to 16, eight of period 17 and fifteen of period 18 (at 16 cells) that nothing else excludes (for periods 17 and 18 the counts include the blocks that the plain game also closes), all in Lean, the ten largest certificates of period 18 each checked over two or three modules
    ([ClassBlocks18Split](Rule30Open/Columns/ClassBlocks18Split.md), [class
    blocks](findings/columns/class-blocks.md), [ClassBlocks](Rule30Open/Columns/ClassBlocks.md) and the modules it
    links); the plain game at 15 and 16 cells closes three more blocks of periods 14 to 16, in Lean
    ([GameBlocksWide](Rule30Open/Columns/GameBlocksWide.md)); the kit excludes every
    $1\,0^q$ with $q \ge 9$ and every block followed by exponentially many white cells. After nine 1s, following the
    cells beside the column extends the kit's long black runs to every period whose runs of nine or more 1s are
    separated by segments that the possible windows of three cells follow: exactly the 77 blocks with nine 1s in a row
    of period at most 16 that the game excludes, 616 blocks up to period 22, and families such as $1^a 0^b 1 0$, $1^a 0
    1 1 0^c$ and $1^a 0^{2k+3} 1 0 0$ for every $a \ge 9$ ([WallSegments](Rule30Open/Columns/WallSegments.md),
    [WallSets](Rule30Open/Columns/WallSets.md)). A run of $r \ge 9$ 1s rules out every tail of at most $4 \lfloor r/9
    \rfloor$ steps, and nine 1s and then $b$ 0s every tail of at most $4 \lfloor (b - 1)/9 \rfloor + 2$ steps
    ([WideWall](Rule30Open/Columns/WideWall.md)). Any eventual period needs $T + P \ge 262{,}125$ ([a window of 262,144
    cells](Rule30Open/Columns/WideWindow.md); 65,518 from 65,536 cells in
    [LongWindow](Rule30Open/Columns/LongWindow.md), where the kit has 16,359). The kit's main branch, since October 30
    and after the commit this repository is pinned at, excludes every eventual period whose white runs are all at least
    17, and four more families with long white runs ([the kit's pull
    requests](literature/kit-pull-requests.md#excluding-eventual-periods-by-families-of-blocks)). Windows of 14 cells
    followed through the column's whole history, the limit of the windows that any history leaves, exclude 1,672 blocks
    of period at most 22 and infinite families with white runs: every tail of at most six cells but $10101$ after a white
    run of at least 22, against 74 in the kit, by computation, Lean pending ([limit
    windows](findings/columns/limit-windows.md)); up to period 21 they add no block to the game's list, and no white run
    is a wall, so the kit's threshold of 17 for mixed black runs drops only to 16 ([window
    thresholds](negative-results/columns/window-thresholds.md)).
  - *Where it stops.* The share of blocks the game excludes falls from 2.7% at period 12 to 0.56% at period 20, and
    every exclusion rests on a run of five or more equal values; most blocks do not lock the right half
    ([locking](findings/columns/period-four-locking.md)); column words that fix the cell beside the column without a
    long run exclude no block the game misses up to period 20 ([forcing
    words](negative-results/columns/forcing-words.md)). No block of period 2, 3, 5, 6, 7 or 9 has a locked window of up
    to 20 cells ([window locks](negative-results/columns/window-locks.md)). The Conley index of the window graphs, taken as
    the class of the relation's matrix over GF(2), excludes no block ([Conley index](negative-results/columns/conley-index.md)). Wider ones exist for one block or more of
    each of these periods, the locks of seeds with long runs of 1s carried leftward through columns the rule determines
    ([lock chains](findings/columns/lock-chains.md)), and six are traps in Lean that reduce $01$, $001$, $01111$,
    $001011$, $0011101$ and $001011101$ to entry ([WordTraps](Rule30Open/Columns/WordTraps.md)). Period 9 has a wall of
    its own, a lock of 43 cells of $001011111$ that right halves it drives enter, and carried leftward it gives traps to
    21 of the 56 blocks of period 9, and a second wall, of 41 cells with the phase counted modulo 27, gives one to
    $001010011$ ([NineTraps](Rule30Open/Columns/NineTraps.md)). Period 10 has a background of spatial period 155 whose
    edge, a lock of 16 cells of $0000010001$, every right half of up to eight cells enters within 3,042 steps; its
    columns give traps to 25 blocks of period 10 that the kit does not exclude
    ([TenTraps](Rule30Open/Columns/TenTraps.md)), and at periods 10 to 12 about a quarter of the blocks have traps that
    random halves enter ([natural traps](findings/columns/natural-traps.md)); walls of periods 11 and 12 give traps to
    57 and 83 more blocks ([ElevenTraps](Rule30Open/Columns/ElevenTraps.md),
    [TwelveTraps](Rule30Open/Columns/TwelveTraps.md)), and the closed sets that sampled halves settle into give traps to
    the 35 other blocks of periods 10 to 12 that one settles into and that nothing excludes, 30 of them entered by every
    right half of up to four cells ([NaturalTraps](Rule30Open/Columns/NaturalTraps.md),
    [NaturalTrapsLarge](Rule30Open/Columns/NaturalTrapsLarge.md)), and walls of periods 13 and 14 give traps to the 53
    and 101 blocks of those periods among the columns of their backgrounds
    ([ThirteenTraps](Rule30Open/Columns/ThirteenTraps.md), [FourteenTraps](Rule30Open/Columns/FourteenTraps.md)), and
    the closed sets themselves to 74 more ([NaturalTrapsLong](Rule30Open/Columns/NaturalTrapsLong.md)); for
    $0000010001$, $00000011011$ and $001011100111$ no finite configuration white on cells 9 to 3,058, 1,610 or 2,357 has
    a center repeating the block ([TenGap](Rule30Open/Columns/TenGap.md), [WallGaps](Rule30Open/Columns/WallGaps.md));
    the left half reaches every block, as statements only (below).
  - *Conditional.* For 49 blocks of period 4 to 12 that nothing excludes, 16 of them without a run of more than four,
    one sequence of values in column 14 leads every window of 13 cells into a lock, so once the center repeats the
    block, column 14 never reads that sequence (in Lean, [LockBlocks](Rule30Open/Columns/LockBlocks.md) for any block
    and its instances) and, by computation, has entropy below one bit per step ([steerable
    locks](findings/columns/steerable-locks.md)); for 22 of them a white run in one column suffices, as short as 27
    cells in column 8 ([LockWhite](Rule30Open/Columns/LockWhite.md)).
- **Least period four through the right half's lock.** *Lead.* Masked Jen excludes the three words of period four once
  every finite right half enters the kit's ether-and-wall family, the kit's open `Absorption`. Known: every right half
  of up to 20 cells enters ([the census](findings/columns/absorption-census.md)); every half white on columns 1 to 30
  enters (the kit for $0001$, [WhiteGap](Rule30Open/Columns/WhiteGap.md) for all three words); in Lean, halves of up to
  fourteen cells enter ([EmptyRight](Rule30Open/Columns/EmptyRight.md) for six,
  [TenCells](Rule30Open/Columns/TenCells.md) for ten, [TwelveCells](Rule30Open/Columns/TwelveCells.md) for twelve,
  [FourteenCells](Rule30Open/Columns/FourteenCells.md) for fourteen), so does every half white on columns 7 to $B$,
  whatever lies beyond, with $B$ = 316, 535 and 310 ([WhiteGap](Rule30Open/Columns/WhiteGap.md)), every half white on
  columns 11 to $G'$, with $G'$ = 562, 654 and 371 ([TenCells](Rule30Open/Columns/TenCells.md)), and every half white on
  columns 13 to 750, 995 and 560 ([TwelveCells](Rule30Open/Columns/TwelveCells.md)) and every half white on columns 15
  to 750, 1,446 and 560 ([FourteenCells](Rule30Open/Columns/FourteenCells.md)), and so does every half with at most two
  black cells among columns 1 to $G$, whatever lies beyond, with $G$ = 778, 1,359 and 623, which includes one black cell
  anywhere ([SparseRight](Rule30Open/Columns/SparseRight.md); the kit has one cell for $0001$), and so does every
  truncation of the aligned ether, one of the two infinite halves known to stay out with the half beside a $0001$ column
  of the background of 80 cells, whose truncations enter after 2.5 steps per cell
  ([background halves](findings/columns/background-halves.md)), followed by at most six cells
  ([EtherPrefix](Rule30Open/Columns/EtherPrefix.md) for four, [EtherPrefixSix](Rule30Open/Columns/EtherPrefixSix.md) for
  six); a window of 16 columns has a certificate ([the certificate](findings/columns/period-four-certificate.md)), in
  Lean a trap ([PeriodFourCertificate](Rule30Open/Columns/PeriodFourCertificate.md)), every window can reach it, and one
  word of a few hundred values in column 17 forces entry ([the coin lock](findings/columns/coin-lock.md)); in Lean, one
  sequence of 1,193, 955 or 381 values in column 17, 15 or 14 brings every window into the family, so a center that
  repeats the word keeps that column off the sequence forever ([LockWord](Rule30Open/Columns/LockWord.md)). No set of
  windows of up to 26 cells that no move leaves misses the family, nor one of up to 26 cells the kit's `t001` for $001$
  ([reach of the kit's conjectures](findings/columns/kit-absorption-reach.md)): the test that refutes entry into seven
  traps of periods 13 to 15 ([MissedTraps](Rule30Open/Columns/MissedTraps.md)) finds nothing against either at those
  widths. A set of 52 cells misses `t001`: the second trap for $001$, so the kit's `AbsorptionT t001` is false
  ([Traps001](Rule30Open/Columns/Traps001.md)). Under $0001$ every right half reads column 1 as $0^a 1^{4-a}$ on
  each block of four steps, along a graph of 13 transitions, and a repeated value 2 or 3 forces the aligned ether up to
  its first $B_3$ column ([column-one blocks](findings/columns/column-one-blocks.md)). For a uniformly random infinite
  half the law at each time is exact, uniform on a set of measure $2^{-t}$; almost every infinite half enters exactly
  when entry has a uniform positive chance after every prefix, which is open, and for $0001$ a half stays out for $T$
  steps with chance at least $2^{-(T + 20)}$ ([random halves](findings/columns/random-halves.md)). Open: attraction for
  halves with at least three black cells among the
  first $G$ columns, one of them among columns 1 to 30, one among columns 7 to $B$, one among columns 11 to $G'$ and one
  among columns 15 to 750, 1,446 and 560, beyond the census's 20 cells. *Assessment:* the most direct route to a full
  case of Problem 1, though attraction asks the chaotic part of the right half to deliver an entry pattern, a statement
  of the same kind as the problem.
- **Least period four through the left half.** *Open.* The kit's other reduction of period four asks that no finite left
  half keep column $-1$ on a pattern with one free reading in four (`C3`, one statement for each word). No left half of
  up to 80 cells does, for each word in each phase ([the left-half statements](findings/columns/left-half-c3.md)), and
  Lean checks, for each word, every half that lies within depth 88 at the time it starts to keep the pattern
  ([LeftHalf0001](Rule30Open/Columns/LeftHalf0001.md) with the kit's lane checker,
  [LeftHalfDriven](Rule30Open/Columns/LeftHalfDriven.md) with the checker extended to a boundary that is not white).
  *Assessment:* the latest failure outlasts the half's length by about a third of it, and the work of a check doubles
  with every four cells, so checks settle bounded cases only; a proof needs an argument that uses the finiteness of the
  half.
- **Every period through the left half.** *Open.* One statement for each block of each period, `LeftLatch b`, rules the
  block out in the orbit of every row with a leftmost 1: no finite left half, kicked where the block reads 1 twice in a
  row, meets the check at each 1 with a cell right of the column that latches
  ([LeftLatch](Rule30Open/Columns/LeftLatch.md)). It reaches the periods 3, 5, 6, 7 and 9 that no window lock of up to
  20 cells reaches, and for each of their 91 blocks no left half of at most 37 to 100 cells meets it ([every
  block](findings/columns/left-half-every-block.md)). *Assessment:* each statement is of the kind of period two and of
  `C3`; past the half's length the readings fail at the rate of fair coins, so computation settles bounded cases only,
  and only the black block is proved.
- **Period two through the held column.** *Open, hard.* It reduces to an integer map with the shape of a Collatz problem
  ([HeldColumn](Rule30Open/PeriodTwo/HeldColumn.md)); every integer below $2^{52}$ fails ([left half
  alone](findings/period-two/left-half-alone.md)), the kit proves its Q01 for starts of width at most 52, against the
  white right half no left half within depth 32,754 keeps the center alternating, in Lean
  ([WhiteRightHalf](Rule30Open/PeriodTwo/WhiteRightHalf.md), the kit's milestone `CQ01Empty` for those widths), and no
  finite certificate exists in the forms tried ([no certificate](negative-results/period-two/no-finite-certificate.md)).
  The ether-and-wall family cannot give period two: the white right half never enters it, by computation here ([the
  absorption route](negative-results/period-two/absorption-route.md)) and by a Lean proof claimed in the kit's pull
  request #39, and about half the windows of 19 or 20 columns cannot enter it whatever the next column does. Other pull
  requests work on the gate, from which the kit reconstructs the one candidate left row ([the kit's pull
  requests](literature/kit-pull-requests.md#period-two)). The 2-adic integers that keep the center alternating form the
  one-sided full 2-shift under two steps of the map; its periodic points are domains periodic in space, so a positive
  integer in it would have an itinerary that is never periodic, so the conjecture (R) that every rational point is
  preperiodic would settle period two ([the shift model](findings/period-two/shift-model.md)). (R) holds for every
  rational whose tail falls onto a stripe, since a defect can climb past a stripe by at most one cell, which the kit
  proves in its own encoding (`Rule30ZeroBoundaryStripe.stripe_absorb`); every rational
  point with a head and period of at most 64 cells together, 2,592 of them, is preperiodic and falls onto a stripe or
  the ether, and no integer below $2^{63}$ is a point, by computation; what remains is to bound a defect in front of the
  ether. Beyond the stripes and the ether, every background that a periodic tail of up to 12 cells reaches
  carries fronts on which the tops of most defects run away, provably on 10 of the 12, so there (R) can hold only because
  $K$ misses those tails; no head of up to 16 cells on them is in $K$, each breaking it by step 47, in Lean on all twelve, through the tree of
  $K$, which runs $2^{h/2}$ of the $2^h$ heads of $h$ cells ([NoKTails16](Rule30Open/PeriodTwo/NoKTails16.md),
  [NoKTails](Rule30Open/PeriodTwo/NoKTails.md), [the tail census](findings/period-two/tail-census.md), [front backgrounds](negative-results/period-two/front-backgrounds.md)). Every head of up to 20 cells on the ether settles, entering a closed strip of 13 cells or repeating within 24
  cells of the wall, so (R) holds for those ether tails, in $K$ or not ([the ether
  census](findings/period-two/ether-defect-census.md)), in Lean for heads of up to 16 cells
  ([EtherCensus](Rule30Open/PeriodTwo/EtherCensus.md) for 12, [EtherCensus16](Rule30Open/PeriodTwo/EtherCensus16.md) for 16 with descent to smaller heads); with the condition of $K$, (R) holds in Lean for every point of $K$ whose
  tail from cell 28 on is the ether, whose defect then never leaves the head, and from cell 32 on with the bound 39
  ([EtherKTree](Rule30Open/PeriodTwo/EtherKTree.md), [EtherKTree32](Rule30Open/PeriodTwo/EtherKTree32.md)); by
  computation the points of $K$ with an ether tail from cell 56 on are exactly 203, on four periodic orbits (14 periodic
  points), and they are the points with $p \le 56$ of a finite backward tree of 303 points; conjecture (E), that these are
  all of them, gives (R) on the ether, and a counterexample keeps a defect of more than 57 cells ([the points of $K$ with an
  ether tail](findings/period-two/k-ether-points.md)), but neither the top of the defect nor its length decreases along $K$
  ([no monotone defect on K](negative-results/period-two/k-ether-monotone.md)); $K$ itself is a Cantor set of dimension
  1/2 whose points with a stripe tail are dense, so a census of heads decides nothing until a tail is fixed, and every point
  of $K$ with a tail period of at most 28 and $p + q \le 64$ has a stripe tail or lies in a finite backward closure of the 14
  ether points, so (E) for every tail period is (E) together with the absence of points of $K$ on other backgrounds ([the
  structure of K](findings/period-two/k-structure.md)); a descent of the top at a lag of about twice the top holds for
  heads of 25 to 40 cells, but each head length is its own census ([the descent at a lag](negative-results/period-two/k-descent-lag.md)); in general the bound is open, and the window automaton at the top of the defect does not do at 5, 8, 10 or 12 cells, where it has a cycle
  of positive gain, and real defects follow such cycles: one orbit returns to its own window of 24 cells 14 cells higher, so
  no potential on top windows of up to 28 cells holds even along single orbits ([the ether
  census](findings/period-two/ether-defect-census.md), item 3); no strip of 12 cells or fewer below the top is closed, and the condition of $K$ at
  a fixed lag removes none of its moves, since it does not restrict the cells above the lag (in Lean,
  [BoundedLag](Rule30Open/PeriodTwo/BoundedLag.md)), so
  bounding it is the mirror of the kit's `Absorption` for the ether
  ([ether fronts](negative-results/period-two/ether-front-windows.md)); the forced bits are dense polynomials of
  full degree, which rules out a sparse certificate ([forced bits](negative-results/period-two/forced-bits-dense.md)).
  The right half comes down to three closed sets: every right half of up to 20 cells, in both phases, enters within
  4,190 steps the gap trap of the kit's `Rule30GateTrap` (on its main branch, after the pinned commit), on which the
  black cells of column 1 come 3 or 5 white steps apart and the kit's open `Q01Gap` would exclude it, or the kit's
  ether-and-wall family, or a lock of period seven, 195 windows of 32 columns on which column 1 repeats $0101000$
  ([the census](findings/period-two/gate-census.md)). The last two exclude period two outright, and the lock does so in
  Lean for every half that enters it, whatever lies beyond column 32 ([SevenLock](Rule30Open/PeriodTwo/SevenLock.md)),
  so `Q01Gap` alone would exclude every configuration whose right half has at most 20 cells when its center starts to
  alternate.
  Beside the alternating center, every slip of column 1 out of its lock is one front crossing a locked layer of about 7
  columns along a single depth trace, decided about 20 steps ahead from the chaotic region, which feeds it at about
  0.26 columns per step ([slip geometry](findings/period-two/slip-geometry.md)).
  The structure of this shift and the aperiodic itinerary of a positive integer in it are in Lean
  ([ShiftModel](Rule30Open/PeriodTwo/ShiftModel.md)). Condrey's proof for a constant center does not extend: only the
  uniqueness of the left half carries over, the forced left half is not a finite-state function of the right half, and
  a bound on how long a row of radius $A$ alternates would itself be the period-two theorem; the longest such run is 36
  steps for $A \le 26$, with no law like Condrey's $A + 2$ ([the carry-over](findings/period-two/condrey-carryover.md),
  [where it stops](negative-results/period-two/condrey-mechanism.md)).
- **Least period three.** *Open.* The kit reduces it to statements about the left half and closes the ether-and-wall
  route for period three. For $001$ its period-21 trap `t001` remains, beside a second: every right half white on its
  first 1,317 cells enters `t001`, whatever lies beyond ([HighThree](Rule30Open/Columns/HighThree.md)), and every half
  of up to ten cells enters, but a median of about 16,000 steps in and the latest at step 186,490, at the rate a fair
  coin beyond the trap's 47 cells predicts ([the census](findings/columns/t001-census.md)), so a census in Lean is out
  of reach. Entry into `t001` alone, the kit's `AbsorptionT t001`, is false, and so is entry into one of any three of
  four traps for $001$ pairwise apart, so $001$ comes down to entry into one of the four, or into some trap of $001$
  ([Traps001](Rule30Open/Columns/Traps001.md)); the chains of the seeds with long runs of 1s tried, of periods up to 48,
  give no fifth trap. `t001` is the lock of a block of period 21 with twelve 1s in a row carried 38 columns left, and a
  second trap of the same kind, 52 cells with labels modulo 15, is in Lean ([lock
  chains](findings/columns/lock-chains.md), [WordTraps](Rule30Open/Columns/WordTraps.md)). For $011$ the right half
  never settles next to the center, so no trap of that kind appears ([the word
  011](negative-results/columns/period-three-011.md)), no chain found holds it, and the route is the kit's left-only
  statement `C3w`; against the white right half no left half within depth 32,751 keeps the center on $011$, in Lean
  ([WhiteRightHalf011](Rule30Open/Columns/WhiteRightHalf011.md)). Column 1 does settle into a set of words: under $001$ every right half, finite or not, has readings
  at the second white phase with no run of 1s of length 1 and no run of 0s of length 1 or 2 from step 46 on, a finite
  computation, and under $011$ every half of up to 16 cells reads no two whites 1, 2, 4 or 5 apart from step 104 on,
  so `C3s001` and `C3w` need only exclude free bits in those sets ([reading
  constraints](findings/columns/reading-constraints.md)); the same holds from every state for 15 blocks of period 3 to
  7, and by census for 8 more.
- **2-adic frames and exact reformulations.** *Closed as tried.* The 2-adic isometry, the seed's unique past and the
  strobed, group and stable-set forms all stop at a statement about the chaotic region
  ([reformulations](negative-results/dynamics/reformulations.md), [frames](CATALOG.md#frames-and-the-seeds-past)).
- **Random rows and probabilistic arguments.** *Closed.* The problems hold for random rows, provably, and no amount of
  randomness reaches the single cell ([random rows](negative-results/random-rows/almost-every-row.md)).
- **Counterexamples.** *No signal for the problem; found for hypotheses.* No row of up to 24 cells has a column that
  repeats from time 0, at periods up to 32 over 256 steps ([periodic from time
  0](negative-results/columns/periodic-from-start.md)), and no right half that the searches reach escapes the
  period-four lock ([slow halves](negative-results/columns/slow-half-search.md)). The hypotheses of the trap route do
  have counterexamples: a right half of 52 cells inside a second trap for $001$ never enters the kit's `t001`, so the
  kit's `AbsorptionT t001` is false, and with two more traps entry into one of any three of four is false
  ([Traps001](Rule30Open/Columns/Traps001.md)); entry into 360 single traps of the trap modules is false ([what
  failed](negative-results/columns/missed-traps.md), [ApartTraps](Rule30Open/Columns/ApartTraps.md)). No chain of a seed
  with a long run of 1s, of periods 16 to 40, reaches a word of period four, so no trap found misses the kit's family
  ([lock chains](findings/columns/lock-chains.md)). Finiteness on both sides adds no signal either: no row finite on both sides at the onset, with a right half of
  at most 11 to 14 cells and a left half of fewer than 1,000 cells, keeps its center on any of the 92 blocks of period 2,
  3, 5, 6, 7 or 9 ([finite onset census](findings/columns/finite-onset-census.md)), and from a late onset a small row
  follows a periodic word no longer than a random one ([late onsets](negative-results/columns/late-onset.md)).

## Problem 2: does each color occur with density 1/2?

- **Invariant measures and random rows.** *Closed.* Exact for random rows ([LeftWindow](Rule30Open/RandomRows/LeftWindow.md)),
  silent on the single cell ([random rows](negative-results/random-rows/almost-every-row.md)).
- **Conservation laws.** *Closed.* Rule 30 conserves no density over four steps, at any window width (the kit;
  [conservation laws](negative-results/structure/conservation-laws.md)).
- **Bounds on runs.** *Open.* Runs of the center column are at most linear in their start time, so each color occurs
  at least about $\log n$ times before $n$ (the kit); a black-run slope of $3/5$ and $\log\log$ margins are in the
  kit's main branch since October 30, after the commit this repository is pinned at ([the kit's pull
  requests](literature/kit-pull-requests.md#runs-of-the-center-column)). Numerically the longest runs are logarithmic.
  Every configuration whose left half starts white has a left half that is a function of the center column alone, and
  over every possible center column the left half allows, from time $t \le 175$, a black run of at most 0.13t to 0.18t
  and a white run of at most 0.15t to 0.28t (exact maxima over all drivers); a proof of such slopes would cut the kit's
  slopes 3/5 and 1 and raise the count of black cells before $n$ to about $2.8 \log_2 n$
  ([driven left runs](findings/diagonals/driven-left-runs.md)). The constraint that a black center fixes the next one cuts the
  reachable left halves by a factor of about 1.6 and leaves those maxima almost unchanged, and no finite automaton over
  the center column certifies a slope unless the admissible black runs are bounded ([finite-state
  slopes](negative-results/diagonals/finite-state-slopes.md)). Every configuration white left of a black cell settles to
  the single cell's pairs of left diagonals up to a time shift, by a step and base in Lean
  ([DrivenSkeleton](Rule30Open/Diagonals/DrivenSkeleton.md)) and an induction that holds while each white diagonal is
  followed by a doubling period, which the computation confirms below depth 53,207; so over all drivers the slope
  question is the single cell's question of when its left diagonals settle, and the forced-word, diagonal and
  window-rank routes stop there ([driven run slopes](negative-results/diagonals/driven-run-slopes.md)).
  In Lean, conditionally: if the left diagonals $8 \le j \le J$ repeat with period 16 from time $3j/2$, black runs
  starting at $a$ have length at most $3a/13 + 185$ and white blocks reach at most $a/3 + 34$ cells left, for $a$ up to
  about $3J/2$ ([settled runs](findings/diagonals/settled-runs.md), [SettledRuns](Rule30Open/Diagonals/SettledRuns.md)).
  The hypothesis holds for $j < 80{,}000$ up to time $2^{17}$ by computation, with onsets near $4j/3$, and fails past depth 87,866, where the period becomes 32, so as
  stated the theorem reaches only starts below about 143,000, where computation already bounds the runs; with a
  period that grows, [SettledSlope](Rule30Open/Diagonals/SettledSlope.md) proves in Lean that black runs from time
  $a$ have $13 L \le 3a + 130 A + 130 \delta + 260$ if every left diagonal $j \le J + 1$ repeats, with any period,
  from time $\lceil 3j/2 \rceil + \delta$, and adjacent settled diagonals alternate in antiphase at most $A$ times
  ($A$ equal to the period always suffices), for $\lfloor 8a/13 \rfloor \le J$; it also proves the reset bound, so a
  bound on the white runs of the settled diagonals gives slope $15/29$. Computation checks the hypotheses for every
  $j \le 200{,}000$ with $\delta = 0$ and $A = 9$. The slope $3/13$ for every $a$ needs $T_j \le 3j/2 + o(j)$ and
  $A_j = o(j)$ at every depth, which is linear settling with the period freed, and is open.
  The least front walk, which steps down on a black cell of $D_j$ and down-left on a white one (the kit main branch's
  `frontBound`), bounds every onset, and a walk of slope $41/20$ gives black runs of slope $63/185$, in Lean
  ([FrontWalker](Rule30Open/Diagonals/FrontWalker.md)); the walk advances about $2.01$ per depth to depth 200,000, with
  $\delta = 1$ at slope $41/20$, but it reads only the settled parts, and leads through the onset phase, the front
  at the white diagonals and a finite set of pair types stop at the transient or at a law of large numbers for the
  settled side ([linear-settling leads](negative-results/diagonals/linear-settling-leads.md)); a density budget on reset
  gaps, the decay of damage from one flipped cell and a doubling law for the onsets each reduce to the onsets again, and
  the onsets spread like a walk (variance about 2.2 per depth, a heuristic reading)
  ([onset heuristics](negative-results/diagonals/onset-heuristics.md)). Over every row white left
  of a black cell, a later row of which is again such a row, diagonal $j$ settles by $\lceil 3j/2 \rceil + 5$ for
  $j \le 76$, exactly, with 5 attained at $j = 48$; this seed-uniform bound is conjectured for every $j$ ([seed-uniform
  onsets](findings/diagonals/seed-uniform-onsets.md)), and a sound window abstraction proves it by computation for
  $j \le 1{,}252$ and proves $T_j \le \lceil 8j/5 \rceil$ for every seed and $j \le 87{,}866$ ([seed window
  bounds](findings/diagonals/seed-window-bounds.md)); no finite certificate gives it for every $j$, since a bounded
  potential would bound the one-step jump, which is one plus the longest white run of a settled diagonal and reaches 24
  by depth 200,000 ([finite certificates](negative-results/diagonals/seed-finite-certificate.md)). A potential that grows
  with the white runs does not help: the window bounds grow linearly faster than $3j/2$ while the largest white run
  stays at 15, a certificate that knows only the white runs needs slope $7/3$, and the step carries a white run to the
  diagonals before it without shortening it ([RunTransfer](Rule30Open/Diagonals/RunTransfer.md)), so it bounds the runs
  only by the period ([white-run potential](negative-results/diagonals/white-run-potential.md)). To depth 200,000 the
  settled words look like fair words of their period and the largest white run stays below $\log_2 j + 6$ ([settled
  words](findings/diagonals/settled-words.md)), so a logarithmic bound on it is a conjecture; and [PrefixWalk](Rule30Open/Diagonals/PrefixWalk.md) proves the
  rule that makes the search exact, but induction through later rows, subadditivity over seeds and a fixed delay behind
  the single cell all stop, the first at slope 2 ([seed-uniform induction](negative-results/diagonals/seed-uniform-induction.md)).
  A strip of fixed depth gains nothing on the slope $3/5$ ([fixed-depth
  strips](negative-results/diagonals/fixed-depth-strips.md)). *Assessment:* going below linear needs a statement about
  the chaotic left half near the center, here a linear bound on when the left diagonals settle, with a period that may
  grow; and even a logarithmic bound gives no positive density.
- **Transfer between columns.** *Proved in Lean, weak.* Left permutivity bounds the black cells of column $i - 1$
  by those of columns $i$ (twice) and $i + 1$, and likewise by their white cells, so upper densities satisfy
  $\bar d_{i-1} \le 2 \bar d_i + \bar d_{i+1}$, and rightward $\bar d_{i+1} \le \bar d_{i-1} + \bar d_i$
  ([ColumnTransfer](Rule30Open/Columns/ColumnTransfer.md)). This gives no
  positive density for the center: it moves a density bound left, never onto the center from nothing.
- **Statistics.** *No signal.* The column passes every randomness and compression test tried
  ([randomness tests](negative-results/statistics/randomness-tests.md), [compression](negative-results/statistics/compression.md)).
  Space-time patches of the single cell's chaotic region match the invariant measure under exact tests, and no
  linear or learned projection (PCA, classifiers, an autoencoder, t-SNE) tells them from a random row
  ([patch projections](negative-results/statistics/patch-projections.md)), nor does persistent homology tell its
  windows from those of random rows ([persistent homology](negative-results/statistics/persistent-homology.md)). The
  single cell's pattern has no periodic domain of spatial period at most 16 to row 8,191, so a route through ether walls
  needs the walls to come from the hypothesis ([pattern domains](negative-results/structure/pattern-domains.md)).

## Problem 3: does computing the $n$th cell take effort of order $n$?

- **An upper bound.** *Proved in Lean.* A one-tape machine in the kit's exact model computes $c(n)$ from the binary
  digits of $n$ in exactly $2n^2 + 2n\ell + 7n + 3\ell + 6$ steps, $\ell$ the number of digits, hence within
  $6(n + 1)^2$ ([the quadratic-time machine](Rule30Open/Complexity/QuadraticTime.md)). So the formal Problem 3
  quantifies over a nonempty class of machines and asks whether the exponent 2 of one-tape time can fall to 1.
- **A lower bound.** *Closed with present methods.* It is an exponential lower bound for one explicit function in
  exponential time ([the barrier](negative-results/complexity/problem-three-barrier.md)). Hypotheses about
  satisfiability, settled or not, do not reach it ([the hardness hypotheses](negative-results/complexity/hardness-hypotheses.md)),
  nor does probabilistic checking, and a circuit form of it would give $\mathrm{P} = \mathrm{BPP}$
  ([probabilistic checking](negative-results/complexity/probabilistic-checking.md)). Problem 3 implies Problem 1,
  proved in the kit's equivalent forms, so an affirmative answer to Problem 3 needs everything Problem 1 needs.
- **The cone as a Boolean function.** *Computed, with a proof.* An alternating left half fixes the center cell for
  every right half once $t \ge 8$ or 9, so the $2^t$ left halves give at most $2^t - 2$ functions of the right half;
  reading the row from the right gives far fewer subfunctions at $t \le 10$. No lower bound follows
  ([cone screening](findings/complexity/cone-screening.md)).
- **A space lower bound.** *Open, as hard.* By Paterson's theorem the kit's Problem 3 follows if the center column needs
  space larger than order $\sqrt{n}$, and by the kit Problem 1 follows if it needs any space that grows; tree evaluation
  on the kit's block tree computes it in space $O(\sqrt{n \log n})$, with the final bound of Cook and Mertz, as
  Sibgatullin and Williams (2026, unrefereed) do for any automaton of one dimension ([the space
  ladder](findings/complexity/space-ladder.md), [the thresholds](findings/complexity/space-thresholds.md)). So a lower
  bound through Paterson's theorem has room of a factor $\sqrt{\log n}$ only, and for multitape time $o(n)$ none.
  *Assessment:* a reformulation, and likely a closed one: if tree evaluation runs in space $O(h + b)$ on these trees,
  which Cook and Mertz miss by a factor $\log b$ on the height term, the center column takes space $O(\sqrt{n})$ and the
  threshold is out of reach. The claimed one-tape simulation in space $T^{2/5}$ (OpenAI's family 137, unrefereed) would
  lower the threshold to $n^{2/5}$ up to logarithms.
- **A shortcut.** *No signal.* Automata, linear recurrences, learned predictors and exact structure searches find none
  ([the complexity category](CATALOG.md#complexity), [learned models](CATALOG.md#learned-models)).
- **Restricted models.** *Open.* No automaton with fewer than 131,070 states computes the column from the digits of $t$
  on the range searched ([automaton bounds](negative-results/complexity/automaton-lower-bounds.md)), the column's series
  satisfies no Mahler equation over GF(2)(x) of small size, the column as a 2-adic or real number is a root of no integer
  polynomial of degree at most 8 with small coefficients, and the GF(2) cut ranks of the cone show nothing that rules of
  the same form lack ([hidden algebra](negative-results/structure/hidden-algebra.md)). *Assessment:* a
  lower bound in a restricted model is within reach only for finite ranges; an asymptotic one, even "the column is not
  automatic", needs structure of $c(n)$ as a function of the digits of $n$, which nothing here provides. Crossing
  sequences, the kit's method for one tape, give at most time of order $(\log n)^2$ for any function, and for $c$ only
  under a spectral hypothesis on its digit matrices that already implies Problem 1; every lower bound for finite
  automata with a bounded number of passes is a proof that $c$ is not 2-automatic ([crossing
  sequences](negative-results/complexity/one-tape-crossing.md)).
  In models that read the digits of $n$, a lower bound that exceeds the cost of reading them by an unbounded amount
  implies Problem 1; unbounded one-tape time is equivalent to excluding every eventual period $2^a$, which the kit's
  `Rule30Problem3Bounds` (main branch) does for $2^k$ with $k \le 13$ and a computation here for $k \le 20$, and
  $T(n) \ge \lfloor \log_2 n \rfloor + 2$ holds for $n < 2^{16}$. Two bounds hold for every $n$, a strip of width at
  least $(n - 1)/2$ and certificates of at least about $n^2/8$ cells, but Rule 90, whose column is white, meets both, so
  they bound the model and not $c$ ([restricted models](negative-results/complexity/restricted-models.md)). For a row
  given as input, a decision tree for the center cell after $t$ steps reads at least $2t$ cells (a Lean reduction joined
  on paper to the kit's degree theorem) and all $2t + 1$ for $t \le 22$ by computation, where Rule 90 needs only
  $2^{\mathrm{popcount}(t)}$; this bound is linear and says nothing about the single seed
  ([QueryDepth](Rule30Open/Complexity/QueryDepth.md)); certificates, sensitivity and fixed answers cannot pass $2t$,
  since no row is sensitive to all three rightmost cells of the cone, in Lean ([RightCorner](Rule30Open/Complexity/RightCorner.md),
  [query-depth routes](negative-results/complexity/query-depth-routes.md)); the center sees the two rightmost cone cells
  only through their OR, in Lean, so an adversary must answer the first of them white, and $2t + 1$ for every $t$ is
  equivalent to one function $G_t$ of $2t - 1$ cells needing all its cells; self-similar restrictions, restricted top
  coefficients and congruences stop ([CornerOr](Rule30Open/Complexity/CornerOr.md), [adversary
  routes](negative-results/complexity/query-adversary-routes.md)); the derivative along $x_{-t+1}$ is $t$ plus the parity
  of a diagonal that ends in a copy of $c_{t-1}$, and the right corner repeats once as an AND after $x_{t-3}$ is black, in
  Lean, but the adversaries for trees that read $x_{-t+1}$ last and earlier do not combine ($t \le 9$), gates stop after
  one level ($t \le 12$), and every linear measure is a multiple of $\mu$ ([SecondCells](Rule30Open/Complexity/SecondCells.md),
  [evasiveness routes](negative-results/complexity/query-evasive-routes.md)). As a function of the digits of $n$, $c$
  has the algebraic normal form, the parity correlations and the mod-3 correlations of a random function for digit
  lengths up to 20 ([index spectrum](negative-results/complexity/index-function-spectrum.md)), and one step on a ring of
  $W$ cells loses fewer than $0.85^W$ bits, less than Rule 90's 1 or 2, so erased information gives no lower bound
  ([ring images](findings/structure/ring-images.md), [ring loss](negative-results/complexity/ring-information-loss.md)).

## Next steps

In order of the assessment above.

1. **Attraction for period four.** The Lean classes so far are halves of at most fourteen cells, a white gap after the
   sixth, the tenth, the twelfth or the fourteenth cell, at most two black cells among the first $G$, the aligned ether
   cut anywhere with at most six cells after it, and every half whose column 17, 15 or 14 reads one fixed sequence
   ([LockWord](Rule30Open/Columns/LockWord.md)). Next: the shift lemma of
   [EtherPrefix](Rule30Open/Columns/EtherPrefix.md) applies to any half whose column 1 stays the ether's until it
   enters, so ether prefixes in front of the census halves, or of longer tails, need only base checks; three black cells
   by [SparseRight](Rule30Open/Columns/SparseRight.md)'s route need 32,219 to 476,314 kernel checks per word and phase;
   halves of 16 cells by [FourteenCells](Rule30Open/Columns/FourteenCells.md)'s route would take about four times its
   twelve minutes of kernel time and a data file of about 4 MB; and the slowest halves, which are rare and which local
   and beam searches do not find ([the slow-half searches](negative-results/columns/slow-half-search.md)). *Assessment:*
   each class is thin; a proof for every finite half needs an argument that the chaotic part near the center delivers a
   wall, which none of these gives.
2. **Block exclusions.** Where the route stands is in [Problem 1](#problem-1-is-the-center-column-eventually-periodic)
   above, in [the coverage](findings/columns/coverage.md) and in [what
   failed](negative-results/columns/missed-traps.md): the game excludes 1,400 blocks of periods up to 21 in Lean, blocks
   with nine 1s in a row have a uniform argument ([WallSets](Rule30Open/Columns/WallSets.md)), and a quarter to three
   tenths of each of periods 12 to 15 come down to entry into one of the block's traps. Next, in order:
   - *Hypotheses that no further trap refutes.* Two traps of one block apart from each other refute entry into each
     alone, and the chains of seeds keep giving traps: $001$ has four pairwise apart
     ([Traps001](Rule30Open/Columns/Traps001.md)), and 48 natural traps that pass the test of reach are missed by a
     wider carried trap of their block ([ApartTraps](Rule30Open/Columns/ApartTraps.md)), as are the only trap of
     $01111$ and two more, by locks of seeds with long runs of 1s carried hundreds of cells ([what
     failed](negative-results/columns/missed-traps.md)). The reduction of a block is entry into some trap of the block
     (`WTrap.AbsorptionAny`); search the chains of more seeds, of every multiple of the block's period, for traps apart
     from all known ones, which show how far a fixed list falls short.
   - *Wider tests of reach.* The test in games of 23 and 24 cells for every hypothesis that passes at 22, which only
     refutes more; the kit's family and `t001` pass at 26 ([reach of the kit's
     conjectures](findings/columns/kit-absorption-reach.md)).
   - *Lean refutations.* The refutations not yet checked, by `not_absorption` and `not_absorption_wide` of
     [MissedTraps](Rule30Open/Columns/MissedTraps.md), by `not_absorption_back` and `not_absorption_fwd` of
     [ReachRefuted](Rule30Open/Columns/ReachRefuted.md), or by `not_absorption_some_fwd` of
     [Traps001](Rule30Open/Columns/Traps001.md), as the size of each certificate allows the kernel.
   - *Hypotheses that can hold.* For the blocks whose traps all fail, traps built so that every window of the widest
     game tested can reach them: the natural traps of the scans
     ([NaturalTrapsWalls](Rule30Open/Columns/NaturalTrapsWalls.md)), the walls that the few windows missing a carried
     trap settle into ([WideWalls](Rule30Open/Columns/WideWalls.md)), sets of several traps
     ([TrapSets](Rule30Open/Columns/TrapSets.md)), and the kit's `Lock`, the weakest hypothesis of the kind ([the kit's
     pull requests](literature/kit-pull-requests.md#least-periods-four-and-three-traps-for-the-right-half)). The
     block's own locked windows of 20 or 22 cells give traps that pass both tests to 14 blocks of periods 11 and 13
     ([own locks](findings/columns/own-locks.md)); next, the apartness check for the nine blocks not yet compared
     (`census_apart`), the module `Rule30Open.Columns.WideCensus` from `lean_wide_census`, counting the blocks in
     `coverage.py`, the 22-cell traps of $0010011110101$, and the census at periods 14 and 15, where it already finds
     blocks with locks every window can reach.
   - *Period 16.* Traps from the three backgrounds with walls at period 16, of 216, 325 and 2,032 cells, whose chains
     hold 1,365 of the 4,080 blocks, and wider windows for the backgrounds without walls of 16 cells.
   - *Classes of halves.* For the walls with Lean classes of entering halves ([TenGap](Rule30Open/Columns/TenGap.md),
     [WallGaps](Rule30Open/Columns/WallGaps.md), [NineWhite](Rule30Open/Columns/NineWhite.md)), wider classes, such as
     every half of twelve cells as [FourteenCells](Rule30Open/Columns/FourteenCells.md) does for period four, and a word
     of the column beyond that brings every window in, as [LockWord](Rule30Open/Columns/LockWord.md) does.
   - *Steering.* Steering at wider windows and longer periods ([steerable locks](findings/columns/steerable-locks.md)),
     the one tool here that reaches blocks without long runs, though only to a condition on a farther column.
   - *Periods 5, 6 and 7.* Traps that the coin of `coin_entry` enters readily ([trap
     entry](negative-results/columns/trap-entry.md)); for $001011$, whose four known traps share their first 22 cells
     and fail in the game of 22 cells, a trap that does not begin with those columns, which has to be wider than 22
     cells ([what failed](negative-results/columns/missed-traps.md)).
   - *The left half.* For the blocks no trap reaches, one statement per block
     ([LeftLatch](Rule30Open/Columns/LeftLatch.md)), which no small half meets
     ([every block](findings/columns/left-half-every-block.md)).

   *Assessment:* every family of exclusions rests on long runs, and a typical block of large period has only short
   ones, so exclusions stay thin. The trap reductions reach a quarter to three tenths of each period, but each rests on
   entry, a statement about the chaotic part of the right half of the same kind as the problem. A fair coin in place of
   that part enters the kit's `t001` at about the rate Rule 30's own halves do ([the census for
   001](findings/columns/t001-census.md)), so for a trap that every window can reach entry is what a random model
   predicts; but no argument turns the coin into entry for every finite half, and since a block can have several traps
   apart from each other, the hypothesis has to be entry into one of all of them.
3. **Findings that want a Lean proof.** The census beyond what SparseRight covers, the entry statements of the
   period-four certificate, the periodic backgrounds and the period-two computations ([open
   work](CATALOG.md#open-work)); the general facts of the seed's past are now in Lean
   ([SeedPast](Rule30Open/Frames/SeedPast.md), [SeedPastPeriods](Rule30Open/Frames/SeedPastPeriods.md)). The 2-adic
   trace, the center degree and the Duhamel form are proved in the kit's equivalent forms, which a search should include
   before any formalization (`.lake/packages/rule30prize/equivalents/Rule30Equivalents/`).
4. **Track the kit and the literature.** Re-pin the kit when it gains modules, after the build, the audit and the tests
   pass, and move an entry's `kit:` relation when the kit gains its result; keep [the literature](literature/README.md)
   current, AI-proposed claims included ([ai-proposed.md](literature/ai-proposed.md)), and the kit's open pull
   requests ([kit-pull-requests.md](literature/kit-pull-requests.md)) until each is merged or closed.
5. **Period two, Problems 2 and 3: the open statements at their sharpest.**
   - *Reading constraints in Lean.* The forced sets of words of [reading
     constraints](findings/columns/reading-constraints.md), from every state for 15 blocks of period 3 to 7, are
     finite checks of a few million states. For $001$ the kernel checks the run constraint at the second white step
     ([ThreeRuns](Rule30Open/Columns/ThreeRuns.md)), which reduces $001$ in Lean to `C3r001`, the kit's `C3s001` with
     constrained free bits ([ConstrainedLeft001](Rule30Open/Columns/ConstrainedLeft001.md)). The constraint lowers
     the left statement's entropy from 1/3 to 0.2042 bits per step, but no finite left game closes it ([constrained left
     halves](negative-results/columns/constrained-left-halves.md)). The kernel also checks $00001$
     ([Runs00001](Rule30Open/Columns/Runs00001.md)) and, read at one white step, 15 blocks of period 5 to 7
     ([ReadingWords](Rule30Open/Columns/ReadingWords.md)). Every list kernel-checked so far keeps positive entropy;
     an exclusion would need a forced list of entropy 0 read at every white step.
   - *Period two, the right half.* Every finite right half entering the gap trap, the kit's ether family or the lock of
     period seven ([the census](findings/period-two/gate-census.md)) would leave the left statement `Q01Gap` alone; the
     census reaches 20 cells, and wider locks, or a test of reach for the three sets together, are next.
   - *Period two.* (R) on ether tails is what the computations leave; it needs every defect on the ether to have a
     bounded top ([the shift model](findings/period-two/shift-model.md), items 5 and 8). Windows of 5, 8, 10 and 12 cells at the top
     cannot certify that, with or without $K$ ([ether fronts](negative-results/period-two/ether-front-windows.md),
     [BoundedLag](Rule30Open/PeriodTwo/BoundedLag.md)); entry into the 13-cell closed strips suffices and is the mirror
     of the kit's `Absorption` for the ether. Next: a statement about the region between the wall and the top that
     uses $K$ at a lag growing with the top, or a proof of entry for the ether that also serves the kit.
   - *Problem 2.* The transfer inequalities ([ColumnTransfer](Rule30Open/Columns/ColumnTransfer.md)) move density
     bounds left and give nothing on the center; a positive lower density needs an input that creates black cells,
     such as a linear bound on runs with slope below 1 ([bounds on runs](#problem-2-does-each-color-occur-with-density-12)).
   - *Problem 3.* The cone of the center is screened by alternating left halves
     ([ConeScreening](Rule30Open/Complexity/ConeScreening.md)), so its $2^t$ left halves are not pairwise distinguishable
     for $t \ge 9$; the counts for other variable orders are in [cone screening](findings/complexity/cone-screening.md)
     to $t = 10$, and a proof of a lower bound for some order is open.
