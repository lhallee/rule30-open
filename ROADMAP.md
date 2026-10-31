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
kit's commit 932cf8d; the kit's main branch has since gained 27 modules from nine pull requests (a6399ef, October 30),
and moving the pin there, after the build, the audit and the tests pass, is pending.

## At a glance

| Problem | Route | Status | Where it stands |
|---|---|---|---|
| 1 | Rigidity from the left edge | closed on its own | no two adjacent columns are eventually periodic; Rules 90, 150 and 210 share every fact it uses |
| 1 | Excluding eventual periods block by block | open | the finite game excludes 1,400 blocks of period at most 21, all in Lean, and reaches no block of period 2, 3, 5, 6, 7 or 9 |
| 1 | Single blocks through traps | open | 16 of the 56 blocks of period 9, 24 of the 99 of period 10, 56 of the 186 of period 11, 99 of the 335 of period 12, 183 of the 630 of period 13, 340 of the 1,161 of period 14 and 537 of the 2,182 of period 15 come down to entry into traps that every window of 20 cells can reach, in Lean, from walls at the edges of backgrounds periodic in time and space, all of which are known to period 14 and six of period 15, from the closed sets that driven right halves settle into, every block of periods 10 to 14 that a sampled half settles into a trap for (at 13 and 14 with windows of 16 cells), and from every locked window of 16 cells at periods 10 to 15, carried by its chain; for one block each of period 10, 11 and 12 every right half white past its first eight cells, to a bound of 1,610 to 3,058, enters, in Lean, and for two blocks of period 9 every right half white on its first $10^5$ cells or so enters from most phases; one block each of period 3, 5, 6 and 7 has a trap that small halves almost never enter; entry into 247 other traps, most of them carried along a background's columns, is false, seven of them in Lean, and ten blocks need entry into one of two traps |
| 1 | Least period four through the right half's lock | lead | every right half of up to 20 cells enters the kit's family by computation, up to 14 cells in Lean; open for the rest |
| 1 | Least period four through the left half | open | no left half of up to 80 cells meets the kit's `C3`; depth 88 in Lean |
| 1 | Every period through the left half | open | one statement per block (`LeftLatch`); no left half of up to 37 to 100 cells meets it at the lock-free periods |
| 1 | Period two through the held column | open, hard | a map with the shape of a Collatz problem; every integer below $2^{52}$ fails |
| 1 | Least period three | open | $001$ through the kit's trap, which every window of 24 cells can reach (a second trap fails that test), $011$ through the left half |
| 1 | 2-adic frames and exact reformulations | closed as tried | every form stops at a statement about the chaotic region |
| 1 | Random rows and probabilistic arguments | closed | true for almost every row, silent on the single cell |
| 1 | Counterexamples | no signal for the problem | no small row has a periodic column; no right half found escapes the period-four lock; but 247 trap reductions here had false hypotheses, a closed set of windows apart from each trap |
| 2 | Invariant measures and random rows | closed | exact for random rows only |
| 2 | Conservation laws | closed | none over four steps |
| 2 | Bounds on runs | open | runs at most linear in their start time |
| 2 | Statistics | no signal | the column passes every test tried |
| 3 | A lower bound | closed with present methods | it amounts to an exponential lower bound for one explicit function |
| 3 | A space lower bound | open, as hard | space $O(\sqrt{n} \log n)$ suffices; needing more than order $\sqrt{n}$ would give the kit's Problem 3 |
| 3 | A shortcut | no signal | automata, recurrences and learned predictors find none |
| 3 | Restricted models | open | no automaton below 131,070 states on the range searched |

## Problem 1: is the center column eventually periodic?

- **Rigidity from the left edge.** *Closed as a route on its own; every other route ends with it.* Two adjacent
  columns are never both eventually periodic, and no column is eventually constant
  ([AdjacentColumns](Rule30Open/Columns/AdjacentColumns.md)). The kit proves that Rules 90, 150 and 210 share every
  fact this argument uses and have eventually constant center columns, so it cannot imply Problem 1 alone.
- **Excluding eventual periods block by block.** *Open.* Each block needs its own certificate outside a few families,
  and the share of blocks covered falls with the period. [The coverage](findings/columns/coverage.md) counts, period by
  period up to 12, the blocks excluded, reduced to entry into a trap, reduced by steering, or not reached: at periods 5
  to 7 one block each is reached, and from period 9 a quarter to two fifths have traps.
  - *Excluded.* Finite games, strip certificates and padding families exclude 197 of the 8,800 blocks of period at most
    16, all 136 beyond the kit in Lean ([game blocks](findings/columns/game-blocks.md),
    [BitGame](Rule30Open/Columns/BitGame.md)), 261 of the 22,242 of period 17 and 18, 508 of the 79,971 of period 19 and
    20 and 434 of the 99,858 of period 21, all in Lean, those that need 13 or 14 cells one phase at a time ([periods 17
    and 18](findings/columns/game-blocks-18.md), [periods 19 and 20](findings/columns/game-blocks-20.md), [period
    21](findings/columns/game-blocks-21.md), [BitPhases](Rule30Open/Columns/BitPhases.md)); the kit excludes every
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
    requests](literature/kit-pull-requests.md#excluding-eventual-periods-by-families-of-blocks)).
  - *Where it stops.* The share of blocks the game excludes falls from 2.7% at period 12 to 0.56% at period 20, and
    every exclusion rests on a run of five or more equal values; most blocks do not lock the right half
    ([locking](findings/columns/period-four-locking.md)); column words that fix the cell beside the column without a
    long run exclude no block the game misses up to period 20 ([forcing
    words](negative-results/columns/forcing-words.md)). No block of period 2, 3, 5, 6, 7 or 9 has a locked window of up
    to 18 cells ([window locks](negative-results/columns/window-locks.md)). Wider ones exist for one block or more of
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
  truncation of the aligned ether, the only infinite half seen to stay out, followed by at most six cells
  ([EtherPrefix](Rule30Open/Columns/EtherPrefix.md) for four, [EtherPrefixSix](Rule30Open/Columns/EtherPrefixSix.md) for
  six); a window of 16 columns has a certificate ([the certificate](findings/columns/period-four-certificate.md)), in
  Lean a trap ([PeriodFourCertificate](Rule30Open/Columns/PeriodFourCertificate.md)), every window can reach it, and one
  word of a few hundred values in column 17 forces entry ([the coin lock](findings/columns/coin-lock.md)); in Lean, one
  sequence of 1,193, 955 or 381 values in column 17, 15 or 14 brings every window into the family, so a center that
  repeats the word keeps that column off the sequence forever ([LockWord](Rule30Open/Columns/LockWord.md)). No set of
  windows of up to 23 cells that no move leaves misses the family, nor one of up to 24 cells the kit's `t001` for $001$
  ([reach of the kit's conjectures](findings/columns/kit-absorption-reach.md)): the test that refutes entry into seven
  traps of periods 13 to 15 ([MissedTraps](Rule30Open/Columns/MissedTraps.md)) finds nothing against either. Open:
  attraction for halves with at least three black cells among the first $G$ columns, one of them among columns 1 to 30,
  one among columns 7 to $B$, one among columns 11 to $G'$ and one among columns 15 to 750, 1,446 and 560, beyond the
  census's 20 cells. *Assessment:* the most direct route to a full case of Problem 1, though attraction asks the chaotic
  part of the right half to deliver an entry pattern, a statement of the same kind as the problem.
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
  18 cells reaches,
  and for each of their 91 blocks no left half of at most 37 to 100 cells meets it ([every
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
  requests](literature/kit-pull-requests.md#period-two)).
- **Least period three.** *Open.* The kit reduces it to statements about the left half and closes the ether-and-wall
  route for period three. For $001$ its period-21 trap `t001` remains: every right half white on its first 1,317 cells
  enters it, whatever lies beyond ([HighThree](Rule30Open/Columns/HighThree.md)), and every half of up to ten cells
  enters, but a median of about 16,000 steps in and the latest at step 186,490 ([the
  census](findings/columns/t001-census.md)), so a census in Lean is out of reach. `t001` is the lock of a block of
  period 21 with twelve 1s in a row carried 38 columns left, and a second trap of the same kind, 52 cells with labels
  modulo 15, is in Lean ([lock chains](findings/columns/lock-chains.md),
  [WordTraps](Rule30Open/Columns/WordTraps.md)). For $011$ the right half never settles next to the center, so no trap
  of that kind appears ([the word 011](negative-results/columns/period-three-011.md)), no chain found holds it, and the
  route is the kit's left-only statement `C3w`.
- **2-adic frames and exact reformulations.** *Closed as tried.* The 2-adic isometry, the seed's unique past and the
  strobed, group and stable-set forms all stop at a statement about the chaotic region
  ([reformulations](negative-results/dynamics/reformulations.md), [frames](CATALOG.md#frames-and-the-seeds-past)).
- **Random rows and probabilistic arguments.** *Closed.* The problems hold for random rows, provably, and no amount of
  randomness reaches the single cell ([random rows](negative-results/random-rows/almost-every-row.md)).
- **Counterexamples.** *No signal.* No row of up to 24 cells has a column that repeats from time 0, at periods up to
  32 over 256 steps ([periodic from time 0](negative-results/columns/periodic-from-start.md)), and no right half
  that the searches reach escapes the period-four lock ([slow halves](negative-results/columns/slow-half-search.md)).

## Problem 2: does each color occur with density 1/2?

- **Invariant measures and random rows.** *Closed.* Exact for random rows ([LeftWindow](Rule30Open/RandomRows/LeftWindow.md)),
  silent on the single cell ([random rows](negative-results/random-rows/almost-every-row.md)).
- **Conservation laws.** *Closed.* Rule 30 conserves no density over four steps, at any window width (the kit;
  [conservation laws](negative-results/structure/conservation-laws.md)).
- **Bounds on runs.** *Open.* Runs of the center column are at most linear in their start time, so each color occurs
  at least about $\log n$ times before $n$ (the kit); a black-run slope of $3/5$ and $\log\log$ margins are in the
  kit's main branch since October 30, after the commit this repository is pinned at ([the kit's pull
  requests](literature/kit-pull-requests.md#runs-of-the-center-column)). Numerically the longest runs are logarithmic. *Assessment:* going below linear needs
  a statement about the chaotic left half near the center, and even a logarithmic bound gives no positive density.
- **Statistics.** *No signal.* The column passes every randomness and compression test tried
  ([randomness tests](negative-results/statistics/randomness-tests.md), [compression](negative-results/statistics/compression.md)).

## Problem 3: does computing the $n$th cell take effort of order $n$?

- **A lower bound.** *Closed with present methods.* It is an exponential lower bound for one explicit function in
  exponential time ([the barrier](negative-results/complexity/problem-three-barrier.md)). Hypotheses about
  satisfiability, settled or not, do not reach it ([the hardness hypotheses](negative-results/complexity/hardness-hypotheses.md)),
  nor does probabilistic checking, and a circuit form of it would give $\mathrm{P} = \mathrm{BPP}$
  ([probabilistic checking](negative-results/complexity/probabilistic-checking.md)). Problem 3 implies Problem 1,
  proved in the kit's equivalent forms, so an affirmative answer to Problem 3 needs everything Problem 1 needs.
- **A space lower bound.** *Open, as hard.* By Paterson's theorem the kit's Problem 3 follows if the center column needs
  space larger than order $\sqrt{n}$, and by the kit Problem 1 follows if it needs any space that grows; tree evaluation
  on the kit's block tree computes it in space $O(\sqrt{n} \log n)$ ([the space
  ladder](findings/complexity/space-ladder.md)). *Assessment:* a reformulation, and likely a closed one: if tree
  evaluation runs in logarithmic space, which Cook and Mertz's algorithm misses by a factor $\log b$, the center column
  takes space $O(\sqrt{n})$ and the threshold is out of reach. The claimed one-tape simulation in space $T^{2/5}$ would
  lower the threshold to $n^{2/5}$.
- **A shortcut.** *No signal.* Automata, linear recurrences, learned predictors and exact structure searches find none
  ([the complexity category](CATALOG.md#complexity), [learned models](CATALOG.md#learned-models)).
- **Restricted models.** *Open.* No automaton with fewer than 131,070 states computes the column from the digits of $t$
  on the range searched ([automaton bounds](negative-results/complexity/automaton-lower-bounds.md)). *Assessment:* a
  lower bound in a restricted model is within reach only for finite ranges; an asymptotic one, even "the column is not
  automatic", needs structure of $c(n)$ as a function of the digits of $n$, which nothing here provides.

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
2. **Block exclusions.** Blocks with nine 1s in a row now have a uniform argument
   ([WallSets](Rule30Open/Columns/WallSets.md)), which matches the game on every such block to period 16. The open cases
   are blocks without a long run of 1s. All 197 blocks [the game](findings/columns/game-blocks.md) excludes up to period
   16 are kernel-checked, seven of them by [BitGame](Rule30Open/Columns/BitGame.md), which decides the game from the
   block alone, without a certificate. At periods 17 and 18 the game excludes 261 more, all with a run of at least six
   equal values ([periods 17 and 18](findings/columns/game-blocks-18.md)); periodic orbits on rings of up to 25 cells
   explain the game's failure only for $01$ ([ring orbits](negative-results/columns/ring-orbits.md)), and the
   backgrounds periodic in time of period up to 14, on rings of up to 728 cells, for eight more blocks, $0001$ among
   them ([backgrounds periodic in time](findings/columns/space-time-backgrounds.md)). At periods 19 and 20 it excludes
   508 more, 327 of them new ([periods 19 and 20](findings/columns/game-blocks-20.md)), and at period 21 it excludes
   434, 303 of them new, 0.43% of the period ([period 21](findings/columns/game-blocks-21.md)). Lean checks every one of
   these 1,400 blocks; the 75 that need 13 or 14 cells, whose check as one declaration takes the kernel up to 12 GB or
   more, are checked one phase at a time ([BitPhases](Rule30Open/Columns/BitPhases.md)). Next: steering ([steerable
   locks](findings/columns/steerable-locks.md)) at wider windows and longer periods, the one tool here that reaches
   blocks without long runs, though only to a condition on a farther column. Column words without long runs also fix the
   cell beside the column, the shortest being $0110000$, but up to period 20 they exclude no block the game misses
   ([forcing words](negative-results/columns/forcing-words.md)). *Assessment:* every family found so far rests on long
   runs, and a typical block of large period has only short ones, so these exclusions stay thin. Every locked window
   found is the lock of a seed carried leftward through columns the rule determines ([lock
   chains](findings/columns/lock-chains.md)): the three families that lock at period 8 and from 10 but not at 9 are one
   chain, that of $0\,1^{P-1}$, whose block of period 9 does not lock, and the kit's wall for period four and its trap
   for $001$ are chains too. Wider chain locks reach one block or more of each period from 2 to 9, and six are traps in
   Lean ([WordTraps](Rule30Open/Columns/WordTraps.md)). Period 9 has an ether and a wall like period four's: the lock of
   $001011111$, 43 cells wide, whose chain enters a background of spatial period 135, gives traps to 21 blocks of period
   9 that driven right halves enter, and a second wall, for $001010011$, a 22nd
   ([NineTraps](Rule30Open/Columns/NineTraps.md)). Of 301 halves, the 67 whose column 1 locks under a word of period 9
   are all inside traps, under 12 of these 22 blocks, and the white right half enters both walls from most phases, but
   only after $10^5$ steps; at periods 5, 6 and 7 driven halves almost never settle next to the center, none of the 301
   under a word of period 6 or 7, and a fair coin in place of the cells beyond the window enters the traps about as
   often as the rule's own half does, so the traps found there are hard to reach whatever arrives from the right ([trap
   entry](negative-results/columns/trap-entry.md)). Over 500,000 steps, small halves keep entering both walls of period
   9 at steady rates, about $2.2 \cdot 10^{-6}$ and $1.4 \cdot 10^{-6}$ per step: two thirds and one half of a sample by
   the end. In Lean, every right half white on its first 91,129 to 201,172 cells enters them from the phases where the
   white half does, 4 of the 9 phases of $001011111$ and 6 of $001010011$
   ([NineWhite](Rule30Open/Columns/NineWhite.md)). From period 10 on driven halves settle often: about a quarter of the
   blocks of period 10, 11 and 12 have traps that random halves enter, often every one of 31 within 12,000 steps
   ([natural traps](findings/columns/natural-traps.md)), and at period 10 one background of spatial period 155, whose
   edge every right half of up to eight cells and the white half enter within 3,042 and 74 steps, gives traps to 25
   blocks that the kit does not exclude, the nine blocks with locked windows of 13 cells among its columns
   ([TenTraps](Rule30Open/Columns/TenTraps.md)). In Lean, no finite configuration whose cells 9 to 3,058 are white has a
   center repeating $0000010001$ ([TenGap](Rule30Open/Columns/TenGap.md)), and every block of periods 10 to 12 that a
   sampled half settles into a trap for, and that nothing excludes, has a trap there: carried from a wall, or the closed
   set itself for 35 blocks ([NaturalTraps](Rule30Open/Columns/NaturalTraps.md)), one of them of 61,857 windows checked
   in parts ([NaturalTrapsLarge](Rule30Open/Columns/NaturalTrapsLarge.md)). Every background periodic in time is known
   up to period 14, at most nine per period, and each trap found by sampling at periods 8 to 12 that counts the phase
   modulo the period is a wall of one of them: of the ether at period 8, of one or two backgrounds at each of periods 9
   to 12 ([backgrounds periodic in time](findings/columns/space-time-backgrounds.md)). The natural scan with windows of
   16 cells finds traps for 86 blocks of period 13 and 109 of period 14, the commonest walls of the backgrounds of 689
   and 728 cells, and the smallest wall of each, carried leftward, gives traps to every block of its period among that
   background's columns ([ThirteenTraps](Rule30Open/Columns/ThirteenTraps.md),
   [FourteenTraps](Rule30Open/Columns/FourteenTraps.md)). A census of every locked window of 16 cells at periods 10 to
   14 sorts the locks by the background their chains end in: none ends in the backgrounds of 30 or 90 cells at period
   10, 100 at 12, 117 or 130 at 13, or 14, 28 or 84 at 14, and carried by their chains they reach 12, 135 and 244 blocks
   of periods 12 to 14 that nothing reached, all but one now with traps in Lean ([backgrounds periodic in
   time](findings/columns/space-time-backgrounds.md), [FarWalls](Rule30Open/Columns/FarWalls.md),
   [CensusTraps13](Rule30Open/Columns/CensusTraps13.md), [CensusTraps14](Rule30Open/Columns/CensusTraps14.md),
   [CensusTrapsLarge](Rule30Open/Columns/CensusTrapsLarge.md)), though small halves enter few of the traps carried far.
   At period 15 the same census finds six backgrounds with walls, of 64 to 2,145 cells, and its chains hold 648 of the
   2,182 blocks, every block excluded there and 595 more, all but two now with traps in Lean
   ([CensusTraps15](Rule30Open/Columns/CensusTraps15.md),
   [CensusTrapsLarge15](Rule30Open/Columns/CensusTrapsLarge15.md)). Entry needs at least that every node of the finite
   game can reach the trap, and that is false for 247 traps: seven at their own width of 16 cells, refuted in Lean
   ([MissedTraps](Rule30Open/Columns/MissedTraps.md)), and 240 still in the modules in the game of 20 cells ([what
   failed](negative-results/columns/missed-traps.md)). Most are traps carried along a background's columns; seven, of
   16 to 19 cells, pass in the game of their own width, where the cell beyond takes any value, and fail in that of 20,
   where the cells after them follow the rule, among them two walls and two natural traps. The sampled halves of ten
   blocks split between two traps apart from each other, and these come down to entry into one of the two
   ([TrapPairs](Rule30Open/Columns/TrapPairs.md), [NaturalTrapsWalls](Rule30Open/Columns/NaturalTrapsWalls.md), which
   refutes entry into each trap alone of five of its six pairs in Lean with `not_absorption_wide`); for three of these
   blocks only the halves show it, the test of reach at 20 cells passing; from the white window of the other
   three blocks of MissedTraps no locked window of 16 to 18 cells can be reached. Natural traps that pass reduce 60 of
   the blocks whose wall traps fail ([NaturalTrapsWalls](Rule30Open/Columns/NaturalTrapsWalls.md)). With the failures
   taken out, a quarter to three tenths of each of periods 12 to 15 comes down to entry into a trap that passes ([the
   coverage](findings/columns/coverage.md)). With windows of 18 cells, periods 10 to 12 have more locks but their chains
   hold the same blocks, and the backgrounds without a wall of 16 cells still have none. The census at period 16 finds
   three backgrounds with walls, of 216, 325 and 2,032 cells, whose chains hold 1,365 of the 4,080 blocks. Next: traps
   for the 173 blocks whose traps all fail, built so that every window of 20 cells can reach them; the test of reach in
   wider games, which only refutes more, natural traps among them; Lean refutations for the 240, with `not_absorption`
   and `not_absorption_wide`; traps for period 16; and at
   widths well past 18 for the backgrounds without walls, as the walls of period 9 are 43 cells wide; wider
   classes of halves for that edge, such as every half of twelve cells, as
   [FourteenCells](Rule30Open/Columns/FourteenCells.md) does for period four, and the word of 569 values of column 17
   that brings every window into it, as [LockWord](Rule30Open/Columns/LockWord.md) does for period four; the walls of
   periods 11 and 12 are carried in Lean too ([ElevenTraps](Rule30Open/Columns/ElevenTraps.md),
   [TwelveTraps](Rule30Open/Columns/TwelveTraps.md)), and two of them, with the wall of period 10, take every half white
   past its first eight cells ([WallGaps](Rule30Open/Columns/WallGaps.md)); other classes of halves for the walls of
   period 9; at periods 5, 6 and 7 traps that the coin of `coin_entry` enters readily; and for the blocks no trap
   reaches, the left half, one statement per block ([LeftLatch](Rule30Open/Columns/LeftLatch.md)), which no small half
   meets ([every block](findings/columns/left-half-every-block.md)).
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
