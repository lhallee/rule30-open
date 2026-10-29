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
kit's commit 932cf8d.

## Problem 1: is the center column eventually periodic?

- **Rigidity from the left edge.** *Closed as a route on its own; every other route ends with it.* Two adjacent
  columns are never both eventually periodic, and no column is eventually constant
  ([AdjacentColumns](Rule30Open/Columns/AdjacentColumns.md)). The kit proves that Rules 90, 150 and 210 share every
  fact this argument uses and have eventually constant center columns, so it cannot imply Problem 1 alone.
- **Excluding eventual periods block by block.** *Open.* Finite games, strip certificates and padding families exclude
  specific repeating blocks: 197 of the 8,800 blocks of period at most 16, all 136 beyond the kit in Lean ([game
  blocks](findings/columns/game-blocks.md), [BitGame](Rule30Open/Columns/BitGame.md)), every $1\,0^q$ with $q \ge 9$,
  and every block followed by exponentially many white cells (the kit). Following the cells beside the column after nine
  1s extends the kit's long black runs to every period whose runs of nine or more 1s are separated by segments that the
  possible windows of three cells follow: exactly the 77 blocks with nine 1s in a row of period at most 16 that the game
  excludes, 616 blocks up to period 22, and families such as $1^a 0^b 1 0$, $1^a 0 1 1 0^c$ and $1^a 0^{2k+3} 1 0 0$ for
  every $a \ge 9$ ([WallSegments](Rule30Open/Columns/WallSegments.md) with three values per cell,
  [WallSets](Rule30Open/Columns/WallSets.md) with sets of windows). A run of $r \ge 9$ 1s rules out every tail of at
  most $4 \lfloor r/9 \rfloor$ steps, and nine 1s and then $b$ 0s every tail of at most
  $4 \lfloor (b - 1)/9 \rfloor + 2$ steps, which sharpen the kit's Theorems B and D
  ([WideWall](Rule30Open/Columns/WideWall.md)). Any eventual period needs $T + P \ge 65{,}518$ ([a window of 65,536
  cells](Rule30Open/Columns/LongWindow.md), where the kit has 16,359). Open pull requests to the kit claim every
  eventual period whose white runs are all at least 17, and four more families of blocks with long white runs ([the
  kit's pull requests](literature/kit-pull-requests.md#excluding-eventual-periods-by-families-of-blocks)). Outside such
  families each block needs its own certificate, and most blocks do not lock the right half
  ([locking](findings/columns/period-four-locking.md)); column words that fix the cell beside the column without a long
  run exist, but exclude no block the game misses up to period 20 ([forcing
  words](negative-results/columns/forcing-words.md)).
- **Least period four through the right half's lock.** *Lead.* Masked Jen excludes the three words of period four once
  every finite right half enters the kit's ether-and-wall family, the kit's open `Absorption`. Known: every right half
  of up to 20 cells enters ([the census](findings/columns/absorption-census.md)); every half white on columns 1 to 30
  enters (the kit for $0001$, [WhiteGap](Rule30Open/Columns/WhiteGap.md) for all three words); in Lean, halves of up to
  ten cells enter ([EmptyRight](Rule30Open/Columns/EmptyRight.md) for six, [TenCells](Rule30Open/Columns/TenCells.md)
  for ten), so does every half white on columns 7 to $B$, whatever lies beyond, with $B$ = 316, 535 and 310
  ([WhiteGap](Rule30Open/Columns/WhiteGap.md)), and every half white on columns 11 to $G'$, with $G'$ = 562, 654 and 371
  ([TenCells](Rule30Open/Columns/TenCells.md)), and so does every half with at most two black cells among columns 1 to
  $G$, whatever lies beyond, with $G$ = 778, 1,359 and 623, which includes one black cell anywhere
  ([SparseRight](Rule30Open/Columns/SparseRight.md); the kit has one cell for $0001$), and so does every truncation of
  the aligned ether, the only infinite half seen to stay out, followed by at most four cells
  ([EtherPrefix](Rule30Open/Columns/EtherPrefix.md)); a window of 16 columns has a certificate ([the
  certificate](findings/columns/period-four-certificate.md)), every window can reach it, and one word of a few hundred
  values in column 17 forces entry ([the coin lock](findings/columns/coin-lock.md)). Open: attraction for halves with at
  least three black cells among the first $G$ columns, one of them among columns 1 to 30, one among columns 7 to $B$ and
  one among columns 11 to $G'$, beyond the census's 20 cells. *Assessment:* the most direct route to a full case of
  Problem 1, though attraction asks the chaotic part of the right half to deliver an entry pattern, a statement of the
  same kind as the problem.
- **Least period four through the left half.** *Open.* The kit's other reduction of period four asks that no finite left
  half keep column $-1$ on a pattern with one free reading in four (`C3`, one statement for each word). No left half of
  up to 80 cells does, for each word in each phase ([the left-half statements](findings/columns/left-half-c3.md)), and
  Lean checks, for each word, every half that lies within depth 88 at the time it starts to keep the pattern
  ([LeftHalf0001](Rule30Open/Columns/LeftHalf0001.md) with the kit's lane checker,
  [LeftHalfDriven](Rule30Open/Columns/LeftHalfDriven.md) with the checker extended to a boundary that is not white).
  *Assessment:* the latest failure outlasts the half's length by about a third of it, and the work of a check doubles
  with every four cells, so checks settle bounded cases only; a proof needs an argument that uses the finiteness of the
  half.
- **Period two through the held column.** *Open, hard.* It reduces to an integer map with the shape of a Collatz
  problem ([HeldColumn](Rule30Open/PeriodTwo/HeldColumn.md)); every integer below $2^{52}$ fails
  ([left half alone](findings/period-two/left-half-alone.md)), the kit proves its Q01 for starts of width at most 52,
  against the white right half no left half within depth 32,754 keeps the center alternating, in Lean
  ([WhiteRightHalf](Rule30Open/PeriodTwo/WhiteRightHalf.md), the kit's milestone `CQ01Empty` for those widths), and no
  finite certificate exists in the forms tried ([no certificate](negative-results/period-two/no-finite-certificate.md)).
  The ether-and-wall family cannot give period two: the white right half never enters it, by computation here
  ([the absorption route](negative-results/period-two/absorption-route.md)) and by a Lean proof claimed in the kit's
  pull request #39. Other pull requests work on the gate, from which the kit reconstructs the one candidate left row
  ([the kit's pull requests](literature/kit-pull-requests.md#period-two)).
- **Least period three.** *Open.* The kit reduces it to statements about the left half and closes the ether-and-wall
  route for period three. For $001$ its period-21 trap `t001` remains: every right half white on its first 1,317 cells
  enters it, whatever lies beyond ([HighThree](Rule30Open/Columns/HighThree.md)), and every half of up to ten cells
  enters, but a median of about 16,000 steps in and the latest at step 186,490 ([the
  census](findings/columns/t001-census.md)), so a census in Lean is out of reach. For $011$ the right half never settles
  next to the center, so no trap of that kind appears ([the word 011](negative-results/columns/period-three-011.md)),
  and the route is the kit's left-only statement `C3w`.
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
  at least about $\log n$ times before $n$ (the kit); a black-run slope of $3/5$ and $\log\log$ margins are claimed in
  open pull requests to the kit. Numerically the longest runs are logarithmic. *Assessment:* going below linear needs
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

1. **Attraction for period four.** The Lean classes so far are halves of at most ten cells, a white gap after the sixth
   or the tenth cell, at most two black cells among the first $G$, and the aligned ether cut anywhere with at most four
   cells after it. Next: the shift lemma of [EtherPrefix](Rule30Open/Columns/EtherPrefix.md) applies to any half whose
   column 1 stays the ether's until it enters, so ether prefixes in front of the census halves, or of longer tails, need
   only base checks; three black cells by [SparseRight](Rule30Open/Columns/SparseRight.md)'s route need 32,219 to
   476,314 kernel checks per word and phase; halves of 12 cells by [TenCells](Rule30Open/Columns/TenCells.md)'s route
   need a few minutes of kernel time; and the slowest halves, which are rare and which local and beam searches do not
   find ([the slow-half searches](negative-results/columns/slow-half-search.md)). *Assessment:* each class is thin; a
   proof for every finite half needs an argument that the chaotic part near the center delivers a wall, which none of
   these gives.
2. **Block exclusions.** Blocks with nine 1s in a row now have a uniform argument
   ([WallSets](Rule30Open/Columns/WallSets.md)), which matches the game on every such block to period 16. The open cases
   are blocks without a long run of 1s. All 197 blocks [the game](findings/columns/game-blocks.md) excludes up to period
   16 are kernel-checked, seven of them by [BitGame](Rule30Open/Columns/BitGame.md), which decides the game from the
   block alone, without a certificate; next, extend the game past period 16. Column words without long runs also fix the
   cell beside the column, the shortest being $0110000$, but up to period 20 they exclude no block the game misses
   ([forcing words](negative-results/columns/forcing-words.md)). *Assessment:* every family found so far rests on long
   runs, and a typical block of large period has only short ones, so these exclusions stay thin.
3. **Findings that want a Lean proof.** The seed's past, the census beyond what SparseRight covers, the coin lock and
   the period-two computations ([open work](CATALOG.md#open-work)). The 2-adic trace, the center degree and the Duhamel
   form are proved in the kit's equivalent forms, which a search should include before any formalization
   (`.lake/packages/rule30prize/equivalents/Rule30Equivalents/`).
4. **Track the kit and the literature.** Re-pin the kit when it gains modules, after the build, the audit and the tests
   pass, and move an entry's `kit:` relation when the kit gains its result; keep [the literature](literature/README.md)
   current, AI-proposed claims included ([ai-proposed.md](literature/ai-proposed.md)), and the kit's open pull
   requests ([kit-pull-requests.md](literature/kit-pull-requests.md)) until each is merged or closed.
