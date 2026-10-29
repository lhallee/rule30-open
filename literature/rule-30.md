# Rule 30 and the prize

Sources about Rule 30 itself: the prize and its formal statements, the papers and book that introduced the rule, the
published data, the known structure of its pattern, and the work on the prize problems since 2019. Each entry gives the
source, what it establishes, and where it bears on this repository.

## The prize and its formal statements

- **Wolfram (2019).**
  [Announcing the Rule 30 Prizes](https://writings.stephenwolfram.com/2019/10/announcing-the-rule-30-prizes/).
  Stephen Wolfram Writings, October 1, 2019.
  Poses the three problems. Notes that reaching step $n$ by direct simulation takes about $n^2$ cell updates, that the
  center column shows no period in its first billion cells, and that a 1986 result of Jen says no two columns can both
  become periodic, which does not settle a single column.
  *Here:* the problems as [the README](../README.md) states them; Jen's result is
  [the adjacent-column theorem](../Rule30Open/Columns/AdjacentColumns.md).
- **The Rule 30 Prizes.** [rule30prize.org](https://rule30prize.org).
  The official rules: $10,000 for each problem, awarded for the first complete proof the committee accepts, with code
  and data for any computation. The site lists no winner. Its [bibliography](https://rule30prize.org/bibliography/)
  holds 29 sources from 1983 to 2019.
- **The Rule 30 Prizes (2026).** [Instructions for agents](https://www.wolframcloud.com/obj/rule-30-prize/Agents/).
  Invites AI agents to work on the problems by computing, proving in Lean and writing an essay. A Lean submission goes
  in the kit's `Rule30Submission.lean` and is checked by its `Check.lean`; entries carry statuses from unverified to
  human-verified.
- **Wolfram Institute.** [Rule30PrizeKit](https://github.com/WolframInstitute/Rule30PrizeKit).
  The reference Lean environment for submissions: the official `Problem1` and `Problem2`, three versions of Problem 3
  for a fixed one-tape machine model, and a library of partial results in core Lean (`lean/`). A second part,
  `equivalents/`, proves in Lean with Mathlib 52 of 54 catalogued equivalent forms of Problem 1, as 163 theorems named
  `problem1_iff_*`, equivalent forms of Problem 2, the implication from Problem 3 to Problem 1, and results on random
  configurations, the algebraic degree of the center cell, Duhamel's formula and the 2-adic frame.
  *Here:* the repository depends on the kit at a pinned commit, and every Lean entry says whether its result is new to
  the kit; every finding the kit proves says so (`formalization: kit`).
- **Google DeepMind.**
  [formal-conjectures: `FormalConjectures/Other/Rule30.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Other/Rule30.lean).
  Problems 1 and 2 as open Lean statements, with the first center cells checked by computation; Problem 3 is left out
  because it depends on a model of computation. The kit's statements match these.

## The papers and the book that introduced the rule

- **Wolfram (1983).** [Statistical mechanics of cellular automata](https://doi.org/10.1103/RevModPhys.55.601).
  *Reviews of Modern Physics* 55(3), 601 to 644.
  Elementary cellular automata studied as statistical systems.
- **Wolfram (1984).** [Universality and complexity in cellular automata](https://doi.org/10.1016/0167-2789(84)90245-8).
  *Physica D* 10(1 to 2), 1 to 35.
  The four classes of behavior of one-dimensional automata.
- **Wolfram (1985).** [Origins of randomness in physical systems](https://doi.org/10.1103/PhysRevLett.55.449).
  *Physical Review Letters* 55(5), 449 to 452.
  Argues that random-looking behavior can arise from the dynamics of a simple nonlinear system without random input.
- **Wolfram (1986).** [Random sequence generation by cellular automata](https://doi.org/10.1016/0196-8858(86)90028-X).
  *Advances in Applied Mathematics* 7(2), 123 to 169.
  Studies a one-dimensional automaton whose time sequences look random, later identified as Rule 30, and proposes it as
  a random sequence generator. The cryptographic proposal of the same period is in [complexity.md](complexity.md).
- **Wolfram (2002).** [*A New Kind of Science*](https://www.wolframscience.com/nks/). Wolfram Media, ISBN 1-57955-008-8.
  Introduces Rule 30 from a single cell on page 27. Page 317 says Mathematica's `Random[Integer]` produces its bits from
  Rule 30's center column. The notes to page 871 give the center column and the periods of the diagonals.
  *Here:* [the left side's memory](../Rule30Open/Diagonals/LeftMemory.md) cites those notes.

## Data

- **OEIS.** [A051023](https://oeis.org/A051023), the center column from a single cell, and
  [A094605](https://oeis.org/A094605), the period of the $n$th diagonal from the right.
  *Here:* the Lean foundations check the first ten center cells against A051023; the kit's `Rule30RightPeriods` studies
  the periods of A094605.
- **Wolfram Research (2017).**
  [A Million Bits of the Center Column of the Rule 30 Cellular Automaton](https://doi.org/10.24097/wolfram.25316.data).
  Wolfram Data Repository.
- **Wolfram Research (2019).**
  [A Billion Bits of the Center Column of the Rule 30 Cellular Automaton](https://datarepository.wolframcloud.com/resources/A-Billion-Bits-of-the-Center-Column-of-the-Rule-30-Cellular-Automaton).
  Wolfram Data Repository. The largest published computation of the center column found in the search.
  *Here:* [the randomness tests](../negative-results/statistics/randomness-tests.md) use $2^{22}$ cells computed here.

## The structure of the pattern

- **Jen (1986).** [Global properties of cellular automata](https://doi.org/10.1007/BF01010579).
  *Journal of Statistical Physics* 43(1), 219 to 242.
  The source the kit and the prize announcement cite for Jen's theorem that no two columns of the single cell's pattern
  are both eventually periodic (the kit's `Rule30Jen.jen`). Jen's 1990 paper on aperiodicity is in
  [columns.md](columns.md).
  *Here:* [the adjacent-column theorem](../Rule30Open/Columns/AdjacentColumns.md) proves the adjacent case for every row
  with a leftmost black cell.
- **Rowland (2006).** [Local nested structure in rule 30](https://doi.org/10.25088/ComplexSystems.16.3.239).
  *Complex Systems* 16(3), 239 to 258.
  At rows $2^n$, part of the initial row reappears on the right, because the rule can be run backward while the right
  part of each row stays white. Proves Wolfram's observation that the periods of the left diagonals double.
  *Here:* [the left side's memory](../Rule30Open/Diagonals/LeftMemory.md) and
  [the left records](../findings/diagonals/left-records.md).
- **Nersissian (2026).** [Diagonal periods and Newton supports of Rules 30, 86 and 135](https://arxiv.org/abs/2609.25077).
  arXiv:2609.25077.
  The least diagonal periods of Rule 30's single-seed cone are unbounded in both directions, and at depth $m$ the period
  is at least $\lfloor m/2 \rfloor + 1$; Rule 135's orbit is a translated complement of Rule 30's after one step.
  *Here:* the kit proves a lower bound of the same kind in Lean (`Rule30RightPeriods.period_gt`); see also
  [the diagonals category](../CATALOG.md#diagonals).
- **Nersissian (2026).** [Diagonal bases and diagonal periods of elementary cellular automata](https://arxiv.org/abs/2609.25078).
  arXiv:2609.25078.
  Classifies the elementary rules whose diagonal families form bases in every finite window (24 rules), and gives
  Fibonacci bounds on interpolation order and on prime-modulus periods for a polynomial construction from Rule 30.

## Work on the prize problems since 2019

None of the following is refereed, and the prize site lists no winner.

- **Das (2022).** [Rule 30: Solving the chaos](https://arxiv.org/abs/2207.13237). arXiv:2207.13237.
  Claims an analytical solution of Problem 1. No refereed version was found.
- **Chan-López and Martín-Ruiz (2026).**
  [Symmetric nonlinear cellular automata as algebraic references for Rule 30](https://arxiv.org/abs/2604.00165).
  arXiv:2604.00165.
  Proves a closed form over $\mathbb{F}_2$ for the single-seed rows of Rule 22 and uses Rule 22 as a symmetric reference
  for Rule 30: the difference in row support sizes is compared with a power law empirically, and a mechanism for the
  apparent randomness of Rule 30's center column is proposed. It claims no result on non-periodicity.
- **Condrey (2026).** [Finite configurations cannot generate a constant trace in Rule
  30](https://arxiv.org/abs/2609.09431). arXiv:2609.09431. For each right half, finds the unique left half that keeps
  the center column constant, and concludes that no column of a nonzero finite Rule 30 orbit is eventually constant.
  *Here:* that conclusion is proved in Lean for every row with a leftmost black cell ([the adjacent-column
  theorem](../Rule30Open/Columns/AdjacentColumns.md), `no_constant_column`), and the kit proves it for every
  configuration with a leftmost black cell (`Rule30FiniteConfigs.no_column_eventually_constant`). The same unique left
  half is the object of [the white right half](../findings/period-two/white-right-half.md) for the alternating center.
- **Adler (2026).** [rule30-constant-column-lean](https://github.com/keithadler/rule30-constant-column-lean). A Lean 4
  proof, in core Lean with the standard axioms, that no nonzero configuration supported on $[-A, A]$ keeps its center
  column constant at every time $t \le A + 2$ (`no_const_column`). The README reports that a SAT search finds $A + 2$
  to be the first impossible horizon for every $A \le 24$, and presents the proof as an independent formalization of
  the horizon bound of Condrey (2026). *Here:* that bound concerns constancy from time 0; [the adjacent-column
  theorem](../Rule30Open/Columns/AdjacentColumns.md) (`no_constant_column`) excludes constancy from any time on, for
  every row with a leftmost black cell, as the kit's `Rule30FiniteConfigs.no_column_eventually_constant` does.
- **Agents on the prize kit (2026).** [Rule30PrizeKit](https://github.com/WolframInstitute/Rule30PrizeKit), its main
  branch and [pull requests](https://github.com/WolframInstitute/Rule30PrizeKit/pulls). After the agents' invitation,
  the kit's catalog grew from 128 modules on October 26, 2026 to 141 on October 28, with contributed modules that are
  proved in Lean on the kit's main branch. Among them: `Rule30LocalConservation` and `Rule30ProductParity` (every
  density or product parity conserved over four steps is a constant plus a coboundary, at every window width),
  `Rule30ArbitraryWhitePadding` and `Rule30WhitePaddingMixtures` (a center column cannot eventually repeat a block
  followed by enough white cells, with a threshold exponential in the block's length), `Rule30AgedLeftDiagonals`,
  `Rule30FrozenRuler` and `Rule30EdgeStaircases` (structure near the two edges of the pattern),
  `Rule30SpatialPeriodLifting` and `Rule30DelayedDefectPeriods`. Its 21 open pull requests claim more, among them a Lean
  proof that the ether-and-wall family cannot give period two (#39), exclusions of every eventual period whose white
  runs are all long (#36, #43), and $\log\log$ margins for runs of the center column (#46); they are summarized, by
  route, in [kit-pull-requests.md](kit-pull-requests.md). The kit's own status table puts least period 4 at its open
  `Absorption`, period 2 at the open Q01, and any eventual period at $T + P \ge 16{,}359$. *Here:* the repository is
  pinned at the kit's commit 932cf8d, so the merged modules count as kit results; an open pull request counts as a
  claim. [The roadmap](../ROADMAP.md) tracks where they meet the routes here, and [a window of 65,536
  cells](../Rule30Open/Columns/LongWindow.md) raises the last bound to $T + P \ge 65{,}518$.
- Faster simulation of the whole pattern, and Boolean functions computed by Rule 30's orbits, are in
  [complexity.md](complexity.md). Results proposed by AI systems outside the prize are in
  [ai-proposed.md](ai-proposed.md).
