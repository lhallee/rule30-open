# rule30-open

An open, checkable effort on the three [Rule 30 Prize](https://rule30prize.org) problems. Every theorem here is
proved in Lean against the prize's official statements and comes with its argument in plain mathematics. Every
computational finding comes with the code that reproduces it. And every approach that failed is written down with
the reason it failed, so the next person can start where it stopped instead of repeating it.

None of the three problems is solved here. [CATALOG.md](CATALOG.md) lists every result: 196 Lean modules with 943
headline theorems, 70 findings and 82 negative results.

## The problems

Rule 30 updates each cell from itself and its two neighbors: the new cell is the left neighbor XOR (the cell OR the
right neighbor). Started from one black cell, its center column begins 1, 1, 0, 1, 1, 1, 0, 0, 1, 1
([OEIS A051023](https://oeis.org/A051023)) and looks random. The prize asks:

1. Does the center column always remain non-periodic?
2. Does each color of cell occur on average equally often in the center column?
3. Does computing the $n$th cell of the center column require at least $O(n)$ computational effort?

The [prize kit](https://github.com/WolframInstitute/Rule30PrizeKit) fixes the formal statements in Lean 4 and collects
partial results. This repository depends on the kit at a pinned commit, states its headline results with the kit's
`Rule30Prize.center`, and marks for each module whether it is new, an independent proof of a kit result, or an
extension of one.

## Where things stand

All three problems are open. Each route toward them ends at a statement that the chaotic part of a Rule 30 row behaves
fairly, and no method here proves such a statement. [ROADMAP.md](ROADMAP.md) gives every route, its status and its
next step; the summary below names the main results and links the entry for each.

### Problem 1: is the center column eventually periodic?

Proved in Lean:

- **Long runs of 1s.** No column of a row with a leftmost black cell is eventually constant, or eventually periodic
  with every run of 1s at least nine long. Several wider families of blocks with runs of nine or more 1s are excluded
  as well ([ROADMAP](ROADMAP.md#problem-1-is-the-center-column-eventually-periodic)).
- **Blocks one at a time.** A finite game excludes 1,400 blocks of period at most 21, hundreds of them beyond the kit
  ([game blocks](findings/columns/game-blocks.md)). An eventual period $P$ after a transient $T$ needs
  $T + P \ge 262{,}125$.
- **Period two.** The kit's hypothesis BWH implies its hypothesis `Q01`
  ([WedgeLadderQ01](Rule30Open/PeriodTwo/WedgeLadderQ01.md)), and one statement about finite left halves,
  `Q01Right(W)`, excludes period two whatever the right half does
  ([ChannelLanguage](Rule30Open/PeriodTwo/ChannelLanguage.md)). Period two also reduces to one integer map
  ([HeldColumn](Rule30Open/PeriodTwo/HeldColumn.md)).
- **Period four.** No finite row whose right half has at most 14 cells has a center repeating a word of period four,
  and no left half within depth 88 keeps the kit's left-half pattern for one.
- **Every period** comes down to one statement about the left half for each block
  ([LeftLatch](Rule30Open/Columns/LeftLatch.md)). Many blocks of period 9 to 15 come down to entry into a trap, while
  entry into 360 other traps alone is false, and so is the kit's own statement of entry into its trap for $001$.
- **Equal center columns.** On the rows supported in $[-A, B]$ the kit's stripe relation, which joins rows with equal
  center columns, has exactly $2^{A+B} + 3 \cdot 2^{A-1}$ classes, none mixing left parts, so those rows have at most
  that many center columns ([StripeClassCount](Rule30Open/Frames/StripeClassCount.md),
  [StripeClasses](Rule30Open/Frames/StripeClasses.md)). If every box $[-A, A]$ reached that count, rows with equal
  center columns would have equal left edges, the kit's `EdgeObservable`, which implies Problem 1; every box of up to
  21 cells reaches it ([center classes](findings/frames/center-classes.md)).
- **The linear barrier, explained.** Under Rules 90 and 150 a column of a finite row is eventually periodic exactly
  when the row is mirror-symmetric about it, so their eventually periodic centers come from the seed's symmetry alone
  ([SymmetricAxes](Rule30Open/Analogs/SymmetricAxes.md)).

Computed: every integer below $2^{63}$ fails the period-two condition of the integer map
([the shift model](findings/period-two/shift-model.md)); every right half of up to 20 cells enters the kit's family
under each period-four word ([the absorption census](findings/columns/absorption-census.md)); no left half of up to 80
cells meets the kit's left-half statement for one ([the left-half statements](findings/columns/left-half-c3.md)).

Where it stops: `Q01` and `Q01Right`, entry into the traps, and attraction into the period-four family are each open,
and in every computation the cells they depend on behave like fair coins.

### Problem 2: does each color occur equally often?

Proved in Lean: no bound on the density. Conditional bounds on runs: if the left diagonals settle by time $3j/2$
and their settled pairs alternate in antiphase a bounded number of times, black runs of the center column have slope
at most 3/13 ([SettledSlope](Rule30Open/Diagonals/SettledSlope.md)), and the point where they start to repeat moves
by a three-case law, so a gain of 2/3 diagonal per step gives that slope
([OnsetEdge](Rule30Open/Diagonals/OnsetEdge.md)).

Computed: density 0.500169 over $2^{22}$ cells; that point gains about 0.75 diagonal per step to depth 200,000; over
every center column the left half allows, black cells grow at a rate near 3/4
([driver density](findings/diagonals/driver-density.md)). From a uniformly random left half, almost surely every center column
the half allows, whatever the right half, has black cells of upper density at most 0.7729, the root of $h(d) = d$
(proved on paper, [the first moment](findings/diagonals/driver-first-moment.md)); the white start is one half of
measure zero.

Where it stops: a proof that the gain is at least 2/3 per step, or that the black rate stays below 1, is open, and
every bound on the black rate contains a positive density for one explicit orbit, Rule 30 beside a cell held black
([the relaxed game](negative-results/diagonals/relaxed-density-game.md)). Random rows satisfy the problem but do not
reach the single cell ([almost every row](negative-results/random-rows/almost-every-row.md)), and invariant measures of
positive entropy need not be uniform: rows moving right at the speed of light form a set of positive entropy, in Lean
([LightLikeEntropy](Rule30Open/RandomRows/LightLikeEntropy.md)).

### Problem 3: does the $n$th cell need about $n$ steps?

Proved in Lean:

- **An upper bound.** A one-tape machine computes $c(n)$ in $2n^2 + 2n \log_2 n + O(n)$ steps
  ([QuadraticTime](Rule30Open/Complexity/QuadraticTime.md)).
- **Lower bounds for a row given as input.** Each is linear in the cone and separates Rule 30 from the linear rules
  such as Rule 90: a decision tree reads at least $2t$ cells ([QueryDepth](Rule30Open/Complexity/QueryDepth.md)); the
  center after $t$ steps has at least $2^{2t-1}$ nonzero Walsh coefficients
  ([ParityLift](Rule30Open/Complexity/ParityLift.md)); the fewest cells that fix it are at most
  $t - 2\lfloor t/9 \rfloor + 2$ ([StripeGrowth](Rule30Open/Complexity/StripeGrowth.md)).
- **Automaticity.** Rule 90's space-time diagram is 2-automatic in two indices, and Rule 30's is not if its right-edge
  cycles grow faster than linearly ([TwoIndex](Rule30Open/Complexity/TwoIndex.md)).
- **Reading the row from the left, for every $t$.** For $a \le 13$ an ordered decision diagram that reads the row from
  the left needs $2^a$ nodes at level $a$ at every $t$ from a threshold on, since white and single black cell
  completions tell the $2^a$ settings of the $a$ leftmost cells apart
  ([LateSeedCut](Rule30Open/Complexity/LateSeedCut.md), [LateSeedCutWide](Rule30Open/Complexity/LateSeedCutWide.md)).

Computed: no automaton under 131,070 states computes the column; linear complexity $n/2$; no learned shortcut.

Where it stops: a lower bound for the single starting cell amounts to an exponential lower bound for one explicit
function ([why it is hard](negative-results/complexity/problem-three-barrier.md)), and the route through a reduction
from a problem hard for exponential time would make the center column constant on infinite sets of times decidable in
polynomial time ([the reduction route](negative-results/complexity/reduction-route.md)); as a space lower bound it sits
between the order $\sqrt{n}$ that Paterson's theorem needs and the $\sqrt{n} \log n$ that tree evaluation uses
([the space ladder](findings/complexity/space-ladder.md)).

## Where to start

[ROADMAP.md](ROADMAP.md) groups every result by route, says which routes are closed and which are open, and lists
the next steps. [CATALOG.md](CATALOG.md#open-work) lists the open work: conjectures to settle, and findings proved on
paper or by computation that still want a Lean proof. Before starting
in a category, read its negative results; each says where an approach stopped and why. [The literature](literature/README.md)
collects what is published around the problems, from Jen's theorem to the claims made since 2019.

## Layout

| Path | What it holds |
|---|---|
| `Rule30Open/<Category>/<Name>.lean` | A Lean module, beside `<Name>.md`, its argument in plain mathematics |
| [`findings/<category>/`](findings/README.md) | Results proved on paper, computed, or conjectured, each with its evidence |
| [`negative-results/<category>/`](negative-results/README.md) | What was tried and did not work, and why |
| [`literature/`](literature/README.md) | The published work around the three problems, by theme, tied to the entries here |
| [`computations/`](computations/README.md) | Python that reproduces the numbers the entries quote |
| `tests/` | Each computation and each computable Lean statement against an independent check |
| [`ROADMAP.md`](ROADMAP.md) | The routes toward each problem, their status, and the next steps |
| [`categories.yaml`](categories.yaml) | The categories, from foundations to complexity |
| [`scripts/catalog.py`](scripts/catalog.py) | Checks every entry and generates [CATALOG.md](CATALOG.md) |

## Check it yourself

Lean 4 (the version in [`lean-toolchain`](lean-toolchain)) with `lake`, and Python 3.12 or later:

```bash
lake build
python scripts/catalog.py audit
pip install -e ".[test]"
python -m pytest
python scripts/catalog.py check
```

`lake build` fetches the prize kit and checks every proof (under a minute after the first build). The audit prints the
axioms of every headline theorem and fails on anything beyond `propext`, `Classical.choice` and `Quot.sound`. The
source contains no `sorry`, `native_decide` or new axiom, which `catalog.py check` enforces. The tests run on your
machine, on a CPU, not in continuous integration, which runs the build, the audit and the catalog check on every push;
the whole suite runs in under a minute ([tests/README.md](tests/README.md)).

## Contributing

Proofs, findings and negative results are all welcome; a well-documented dead end saves the next person weeks. See
[CONTRIBUTING.md](CONTRIBUTING.md) for the entry format and [AGENTS.md](AGENTS.md) for AI agents working here.

## License and citation

Apache-2.0 ([LICENSE](LICENSE)). The prize kit is a separate repository with its own terms and is not copied here.
Cite with [CITATION.cff](CITATION.cff).
