# rule30-open

An open, checkable effort on the three [Rule 30 Prize](https://rule30prize.org) problems. Every theorem here is
proved in Lean against the prize's official statements and comes with its argument in plain mathematics. Every
computational finding comes with the code that reproduces it. And every approach that failed is written down with
the reason it failed, so the next person can start where it stopped instead of repeating it.

None of the three problems is solved here. [CATALOG.md](CATALOG.md) lists every result: 81 Lean modules with 350
headline theorems, 30 findings and 32 negative results.

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

| Problem | Proved in Lean here | Computed here | Open leads |
|---|---|---|---|
| 1 | No column of a row with a leftmost black cell is eventually constant, nor eventually periodic with all runs of 1s at least nine long, nor with a period $P$ holding a run of $r \ge 9$ 1s with $P - r \le 4 \lfloor r/9 \rfloor$, nor with a period holding nine or more 1s, then $b$ 0s, then at most $4 \lfloor (b - 1)/9 \rfloor + 2$ more steps, nor with a period whose runs of nine or more 1s are separated by segments that a check on the possible three-cell windows beside the column accepts, every such block of period at most 16 the finite game excludes among them, and the families $1^a 0^b 1 0$, $1^a 0 1 1 0^c$, $1^a 0^{2k+3} 1 0 0$ and $1^a 0^{2k+2} 1 0 1 0$ for every $a \ge 9$; two blocks of period 8 excluded by a finite game, 136 more of period 8 to 16, 155 of period 17 and 18, 327 of period 19 and 20 and 303 of period 21 that the kit does not exclude; period 2, and the period-four word $0001$, reduced to questions about one integer map; no finite row whose right half has at most fourteen cells, or is white on cells 7 to 535 or on cells 11 to 654, or has at most two black cells among cells 1 to 1,359, or is the aligned ether cut anywhere and followed by at most six cells, has a center repeating a word of period four, nor one whose right half is white on its first 1,317 cells a center repeating $001$, nor one whose right half is white on cells 9 to 3,058, 1,610 or 2,357 a center repeating $0000010001$, $00000011011$ or $001011100111$; no center repeats $0001$, $0011$ or $0111$ while column 17, 15 or 14 later reads one fixed sequence of 1,193, 955 or 381 values, nor one of 49 other blocks of period at most 12, 16 of them without a run of more than four, while column 14 later reads one fixed sequence for the block, and for 22 of them a column near the center is black at least once in every 27 to 302 steps; no left half within depth 88 keeps the kit's left-half pattern for any period-four word from any time; an eventual period $P$ of the center column after a transient $T$ needs $T + P \ge 262{,}125$; every eventual period of every length comes down to one statement about the left half; 22 of the 56 blocks of period 9, 28 of the 99 of period 10, 71 of the 186 of period 11, 113 of the 335 of period 12, 222 of the 630 of period 13, 385 of the 1,161 of period 14 and 595 of the 2,182 of period 15, and one block each of period 2, 3, 5, 6 and 7, come down to entry into a trap, as the kit's $001$ and period-four words do, and for two of them every right half white on its first 91,129 to 201,172 cells enters, from most phases; against a white right half, no left half within depth 32,754 keeps the center alternating | The game excludes 197 of 8,800 blocks up to period 16, 136 of them beyond the kit, 261 of the 22,242 of period 17 and 18, 508 of the 79,971 of period 19 and 20, and 434 of the 99,858 of period 21; sampled right halves driven by blocks of period 9 to 12 settle into their traps, and every right half of up to four cells into 30 of the 35 that no wall carries; the integer map fails below $2^{52}$; no row with its leftmost 1 within 120 cells has an alternating center; every right half of up to 20 cells enters the kit's ether-and-wall family under each period-four word, and no left half of up to 80 cells meets the kit's left-half statement for one, nor one of 37 to 100 cells the left-half statement of any block of period 3, 5, 6, 7 or 9; against a white right half no left half of fewer than a million cells keeps the center alternating | [Period-four locking](findings/columns/period-four-locking.md), with [a width-16 certificate](findings/columns/period-four-certificate.md), [the absorption census](findings/columns/absorption-census.md) and [a fair coin beyond it](findings/columns/coin-lock.md) that leave only attraction open; [the kit's left-half statements](findings/columns/left-half-c3.md), [every block's](findings/columns/left-half-every-block.md); [the white right half](findings/period-two/white-right-half.md); [the integer map](Rule30Open/PeriodTwo/HeldColumn.md); [lock chains](findings/columns/lock-chains.md), which read every lock found, the kit's wall and its trap for $001$ as one lock carried leftward |
| 2 | Nothing | Density 0.500169 over $2^{22}$ cells; no additive conservation law | None found; [random rows do not reach the single cell](negative-results/random-rows/almost-every-row.md) |
| 3 | Nothing | No automaton under 131,070 states; linear complexity $n/2$; no learned shortcut | [Why it is hard](negative-results/complexity/problem-three-barrier.md); [as a space lower bound](findings/complexity/space-ladder.md), between the order $\sqrt{n}$ that Paterson's theorem needs and the $\sqrt{n} \log n$ that tree evaluation uses; and why [hypotheses about satisfiability](negative-results/complexity/hardness-hypotheses.md) do not change it |

## Where to start

[ROADMAP.md](ROADMAP.md) groups every result by route, says which routes are closed and which are open, and lists
the next steps. [CATALOG.md](CATALOG.md#open-work) lists the open work: conjectures to settle, and findings proved on
paper or by computation that still want a Lean proof. For Problem 1, start from the open leads in the table above. Before starting
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
source contains no `sorry`, `native_decide` or new axiom, which `catalog.py check` enforces. Continuous integration
runs all of these on every push.

## Contributing

Proofs, findings and negative results are all welcome; a well-documented dead end saves the next person weeks. See
[CONTRIBUTING.md](CONTRIBUTING.md) for the entry format and [AGENTS.md](AGENTS.md) for AI agents working here.

## License and citation

Apache-2.0 ([LICENSE](LICENSE)). The prize kit is a separate repository with its own terms and is not copied here.
Cite with [CITATION.cff](CITATION.cff).
