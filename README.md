# rule30-open

An open, checkable effort on the three [Rule 30 Prize](https://rule30prize.org) problems. Every theorem here is
proved in Lean against the prize's official statements and comes with its argument in plain mathematics. Every
computational finding comes with the code that reproduces it. And every approach that failed is written down with
the reason it failed, so the next person can start where it stopped instead of repeating it.

None of the three problems is solved here. [CATALOG.md](CATALOG.md) lists every result: 14 Lean modules with 50
headline theorems, 14 findings and 19 negative results.

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
| 1 | No column of a row with a leftmost black cell is eventually constant, nor eventually periodic with all runs of 1s at least nine long; two blocks of period 8 excluded by a finite game; period 2 reduced to a question about one integer map | The game excludes 76 of 2,538 blocks up to period 14; the integer map fails below $2^{52}$; no row with its leftmost 1 within 120 cells has an alternating center | [Period-four locking](findings/columns/period-four-locking.md), with [a width-16 certificate](findings/columns/period-four-certificate.md) that leaves only attraction open; [the integer map](Rule30Open/PeriodTwo/HeldColumn.md) |
| 2 | Nothing | Density 0.500169 over $2^{22}$ cells; no additive conservation law | None found |
| 3 | Nothing | No automaton under 131,070 states; linear complexity $n/2$; no learned shortcut | [Why it is hard](negative-results/complexity/problem-three-barrier.md) |

## Where to start

[CATALOG.md](CATALOG.md#open-work) lists the open work: conjectures to settle, and findings proved on paper or by
computation that still want a Lean proof. For Problem 1, start from the open leads in the table above. Before starting
in a category, read its negative results; each says where an approach stopped and why.

## Layout

| Path | What it holds |
|---|---|
| `Rule30Open/<Category>/<Name>.lean` | A Lean module, beside `<Name>.md`, its argument in plain mathematics |
| [`findings/<category>/`](findings/README.md) | Results proved on paper, computed, or conjectured, each with its evidence |
| [`negative-results/<category>/`](negative-results/README.md) | What was tried and did not work, and why |
| [`computations/`](computations/README.md) | Python that reproduces the numbers the entries quote |
| `tests/` | Each computation and each computable Lean statement against an independent check |
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
