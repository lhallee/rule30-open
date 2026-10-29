# Results proposed by AI systems, and what they bear on

In 2025 and 2026 AI systems produced, or helped produce, a large body of claimed results in mathematics and
theoretical computer science. This file collects those whose subject is near the three problems, says what each claims,
and says whether it opens a route here. Every item is a claim: the collections below say themselves that their results
are at different stages of verification, and none is refereed unless stated. The work of agents on the prize itself is
in [rule-30.md](rule-30.md#work-on-the-prize-problems-since-2019).

The search found no AI-proposed result about cellular automata, normal numbers, 2-adic maps or the pseudorandomness
of an explicit sequence. The items below are the nearest ones, and the bearing of each is assessed against the routes in
[the roadmap](../ROADMAP.md).

## OpenAI's manuscript collection

- **OpenAI (2026).** [Mathematics manuscript collection](https://github.com/openai/math/blob/main/CONTENTS.md).
  The repository openai/math, with 721 manuscripts in 373 result families, some with Lean formalizations of the main
  theorem. The families nearest to this repository:
  - **102, the Unique Games Conjecture.** A deterministic polynomial-time reduction from 3-SAT to unique games with
    completeness $1 - \varepsilon$ and soundness $\delta$, for every fixed $\varepsilon, \delta \in (0, 1/2)$.
  - **378, a disproof of the Exponential Time Hypothesis.** A deterministic algorithm that counts the satisfying
    assignments of a $k$-CNF with $n$ variables and $m$ clauses in time
    $(n + m)^{O_k(1)}\, 2^{n / (\log n)^{1/2 + o(1)}}$, and from it superlinear circuit lower bounds for a language in
    $\mathrm{E}^{\mathrm{NP}}$ on infinitely many input lengths.
  - **103, $\mathrm{L} = \mathrm{RL} = \mathrm{BPL}$.** Every bounded-error randomized logarithmic-space decider becomes
    a deterministic one.
  - **112, depth-three circuits.** A language in deterministic polynomial time whose $n$-bit membership function needs
    $2^{\omega(\sqrt{n})}$ gates in unbounded fan-in OR-AND-OR circuits.
  - **129, two-way automata.** Exponential state lower bounds for complementing two-way nondeterministic automata and
    for simulating one-way nondeterministic automata by two-way deterministic ones.
  - **005 and 017, irrationality.** The irrationality of Catalan's constant, and irrationality exponent 2 for $\pi$.
  - **154, multiple ergodic averages.** Almost-everywhere convergence of consecutive multiple ergodic averages for
    invertible mixing transformations.

  *Here:* 102 and 378 are the subject of [the hardness hypotheses](../negative-results/complexity/hardness-hypotheses.md),
  which explains why neither decides Problem 3; 378's lower bounds are for nondeterministic exponential time, not for
  an explicit function such as the center column. 112 is a lower bound for one constructed language in a restricted
  circuit model; the same model for the center column would ask for lower bounds on $c(n)$ as a function of the digits of
  $n$, about which nothing structural is known. 129 concerns automata on growing alphabets; an automaton that reads the
  digits of $n$ and computes $c(n)$, the model of [the automaton search](../negative-results/complexity/automaton-lower-bounds.md),
  is one-way or two-way equivalently, since both recognize the regular languages. 005 and 017 are irrationality results
  of the kind Problem 1 is, in its 2-adic form ([the 2-adic trace](../findings/frames/two-adic-trace.md)), but their
  methods use analytic structure that the center column is not known to have. 103 and 154 bear on no route here: the
  first concerns space-bounded randomness, the second almost every point, while the problems concern one point
  ([the random-row barrier](../negative-results/random-rows/almost-every-row.md)).

## Other claims

- **Anthropic (2026).** [A 2^o(n) time algorithm for 3-SAT](https://github.com/anthropics/formal-math/pull/31).
  Paper and Lean 4 formalization in the repository anthropics/formal-math, merged October 27, 2026. Claims one
  deterministic machine counting the satisfying assignments of $k$-CNF formulas on $n$ variables in time $2^{o(n)}$,
  for every $k$. Also in [complexity.md](complexity.md#satisfiability-and-unique-games).
  *Here:* [the hardness hypotheses](../negative-results/complexity/hardness-hypotheses.md).

## Checked records, texts not read

- **Georgiev, Gómez-Serrano, Tao and Wagner (2025).** *Mathematical exploration and discovery at scale.*
  arXiv:2511.02864; the record was seen through a search, the text was not read. Reports an LLM-guided evolutionary
  search (AlphaEvolve) on 67 problems in analysis, combinatorics, geometry and number theory, matching most known
  constructions and improving several. A method rather than a result; searches for finite certificates here
  ([the coin-lock finding](../findings/columns/coin-lock.md), [the finite game](../findings/columns/game-blocks.md)) are
  of the same constructive kind.
