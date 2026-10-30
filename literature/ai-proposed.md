# Results proposed by AI systems, and what they bear on

In 2025 and 2026 AI systems produced, or helped produce, a large body of claimed results in mathematics and
theoretical computer science. This file collects those whose subject is near the three problems, says what each claims,
and says whether it opens a route here. Every item is a claim: the collections below say themselves that their results
are at different stages of verification, and none is refereed unless stated. The work of agents on the prize itself is
in [rule-30.md](rule-30.md#work-on-the-prize-problems-since-2019).

The search found three AI-proposed results about cellular automata: one on nonsofic groups (family 197 below) and two
OEIS conjectures proved by formal proof search, one of them on the center column of rule 167 (Other claims). It found
one about the pseudorandomness of an explicit sequence, the Liouville function (family 007), and none about normal
numbers or 2-adic maps. The items below are the nearest ones, and the bearing of each is assessed against the routes in
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
  - **007, two-point Chowla.** For the Liouville function $\lambda$, the correlation $\sum_{n \le X} \lambda(a n + b)
    \lambda(c n + d)$ along fixed nonproportional affine forms is $O(X / (\log X)^{c})$ for an absolute $c > 0$.
  - **136, a quasilinear PCP for PPAD.** End-of-Line instances of length $N$ reduce to numerical constraints of
    length $N (\log N)^{O(1)}$ that tolerate a fixed fraction of violations.
  - **137, one-tape machines in less space.** A one-tape machine's run of $T$ steps is decided in space
    $O(T^{2/5} \log^{C} T)$, below Paterson's $T^{1/2}$ of 1972.
  - **145 and 146, ergodic theory.** Every invertible mixing transformation is mixing of all orders (Rokhlin's
    problem), and the standard map has positive metric entropy for all large parameters.
  - **154, multiple ergodic averages.** Almost-everywhere convergence of consecutive multiple ergodic averages for
    invertible mixing transformations.
  - **197, surjunctivity.** A finitely presented torsion-free nonsofic group whose group algebra over GF(2) is not
    directly finite, and from the same elements an injective cellular automaton on that group that is not surjective,
    against Gottschalk's surjunctivity conjecture.
  - **155, periodic tiling.** A finite tile of $\mathbb{Z}^3$ that tiles space but admits no periodic tiling.
  - **076, flat binary polynomials.** Polynomials with $N$ coefficients in $\{-1, 1\}$ whose modulus is
    $(1 + o(1))\sqrt{N}$ on the whole unit circle, so binary merit factors that tend to infinity, against Turyn's
    conjecture.
  - **179, Barker sequences.** Real circulant Hadamard matrices exist only in orders 1 and 4, so binary sequences whose
    nontrivial aperiodic autocorrelations are at most 1 in magnitude exist, beyond length 1, only at lengths 2, 3, 4,
    5, 7, 11 and 13.
  - **127, 132 and 192, measures of Boolean functions.** Average sensitivity at most $8d\sqrt{n}$ for polynomial
    threshold functions of degree $d$; total functions whose block sensitivity exceeds a power above 2 of their
    sensitivity; and functions whose linear Fourier weight exceeds any constant times the square root of their
    degree.

  *Here:* 137 is the nearest to a route: Paterson's theorem turns the kit's Problem 3 into a space lower bound of order
  $\sqrt{n}$ for the center column, and 137 would lower that to $n^{2/5}$ up to logarithms, a polynomial factor below
  the space $O(\sqrt{n} \log n)$ that tree evaluation uses ([the space ladder](../findings/complexity/space-ladder.md));
  no such space lower bound is known either. 007 is the nearest result to Problem 2: the one-point statement for
  $\lambda$, that its values average to zero, is the prime number theorem, and 007 proves a two-point statement, while
  for $c$ the one-point statement is Problem 2 itself. Results of this kind rest on multiplicativity,
  $\lambda(pn) = -\lambda(n)$, which ties the sequence at one scale to another; no identity of that kind is known for
  $c$ ([the exact structure searches](../negative-results/structure/linear-relations.md)). 136 strengthens probabilistic
  checking, which bears on verifying a computation, not on computing $c$ ([probabilistic
  checking](../negative-results/complexity/probabilistic-checking.md)). 145 and 146 concern almost every point, as 154
  does. 102 and 378 are the subject of [the hardness hypotheses](../negative-results/complexity/hardness-hypotheses.md),
  which explains why neither decides Problem 3; 378's lower bounds are for nondeterministic exponential time, not for an
  explicit function such as the center column. 112 is a lower bound for one constructed language in a restricted circuit
  model; the same model for the center column would ask for lower bounds on $c(n)$ as a function of the digits of $n$,
  about which nothing structural is known. 129 concerns automata on growing alphabets; an automaton that reads the
  digits of $n$ and computes $c(n)$, the model of [the automaton
  search](../negative-results/complexity/automaton-lower-bounds.md), is one-way or two-way equivalently, since both
  recognize the regular languages. 005 and 017 are irrationality results of the kind Problem 1 is, in its 2-adic form
  ([the 2-adic trace](../findings/frames/two-adic-trace.md)), but their methods use analytic structure that the center
  column is not known to have. 103 and 154 bear on no route here: the first concerns space-bounded randomness, the
  second almost every point, while the problems concern one point ([the random-row
  barrier](../negative-results/random-rows/almost-every-row.md)). 197 concerns groups that are not sofic; Rule 30 lives
  on the integers, which are amenable, where the Garden of Eden theorem makes every injective automaton onto, and Rule
  30 is onto and not injective (the kit's equivalent forms, `Preimages`). 155 is about tile sets that force every tiling
  to be aperiodic, while Problem 1 asks about one column of one orbit, which no local rule forces: Rules 90 and 150
  share every structural fact the kit's argument uses and have eventually constant center columns (the kit's
  `Rule30Realization`). 179 settles short words with tiny autocorrelations and 076 builds long words with flat spectra;
  the center column's autocorrelations are of the size of a random sequence's (the kit's `Autocorrelation`, [the
  randomness tests](../negative-results/statistics/randomness-tests.md)). For 127, 132 and 192: the center cell after
  $t$ steps, as a function of its $2t + 1$ initial cells, has degree $2t - 1$ and flips with its leftmost cell (the
  kit's `AlgebraicDegree`, `QueryComplexity`), so these measures are near their maximum for it, and the problems concern
  its value on the single cell, which they do not see.

## Other claims

- **Anthropic (2026).** [A 2^o(n) time algorithm for 3-SAT](https://github.com/anthropics/formal-math/pull/31). Paper
  and Lean 4 formalization in the repository anthropics/formal-math, merged October 27, 2026. Claims one deterministic
  machine counting the satisfying assignments of $k$-CNF formulas on $n$ variables in time $2^{o(n)}$, for every $k$:
  $2^{O(\min\{k^2 n \log\log n / \sqrt{\log n},\ k m / \sqrt{\log m}\})}$ steps for $m$ clauses, as the repository's
  index states it. Also in [complexity.md](complexity.md#satisfiability-and-unique-games). The same repository holds
  Lean formalizations of two human results, on simple zeros of the Riemann zeta function on the critical line and on
  faster 3SUM and all-pairs shortest paths on a word RAM; neither bears on the problems. *Here:* [the hardness
  hypotheses](../negative-results/complexity/hardness-hypotheses.md).

- **Google DeepMind (2026).** [formal-conjectures](https://github.com/google-deepmind/formal-conjectures), the
  conjectures marked solved with a formal proof found by the methods of G. Tsoukalas et al., *Advancing Mathematics
  Research with AI-Driven Formal Proof Search*, arXiv:2605.22763 (the paper's text was not read), the system reported
  as AlphaProof Nexus, whose proofs are in
  [alphaproof-nexus-results](https://github.com/google-deepmind/alphaproof-nexus-results); that repository's index
  groups them as additive combinatorics, algebraic geometry, graphs, optimization, quantum optics, Erdős problems, OEIS
  conjectures and the Stacks Project, and names no other problem on cellular automata. By the search record (the problem
  page, erdosproblems.com, is outside this session's network), one of its nine Erdős problems is #125: the sums of a
  number whose base-3 digits are 0 and 1 and a number whose base-4 digits are 0 and 1 have lower density zero, by
  Diophantine approximation with the irrationality of $\log 4 / \log 3$. A density statement about digits, the kind
  Problem 2 asks; it rests on two multiplicatively independent bases, a structure the center column is not known to
  have. On October 29, 2026,
  38 entries of the repository cite it: 36 conjectures from the OEIS, one Erdős problem and one from *Written on the
  Wall II*. Two concern cellular automata: [A300997](https://oeis.org/A300997), on an automaton that redistributes mass,
  and [A267581](https://oeis.org/A267581), the center column of the elementary rule 167 from a single black cell, whose
  recurrence $a(n) = 2a(n - 1) + 1 - [\,n \mid 2^{n+1}]$ says that from time 2 on the column is black except at the
  powers of two. *Here:* rule 167 is an elementary automaton whose center column is not eventually periodic and yet
  2-automatic, so the analog of Problem 1 holds while that of Problem 3 fails: a finite automaton reads the cell at time
  $n$ from the binary digits of $n$. For Rule 30 the kit proves that Problem 3 implies the column is not 2-automatic,
  and no automaton with fewer than 131,070 states fits its first $2^{22}$ cells ([the automaton
  search](../negative-results/complexity/automaton-lower-bounds.md)); rule 167's column follows its nested pattern,
  which Rule 30 does not have. The same repository states Prize Problems 1 and 2 in Lean as open
  ([rule-30.md](rule-30.md#the-prize-and-its-formal-statements)).

## Checked records, texts not read

- **Chang (2026).** *Exploring Collatz Dynamics with Human-LLM Collaboration.* arXiv:2603.11066, several versions in
  March 2026; the record was seen through a search, the text was not read, and two sites that summarize it are outside
  this session's network. By the record, a sharpened structural reduction of the Collatz conjecture, written with an
  LLM, that ends at an unproved condition it calls the Carry Independence Conjecture, with no cycle of period at most 13
  checked by computer over 238,811 words. It does not claim a proof. *Here:* period two reduces to an integer map with
  the shape of a Collatz problem ([HeldColumn](../Rule30Open/PeriodTwo/HeldColumn.md)), but that map,
  $H(U) = (U \gg 1) \oplus (U \lor (U \ll 1))$, is Rule 30 itself on the bits of $U$ and has no carries, so a condition
  on the carries of $3n + 1$ has no counterpart there; the computer checks are of the kind of [the left-half
  census](../findings/period-two/left-half-alone.md), where every integer below $2^{52}$ fails.

- **Georgiev, Gómez-Serrano, Tao and Wagner (2025).** *Mathematical exploration and discovery at scale.*
  arXiv:2511.02864; the record was seen through a search, the text was not read. Reports an LLM-guided evolutionary
  search (AlphaEvolve) on 67 problems in analysis, combinatorics, geometry and number theory, matching most known
  constructions and improving several. A method rather than a result; searches for finite certificates here
  ([the coin-lock finding](../findings/columns/coin-lock.md), [the finite game](../findings/columns/game-blocks.md)) are
  of the same constructive kind.
