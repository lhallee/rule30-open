# Problem 3, prediction, and Rule 30 as a cipher

Problem 3 asks whether the $n$th center cell needs effort of order $n$. This file collects what is known about the cost
of computing Rule 30, the hardness results proved for other automata, the general lower-bound landscape a proof would
have to enter, and the cryptanalysis of Rule 30 as a pseudorandom generator. [The Problem 3 barrier](../negative-results/complexity/problem-three-barrier.md)
explains why an affirmative answer is beyond current complexity theory; the sources below are its context.

## The cost of computing Rule 30

- **Wolfram (2019).** [Announcing the Rule 30 Prizes](https://writings.stephenwolfram.com/2019/10/announcing-the-rule-30-prizes/).
  Reaching step $n$ by direct simulation takes about $n^2$ cell updates; Problem 3 asks whether anything essentially
  faster exists for the center cell.
- **Natal and Al-saadi (2024).** [Fast simulation of cellular automata by self-composition](https://arxiv.org/abs/2409.07065).
  arXiv:2409.07065.
  Composing a rule with itself reaches generation $n$ of the whole configuration in time $O(n^2 / \log n)$ and space
  $O(n^2 / (\log n)^3)$, with experiments on Rule 30. It concerns whole rows, not single cells, and gives no lower
  bound.
  *Here:* the barrier entry notes that a random-access machine with unit-cost bitwise operations computes $c(n)$ in
  $O(n)$ operations, so the machine model matters to the question.
- **Castronuovo, Dennunzio and Margara (2026).**
  [Computing functions through the orbits of dynamical systems: the case of cellular automata](https://arxiv.org/abs/2610.34096).
  arXiv:2610.34096.
  Studies automata whose cells carry Boolean functions of input variables, separates universal from non-universal rules
  by algebraic and dynamical criteria, and reports that simple initial rows of Rule 30 generate every Boolean function
  of up to five variables, which suggests, without proof, universality in this sense.
  *Here:* the barrier entry names a proof that Rule 30 can simulate arbitrary computation as one route to Problem 3.

## Computational irreducibility and coarse prediction

- **Wolfram (1985).** [Undecidability and intractability in theoretical physics](https://doi.org/10.1103/PhysRevLett.54.735).
  *Physical Review Letters* 54(8), 735 to 738.
  Treats physical processes as computations and argues that cellular automata give concrete questions that are
  undecidable or computationally intractable.
- **Israeli and Goldenfeld (2004).**
  [Computational irreducibility and the predictability of complex physical systems](https://doi.org/10.1103/PhysRevLett.92.074105).
  *Physical Review Letters* 92, 074105; [arXiv:nlin/0309047](https://arxiv.org/abs/nlin/0309047).
  Coarse-grained elementary automata reproduce the large-scale behavior of many rules, including one capable of
  universal computation, so a system can be irreducible cell by cell and still predictable at a coarser scale.
- **Israeli and Goldenfeld (2006).**
  [Coarse-graining of cellular automata, emergence, and the predictability of complex systems](https://doi.org/10.1103/PhysRevE.73.026203).
  *Physical Review E* 73, 026203; [arXiv:nlin/0508033](https://arxiv.org/abs/nlin/0508033).
  The full study across the elementary rules. Rule 30 is among the few rules the authors could not coarse-grain.
  *Here:* [coarse-graining](../negative-results/structure/coarse-graining.md) searches for a coarse-graining of Rule 30
  directly. Problem 3 concerns exact cells, which coarse predictability does not touch.

## Hardness of predicting other automata

- **Cook (2004).** [Universality in elementary cellular automata](https://doi.org/10.25088/ComplexSystems.15.1.1).
  *Complex Systems* 15(1), 1 to 40.
  Proves that Rule 110 is computationally universal.
- **Neary and Woods (2006).** [P-completeness of cellular automaton Rule 110](https://doi.org/10.1007/11786986_13).
  ICALP 2006, *Lecture Notes in Computer Science* 4051, 132 to 143.
  Predicting Rule 110 for $t$ steps is P-complete, because Rule 110 simulates Turing machines with polynomial
  overhead. It is the strongest prediction-hardness result for an elementary rule that the search found, and it is not
  about Rule 30.
- **Moore (1997).** [Majority-vote cellular automata, Ising dynamics, and P-completeness](https://doi.org/10.1023/B:JOSS.0000015172.31951.7b).
  *Journal of Statistical Physics* 88(3 to 4), 795 to 805; [arXiv:cond-mat/9701118](https://arxiv.org/abs/cond-mat/9701118).
  Majority-vote automata in three or more dimensions embed logic gates, so predicting them is P-complete.

## The lower-bound landscape

A positive answer to Problem 3 is a lower bound for one explicit function, which complexity theory cannot yet give for
any natural function in exponential time (see the barrier entry).

- **Hartmanis and Stearns (1965).** [On the computational complexity of algorithms](https://doi.org/10.1090/S0002-9947-1965-0170805-7).
  *Transactions of the American Mathematical Society* 117, 285 to 306.
  The origin of time complexity classes and of the question whether irrational algebraic numbers can be generated in
  real time, an open question of the same flavor as Problem 3.
- **Adamczewski, Cassaigne and Le Gonidec (2016).**
  [On the computational complexity of algebraic numbers: the Hartmanis-Stearns problem revisited](https://arxiv.org/abs/1601.02771).
  arXiv:1601.02771.
  Answers the Hartmanis-Stearns question for restricted machines: multistack machines, deterministic pushdown automata,
  which cannot produce such expansions, and tag machines.
- **Paterson (1972).** [Tape bounds for time-bounded Turing machines](https://doi.org/10.1016/S0022-0000(72)80017-5).
  *Journal of Computer and System Sciences* 6(2), 116 to 124; the record and abstract were checked through catalog
  entries, the text was not read.
  A language recognized by a one-tape machine, even a nondeterministic one, in time $T(n) \ge n^2$ is recognized by a
  deterministic machine in space $T(n)^{1/2}$. One tape is the kit's model for Problem 3.
  *Here:* [the space ladder](../findings/complexity/space-ladder.md): the kit's `Problem3` follows if the center
  column needs space larger than order $\sqrt{n}$.
- **Hopcroft, Paul and Valiant (1977).** [On time versus space](https://doi.org/10.1145/322003.322015).
  *Journal of the ACM* 24(2), 332 to 337.
  Multitape time $t$ can be simulated in space about $t / \log t$.
- **Cook and Mertz (2024).** [Tree evaluation is in space O(log n · log log n)](https://doi.org/10.1145/3618260.3649664).
  STOC 2024, 1268 to 1278; ECCC TR23-174.
  Evaluates a tree of fixed fan-in, height $h$ and $b$-bit nodes in space about $(h + b) \log b$, below the
  $h \cdot b$ of storing a path of values.
  *Here:* the kit's `Rule30LightCone` cuts the spacetime diagram into a tree of this shape, which puts the center
  cell at time $n$ in space $O(\sqrt{n} \log n)$ ([the space ladder](../findings/complexity/space-ladder.md)).
- **Williams (2025).** [Simulating time with square-root space](https://arxiv.org/abs/2502.17779). arXiv:2502.17779,
  STOC 2025.
  Improves the simulation to space about $\sqrt{t \log t}$, through Cook and Mertz's algorithm. For the center
  column the direct tree is better: simulation takes multitape time of order $n^2$, which this turns into space of
  order $n \sqrt{\log n}$.
- **Razborov and Rudich (1997).** [Natural proofs](https://doi.org/10.1006/jcss.1997.1494).
  *Journal of Computer and System Sciences* 55(1), 24 to 35.
  Most known circuit lower-bound proofs are natural, and natural proofs cannot give superpolynomial circuit lower bounds
  if strong pseudorandom generators exist. If Rule 30 behaves like such a generator, circuit-style arguments for
  Problem 3 meet this barrier; that is an analogy, not a theorem about Rule 30.

## Checking and derandomization

Verifying a computation is cheap whatever the computation, and an explicit lower bound in exponential time would
derandomize probabilistic algorithms. [Probabilistic checking](../negative-results/complexity/probabilistic-checking.md)
explains why neither bears on computing the center column.

- **Babai, Fortnow, Levin and Szegedy (1991).** [Checking computations in polylogarithmic time](https://doi.org/10.1145/103418.103428).
  STOC 1991, 21 to 31; the record was checked through dblp and BibSLEIGH.
  Every computation of $T$ steps has a proof of length about $T^{1 + \varepsilon}$ that a randomized verifier checks in
  time polylogarithmic in $T$.
  *Here:* [probabilistic checking](../negative-results/complexity/probabilistic-checking.md).
- **Goldwasser, Kalai and Rothblum (2008).** [Delegating computation: interactive proofs for muggles](https://eccc.weizmann.ac.il/report/2017/108/).
  STOC 2008; the journal version is ECCC TR17-108.
  An efficient prover convinces a verifier of the output of a uniform circuit of depth $d$ in time about $d$ times a
  polylogarithm of its size.
  *Here:* [probabilistic checking](../negative-results/complexity/probabilistic-checking.md).
- **Impagliazzo and Wigderson (1997).** [P = BPP if E requires exponential circuits: derandomizing the XOR lemma](https://doi.org/10.1145/258533.258590).
  STOC 1997, 220 to 229.
  If some language in exponential time needs circuits of size $2^{\Omega(n)}$, then $\mathrm{P} = \mathrm{BPP}$.
  *Here:* a circuit form of Problem 3 would supply such a language
  ([probabilistic checking](../negative-results/complexity/probabilistic-checking.md)).

## Satisfiability and unique games

Two unrefereed claims of October 2026, each released with a Lean formalization. If correct, the first settles the
Unique Games Conjecture and the second refutes the Exponential Time Hypothesis.
[The hardness hypotheses](../negative-results/complexity/hardness-hypotheses.md) explains why neither bears on
Problem 3.

- **OpenAI (2026).** [The Unique Games conjecture and optimal approximation thresholds](https://github.com/openai/math/blob/main/lean/docs/102.md).
  A page of the repository openai/math, with preprints dated September 23, 2026, among them *The Unique Games
  Theorem*, and their Lean files.
  Claims a deterministic polynomial-time reduction from 3-SAT to bipartite unique games over an alphabet
  $\mathbb{F}_2^s$ with translation constraints, with completeness at least $1 - \varepsilon$ and soundness at most
  $\delta$ for every fixed $0 < \varepsilon, \delta < 1/2$. The repository says that its results are at different
  stages of verification.
  *Here:* [the hardness hypotheses](../negative-results/complexity/hardness-hypotheses.md).
- **Anthropic (2026).** [A 2^o(n) time algorithm for 3-SAT](https://github.com/anthropics/formal-math/pull/31).
  The paper and its Lean 4 formalization, merged into the repository anthropics/formal-math on October 27, 2026.
  Claims one deterministic machine that counts, for every $k$, the satisfying assignments of $k$-CNF formulas on $n$
  variables in time $2^{o(n)}$.
  *Here:* [the hardness hypotheses](../negative-results/complexity/hardness-hypotheses.md).

## Rule 30 as a pseudorandom generator and a cipher

- **Wolfram (1986).** [Cryptography with cellular automata](https://doi.org/10.1007/3-540-39799-X_32).
  CRYPTO '85, *Lecture Notes in Computer Science* 218, 429 to 432.
  A stream cipher whose keystream is one cell of a circular Rule 30 register and whose key is the initial row; key
  recovery is conjectured, not proved, to take more than polynomial time.
- **Wolfram (2002).** [*A New Kind of Science*, page 317](https://www.wolframscience.com/nks/p317/).
  Mathematica's `Random[Integer]` takes its bits from Rule 30's center column. The center column is judged random for
  practical purposes, though not under definitions that allow any simple program.
- **Meier and Staffelbach (1991).** [Analysis of pseudo random sequences generated by cellular automata](https://doi.org/10.1007/3-540-46416-6_17).
  EUROCRYPT '91, *Lecture Notes in Computer Science*, 186 to 199.
  A known-plaintext attack on cellular-automaton stream ciphers that is practical for keys of a few hundred bits.
- **Carrijo, Nascimento, Tonicelli and Alves (2011).**
  [Fault attacks against a cellular automata based stream cipher](https://doi.org/10.5753/sbseg.2011.20565).
  SBSeg 2011, 85 to 94.
  Recovers the key of a Rule 30 stream cipher from injected faults.
- **Das and RoyChowdhury (2013).** [CAR30: A new scalable stream cipher with rule 30](https://doi.org/10.1007/s12095-012-0079-1).
  *Cryptography and Communications* 5(2), 137 to 162. A cipher design built on Rule 30.
- **Spencer (2013).** [Cellular automata in cryptographic random generators](https://arxiv.org/abs/1306.3546).
  arXiv:1306.3546.
  A review of cellular-automaton generators: little proven security despite good statistics, and known attacks
  revisited and in places improved.
- **Martin and Solé (2008).** [Pseudo-random sequences generated by cellular automata](https://arxiv.org/abs/0807.3865).
  arXiv:0807.3865. A short survey of cellular-automaton random generators.
- **Mariot (2024).** [Insights gained after a decade of cellular automata-based cryptography](https://arxiv.org/abs/2405.02875).
  arXiv:2405.02875.
  A recent review of cellular-automaton cryptography and its weaknesses.

These attacks recover keys of finite registers; none says anything about the cost of the single seed's center cell.
*Here:* [the complexity category](../CATALOG.md#complexity) and
[the statistical tests](../negative-results/statistics/randomness-tests.md).
