# Problem 3, prediction, and Rule 30 as a cipher

Problem 3 asks whether the $n$th center cell needs effort of order $n$. This file collects what is known about the cost
of computing Rule 30, the hardness results proved for other automata, the general lower-bound landscape a proof would
have to enter, and the cryptanalysis of Rule 30 as a pseudorandom generator. [The Problem 3 barrier](../negative-results/complexity/problem-three-barrier.md)
explains why an affirmative answer is beyond current complexity theory; the sources below are its context.

## The cost of computing Rule 30

- **Wolfram (2019).** [Announcing the Rule 30 Prizes](https://writings.stephenwolfram.com/2019/10/announcing-the-rule-30-prizes/).
  Reaching step $n$ by direct simulation takes about $n^2$ cell updates; Problem 3 asks whether anything essentially
  faster exists for the center cell.
  *Here:* [the quadratic-time machine](../Rule30Open/Complexity/QuadraticTime.md) does the simulation in the kit's
  one-tape model in exactly $2n^2 + 2n\ell + 7n + 3\ell + 6$ steps, $\ell$ the number of digits of $n$, in Lean.
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
- **Sibgatullin and Williams (2026).**
  [Space-efficient simulations beyond multitape Turing machines](https://eccc.weizmann.ac.il/report/2026/223/).
  ECCC TR26-223, October 2, 2026; unrefereed. The record and the text of the introduction and of Section 6 were read.
  Simulates $t$ steps of a $d$-dimensional cellular automaton, from the initial states of the cells within the light
  cone of the cell asked for, in space $O((t \log t)^{1 - 1/(d+1)})$ (Theorem 1.5); for $d = 1$ this is
  $O(\sqrt{t \log t})$ (Theorem 1.4). The proof runs $k$ steps per round of an external-memory model, one processor per
  cell, and applies their generalization of Cook and Mertz's algorithm. The same paper evaluates unbounded fan-in
  circuits of $n$ gates in space $O(\sqrt{n \log n})$ and lexicographically first 2-satisfiability in space
  $\tilde O(\sqrt{n})$.
  *Here:* it is the center column. For the single black cell the initial states are computed on demand; [the space
  thresholds](../findings/complexity/space-thresholds.md) derive $O(\sqrt{n \log n})$ from the kit's block tree
  directly, and compare it with the thresholds a space lower bound must pass.

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
- **Hopcroft and Ullman (1968).** [Relations between time and tape complexities](https://doi.org/10.1145/321466.321474).
  *Journal of the ACM* 15(3), 414 to 427; the record was checked through Crossref, the text was not read.
  Williams credits it with the simulation of one-tape time $t$ in space $O(\sqrt{t})$ that predates Paterson's.
- **Hennie (1965) and Hartmanis (1968).**
  [One-tape, off-line Turing machine computations](https://doi.org/10.1016/s0019-9958(65)90399-2),
  *Information and Control* 8(6), 553 to 578;
  [Computational complexity of one-tape Turing machine computations](https://doi.org/10.1145/321450.321464),
  *Journal of the ACM* 15(2), 325 to 339. The records were checked through Crossref, the texts were not read.
  A deterministic one-tape machine that decides a nonregular language needs time of order $n \log n$ (Hennie with
  Trakhtenbrot, 1964, and Hartmanis, as the kit's `OneTapeGap` attributes it), proved by counting crossing sequences.
  *Here:* the kit proves it in Lean for digit input, and [the crossing-sequence barrier](../negative-results/complexity/one-tape-crossing.md)
  asks what the same method can give for the center column beyond it.
- **Cook and Mertz (2024).** [Tree evaluation is in space O(log n · log log n)](https://doi.org/10.1145/3618260.3649664).
  STOC 2024, 1268 to 1278; ECCC TR23-174; *SIAM Journal on Computing*, 2025,
  [DOI 10.1137/24m1690126](https://doi.org/10.1137/24m1690126) (the record was checked through Crossref).
  Evaluates a tree of fan-in $d$, height $h$ and $b$-bit nodes in space $O(d b + h \log (d b))$, as Williams states
  their Theorem 7 and as Goldreich states it for binary trees, $O(b + h \log b)$. The ECCC text proves the weaker
  $O((h + b) \log b)$ (its Theorem 10); both are below the $h \cdot b$ of storing a path of values.
  *Here:* the kit's `Rule30LightCone` cuts the spacetime diagram into a tree of this shape, which puts the center
  cell at time $n$ in space $O(\sqrt{n \log n})$ with the first form and $O(\sqrt{n} \log n)$ with the second ([the space
  thresholds](../findings/complexity/space-thresholds.md)).
- **Goldreich (2024) and Stoeckl.** [On the Cook-Mertz tree evaluation procedure](https://eccc.weizmann.ac.il/report/2024/109),
  ECCC TR24-109, June 29, 2024, revised December 2024; and
  [Solving tree evaluation in o(log n · log log n) space](https://eccc.weizmann.ac.il/report/2024/124/), ECCC TR24-124,
  July 26, 2024, also in *Computational Complexity and Local Algorithms*, Lecture Notes in Computer Science, 2025,
  [DOI 10.1007/978-3-031-88946-2_7](https://doi.org/10.1007/978-3-031-88946-2_7) (Crossref); the text of TR24-124 was
  read. The first explains Cook and Mertz's algorithm as univariate interpolation. The second, a result Goldreich
  credits to Manuel Stoeckl, groups $h'$ levels into one $2^{h'}$-ary node and obtains space
  $O(h + 2^{h'} b + (h / h') \log b)$, which shaves a factor $\log\log$ from $h \log b$ when the height $h$ is much
  larger than $b / \log b$ ($h \log b \gg b$).
  *Here:* the block tree of the center column has $h \approx 3 b / \log_2 b$ at its best $b$, the balanced case where
  the grouping gains nothing ([the space thresholds](../findings/complexity/space-thresholds.md)).
- **Williams (2025).** [Simulating time with square-root space](https://arxiv.org/abs/2502.17779). arXiv:2502.17779,
  STOC 2025; *Journal of the ACM* 73(3), 1 to 25, June 2026,
  [DOI 10.1145/3798104](https://doi.org/10.1145/3798104) (the record was checked through Crossref; the text read is the
  arXiv version).
  Multitape time $t$ is simulated in space $O(\sqrt{t \log t})$ (Theorem 1.1), by cutting a block-respecting run into
  $b$-step blocks, evaluating the resulting tree of height $t / b$ with Cook and Mertz's algorithm, and choosing
  $b = \Theta(\sqrt{t \log t})$; $d$-dimensional multitape machines go in $O((t \log t)^{1 - 1/(d+1)})$ (Theorem 1.5);
  random-access machines only when their memory accesses are oblivious (Remark 1.6). Section 5 asks whether the
  Hopcroft and Ullman bound $O(\sqrt{t})$ for one tape can be lowered to $t^{1/2 - \varepsilon}$.
  *Here:* simulating Rule 30 row by row is multitape time of order $n^2$, which gives space of order
  $n \sqrt{\log n}$, worse than the tree on the block structure and than Sibgatullin and Williams below.
- **Shalunov (2025).** [Improved bounds on the space complexity of circuit evaluation](https://arxiv.org/abs/2504.20950).
  arXiv:2504.20950, April 29, 2025, revised June 19, 2025; the abstract was read.
  A direct reduction from circuit evaluation to tree evaluation: a circuit of $s$ gates in space $O(\sqrt{s \log s})$.
  *Here:* the same balance of $b$ and $h$ as for the center column.
- **Henzinger, Pyne and Ragavan (2026).** [Catalytic tree evaluation from matching vectors](https://arxiv.org/abs/2602.14320).
  arXiv:2602.14320, February 15, 2026; the abstract was read.
  A catalytic algorithm for tree evaluation with logarithmic free space, polynomial time and catalytic space
  $2^{\log^{\varepsilon} n}$ for every $\varepsilon > 0$, an improvement of the catalytic space of an earlier route
  through circuit evaluation; they present it as a step toward placing tree evaluation in logarithmic space, which
  stays open.
  *Here:* catalytic space is borrowed space that must be restored, so the result lowers the free space of a simulation
  only when the borrowed memory is available; it does not change the space ladder's $O(\sqrt{n \log n})$.
- **Morrison Orozco et al. (2026).** *Computing faster with a full memory: catalytic algorithms break time-space lower
  bounds.* [arXiv:2610.24377](https://arxiv.org/abs/2610.24377), October 2026; seen only in search results (arXiv is
  outside this session's network), the text and the full author list were not read. By the abstract as quoted there,
  with $O(\log n)$ free space and polynomial catalytic space, sorting and the discrete Fourier transform run in time
  $n^{1 + o(1)}$ and matrix multiplication in time $n^{\omega + o(1)}$, below the time-space lower bounds of order
  $n^2$ and $n^3$ that hold without catalytic space, in a model where the output is written in two passes; all known
  time-space lower bounds hold with any constant number of output passes. Unrefereed. *Here:* the lower bounds it
  passes are for functions with many output bits, proved by the branching-program method, and the result shows that
  they depend on the model's memory; the center column has one output bit, no time-space tradeoff is known for it,
  and Problem 3 asks for time alone ([the barrier](../negative-results/complexity/problem-three-barrier.md)).
- **Bhardwaj (2026).** *Unconditional separation between LL and CLL.*
  [arXiv:2610.15554](https://arxiv.org/abs/2610.15554) and ECCC TR26-252, October 14, 2026; seen only in search results,
  the text was not read. By the abstract as quoted there, a catalytic machine with $O(\log\log n)$ work space and
  $O(\log n)$ catalytic space decides the unary language of powers of two, which deterministic space $O(\log\log n)$
  does not, an unconditional separation at the doubly logarithmic scale; the logarithmic scale is stated open.
  Unrefereed. *Here:* a space lower bound for an explicit language, at a scale doubly logarithmic in the input's length
  $n$; the space form of Problem 3 asks a bound of order $\sqrt{n}$ when the input is the $\log_2 n$ digits of $n$,
  exponential in the input's length ([the space thresholds](../findings/complexity/space-thresholds.md)).
- **Asadi and Cleve (2026), withdrawn.** [Polynomial-time almost log-space tree evaluation by catalytic pebbling](https://eccc.weizmann.ac.il/report/2026/044/).
  ECCC TR26-044, April 2, 2026, and [arXiv:2604.02606](https://arxiv.org/abs/2604.02606). Claimed space
  $O(\log^{1 + \varepsilon} n)$ in polynomial time. Both records are withdrawn, on April 7, 2026, for an error in the
  degree of the polynomial for each subtree. Do not cite it as a result.
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
