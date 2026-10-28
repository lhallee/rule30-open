# Invariant measures, statistics and sibling rules

Problem 2 asks for the density of black cells in one specific sequence. The theory of invariant measures answers the
same question for a random initial row, and sibling rules show which density and aperiodicity questions can be settled
and why. This file collects both, with what each result does and does not say about the single cell.

## What measure theory gives

A cellular automaton that is onto keeps the uniform Bernoulli measure invariant. Rule 30 is onto because it is
permutive in its left input. So for a uniformly random initial row, every cell, the center included, is black with
probability exactly 1/2 at every time. The single cell is one row, of measure zero, so none of this decides Problem 2;
a proof has to use the single cell's orbit itself.

- **Hedlund (1969).** [Endomorphisms and automorphisms of the shift dynamical system](https://doi.org/10.1007/BF01691062).
  *Mathematical Systems Theory* 3, 320 to 375.
  The classical study of cellular automata as maps of the shift. Among its results, an automaton on a full shift is onto
  exactly when every block has the same number of preimages, which makes the uniform measure invariant.
- **Kari and Taati (2015).** [Statistical mechanics of surjective cellular automata](https://doi.org/10.1007/s10955-015-1281-2).
  *Journal of Statistical Physics* 160, 1198 to 1243; [arXiv:1311.2319](https://arxiv.org/abs/1311.2319).
  A surjective automaton preserves a shift-invariant Gibbs measure exactly when it conserves the corresponding
  energy; the uniform measure is the case of zero energy. The authors suggest that sufficiently chaotic automata have no
  other Gibbs or Markov invariant measures.
  *Here:* [conservation laws](../negative-results/structure/conservation-laws.md) finds no additive conservation law for
  Rule 30.
- **Pivato (2003).** [Invariant measures for bipermutative cellular automata](https://arxiv.org/abs/math/0306211).
  arXiv:math/0306211.
  Classifies the invariant measures of automata that are permutive in both outer inputs. Rule 30 is permutive only in
  its left input (when the center cell is black, the right input has no effect), so the classification does not apply.
- **Guan and Wang (2011).** [Complex shift dynamics of some elementary cellular automaton rules](https://doi.org/10.25088/ComplexSystems.20.1.31).
  *Complex Systems* 20(1).
  Claims that Rules 30, 41 and 110 act as Bernoulli shifts and are topologically mixing on closed invariant subsystems
  of their own. A statement about a subsystem, not about the uniform measure on all rows.

## Randomization and the linear rules

For linear rules, measures do more than stay invariant: iteration drives many initial measures toward the uniform one,
and the space-time pattern from a simple row is automatic. None of these theorems is known for a nonlinear rule.

- **Martin, Odlyzko and Wolfram (1984).** [Algebraic properties of cellular automata](https://doi.org/10.1007/BF01223745).
  *Communications in Mathematical Physics* 93, 219 to 258.
  The algebraic theory of linear automata, through polynomials over finite fields.
- **Pivato and Yassawi (2002).** [Limit measures for affine cellular automata](https://doi.org/10.1017/S0143385702000548).
  *Ergodic Theory and Dynamical Systems* 22(4), 1269 to 1287; [arXiv:math/0108082](https://arxiv.org/abs/math/0108082).
  Conditions under which a linear automaton drives an initial measure to the uniform measure in density; over
  $\mathbb{Z}/p$ every nontrivial linear automaton does so for most Bernoulli measures.
- **Pivato and Yassawi (2004).** [Limit measures for affine cellular automata II](https://doi.org/10.1017/S0143385704000288).
  *Ergodic Theory and Dynamical Systems* 24(6), 1961 to 1980; [arXiv:math/0108083](https://arxiv.org/abs/math/0108083).
  Diffusive linear automata randomize harmonically mixing measures along a set of times of density one.
- **Pivato and Yassawi (2006).** [Asymptotic randomization of sofic shifts by linear cellular automata](https://doi.org/10.1017/S0143385706000228).
  *Ergodic Theory and Dynamical Systems* 26(4), 1177 to 1201; [arXiv:math/0306136](https://arxiv.org/abs/math/0306136).
  Randomization of measures supported on sofic shifts, including measures of zero entropy, so entropy alone does not
  decide whether a measure is randomized.
- **Pivato (2007).** [Module shifts and measure rigidity in linear cellular automata](https://arxiv.org/abs/0707.1408).
  arXiv:0707.1408.
  Invariant measures of linear automata with a mixing property are Haar measures on translates of submodules.
- **Chang and Chang (2016).** [On the Bernoulli automorphism of reversible linear cellular automata](https://doi.org/10.1016/j.ins.2016.01.062).
  *Information Sciences* 345, 217 to 225; [arXiv:1503.05999](https://arxiv.org/abs/1503.05999).
  A reversible linear automaton over $\mathbb{Z}_m$ is either a Bernoulli automorphism or not ergodic. Rule 30 is
  neither linear nor reversible: the all-white and the all-black rows both map to the all-white row.
- **Rowland and Yassawi (2020).** [Automaticity and invariant measures of linear cellular automata](https://doi.org/10.4153/S0008414X19000488).
  *Canadian Journal of Mathematics* 72(6), 1691 to 1726.
  The space-time pattern of a linear automaton over $\mathbb{F}_p$ is automatic when the initial row is, and such
  patterns give invariant sets and measures. For a linear rule, this turns every column into the output of a finite
  automaton; nothing comparable is known for Rule 30.
  *Here:* [automaton lower bounds](../negative-results/complexity/automaton-lower-bounds.md) finds no automaton under
  131,070 states for Rule 30's center column.

The single-cell center columns of the linear Rules 90 and 150 are periodic, so they are no model for Problem 1: Rule
90's is black at time 0 and white after, since $\binom{2m}{m}$ is even for $m \ge 1$, and Rule 150's is black at every
time, since the central trinomial coefficients are odd (checked here by direct evolution to 300 steps). The sibling
rules in [the analogs category](../CATALOG.md#sibling-rules) are compared with Rule 30 on other questions.

## Entropy

- **Tisseur (2000).** [Cellular automata and Lyapunov exponents](https://doi.org/10.1088/0951-7715/13/5/308).
  *Nonlinearity* 13(5), 1547 to 1560; [arXiv:math/0312136](https://arxiv.org/abs/math/0312136).
  Shows that Shereshevsky's left and right Lyapunov exponents of an automaton are well defined for a wider family of
  measures, and bounds the automaton's entropy by them and the shift's entropy.
- **Hurd, Kari and Culik (1992).** [The topological entropy of cellular automata is uncomputable](https://doi.org/10.1017/S0143385700006738).
  *Ergodic Theory and Dynamical Systems* 12(2), 255 to 265.
  No algorithm computes the topological entropy of a cellular automaton, or even approximates it within a fixed
  tolerance; a value for Rule 30 has to come from an argument about Rule 30.

## Statistics of the center column

- **Wolfram (2002).** [*A New Kind of Science*, note (c) to page 871](https://wolframscience.com/nksonline/page-871c/).
  Of the first 100,000 center cells 50,098 are black, and of the first million 500,768; no repetition appears in the
  first million steps.
- **Musselman (2004).** [A study of randomness in the output of simple programs](https://wolframscience.com/conference/2004/presentations/HTMLLinks/index_48.html).
  NKS 2004 conference, presentation abstract.
  The single cell's center column passed every test of a battery drawn from the NIST SP 800-22 suite; no numbers are
  given.
- *Here:* [the randomness tests](../negative-results/statistics/randomness-tests.md) on $2^{22}$ cells (density
  0.500169) and [compression](../negative-results/statistics/compression.md). Finite prefixes cannot fix a limiting
  density, which is why these are recorded as tests that found nothing.

## Exact results for sibling rules

- **Prosen and Mejía-Monasterio (2016).** [Integrability of a deterministic cellular automaton driven by stochastic boundaries](https://doi.org/10.1088/1751-8113/49/18/185003).
  *Journal of Physics A* 49(18), 185003; [arXiv:1512.01385](https://arxiv.org/abs/1512.01385).
  A finite Rule 54 chain with random reservoirs at both ends has a unique steady state with an exact matrix-product
  form, which gives its densities and currents. A density theorem for an open, driven system.
- **Fukś (1999).** [Exact results for deterministic cellular automata traffic models](https://doi.org/10.1103/PhysRevE.60.197).
  *Physical Review E* 60, 197 to 202; [arXiv:comp-gas/9902001](https://arxiv.org/abs/comp-gas/9902001).
  The exact flow at every time for a traffic automaton that reduces to Rule 184, from a random initial row, by counting
  preimages as lattice paths. Preimage counting is one route to exact densities.
- **Chan-López and Martín-Ruiz (2026)**, in [rule-30.md](rule-30.md): a closed form for Rule 22's single-seed rows over
  $\mathbb{F}_2$, the only exact single-seed formula for a nonlinear sibling rule the search found.

## Checked records, texts not read

The search confirmed these records but could not read the texts; check a claim against the text before citing it.

- **Coven and Paul (1974).** [Endomorphisms of irreducible subshifts of finite type](https://doi.org/10.1007/BF01762187).
  *Mathematical Systems Theory* 8, 167 to 175.
- **Lind (1984).** [Applications of ergodic theory and sofic systems to cellular automata](https://doi.org/10.1016/0167-2789(84)90246-X).
  *Physica D* 10, 36 to 44.
- **Allouche, von Haeseler, Peitgen and Skordev (1996).** [Linear cellular automata, finite automata and Pascal's triangle](https://doi.org/10.1016/0166-218X(94)00132-W).
  *Discrete Applied Mathematics* 66, 1 to 22.
- **Allouche and Shallit (2003).** [*Automatic Sequences: Theory, Applications, Generalizations*](https://doi.org/10.1017/CBO9780511546563).
  Cambridge University Press. The standard reference for automatic sequences.
- **Grassberger (1986).** [Long-range effects in an elementary cellular automaton](https://doi.org/10.1007/BF01033074).
  *Journal of Statistical Physics* 45, 27 to 39. On long-range structure in an elementary rule, reportedly Rule 22.
