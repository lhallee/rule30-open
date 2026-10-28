# Single columns of cellular automata

Problem 1 is about one column of one orbit. Symbolic dynamics calls the time sequence of a cell, or of a block of $w$
adjacent cells, a trace of width $w$. This file collects what is proved about traces: Jen's theorems, Kopra's class of
rapidly left expansive automata, which contains Rule 30, the general theory of traces and directional dynamics, and
the 2-adic view. The theorems reach traces of width 2 for Rule 30 and width 1 for some arithmetic automata; the width-1
center column of Rule 30 is open.

## Jen's theorems

- **Jen (1986)**, in [rule-30.md](rule-30.md): no two columns of the single cell's pattern are both eventually periodic.
- **Jen (1990).** [Aperiodicity in one-dimensional cellular automata](https://doi.org/10.1016/0167-2789(90)90169-P).
  *Physica D* 45(1 to 3), 3 to 18.
  Kopra (2023) builds his Theorem 3.5 on its Proposition 3, an aperiodicity result for the columns of certain
  left-permutive elementary rules. The text was not read in this search.
  *Here:* [the adjacent-column theorem](../Rule30Open/Columns/AdjacentColumns.md), proved for every row with a leftmost
  black cell, and its uses in [the finite game](../Rule30Open/Columns/FiniteGame.md) and
  [GameBlocks](../Rule30Open/Columns/GameBlocks.md).

## Traces

- **Kopra (2023).** [Rapid left expansivity, a commonality between Wolfram's Rule 30 and powers of p/q](https://doi.org/10.1016/j.tcs.2022.12.018).
  *Theoretical Computer Science* 946, 113668; preprint [arXiv:2202.13809](https://arxiv.org/abs/2202.13809) under the
  title *A natural class of cellular automata containing fractional multiplication automata, Rule 30, and others*.
  Defines rapidly left expansive automata and proves (Theorem 3.5, numbered as in the preprint) that for such an
  automaton of width $w$ and any nonzero row that is white far to the left, no trace of width $w$ is eventually
  periodic. Rule 30 belongs to the class with $w = 2$: no two adjacent columns are both eventually periodic. The width-1
  trace of Rule 30 from the single cell is left open as Problem 4.8, with the expected answer that it is not eventually
  periodic. Rule 90 is also in the class, and its single-cell center column is eventually periodic, so the class's
  properties alone cannot give width 1.
  *Here:* the adjacent-column theorem is the case $w = 2$; Problem 4.8 is Prize Problem 1.
- **Kopra (2021).** [On the trace subshifts of fractional multiplication automata](https://doi.org/10.1016/j.tcs.2020.11.010).
  *Theoretical Computer Science* 851, 92 to 110; [arXiv:2005.05112](https://arxiv.org/abs/2005.05112).
  For the automaton that multiplies by $p/q$ in base $pq$, with $p > q > 1$ coprime, the width-1 trace at a cell is not
  eventually periodic from any row that represents a positive real, every nonzero finite row included (Proposition 2.8
  in the preprint). The trace subshift is conjugate to a base-$p/q$ numeration system and is not sofic. The proof uses
  the arithmetic of multiplication.
  *Here:* [fractional multiplication](../negative-results/analogs/fractional-multiplication.md) records why the argument
  does not transfer to Rule 30.
- **Kari and Kopra (2017).** [Cellular automata and powers of p/q](https://doi.org/10.1051/ita/2017014).
  *RAIRO Theoretical Informatics and Applications* 51(4), 191 to 204.
  Uses the multiplication automata to bound where the fractional parts of $\xi (p/q)^n$ can lie, the setting of
  Mahler's question below.
- **Mahler (1968).** [An unsolved problem on the powers of 3/2](https://doi.org/10.1017/S1446788700005371).
  *Journal of the Australian Mathematical Society* 8(2), 313 to 321.
  Asks whether a positive number exists whose multiples by every power of 3/2 all have fractional part below one half.
  Through Kopra's automata this is the arithmetic relative of a column question; it is open.
- **Cervelle, Formenti and Guillon (2010).** [Ultimate traces of cellular automata](https://doi.org/10.4230/LIPIcs.STACS.2010.2451).
  STACS 2010, LIPIcs 5, 155 to 166; [arXiv:1001.0251](https://arxiv.org/abs/1001.0251).
  Sufficient conditions for a set of infinite words to be the trace of an automaton, and a Rice theorem: every
  nontrivial property of traces that is stable under eventual agreement is undecidable, which limits what a method
  meant for all automata can decide.
- **Cervelle, Formenti and Guillon (2007).** [Sofic trace of a cellular automaton](https://arxiv.org/abs/math/0703241).
  arXiv:math/0703241.
  Introduces the trace subshift, the set of all columns an automaton can produce, and asks which sofic subshifts are
  traces.

## Directional dynamics and classification

A column is the vertical direction of the space-time diagram. These works classify automata by their behavior along
directions and as dynamical systems on rows; none bears on the periodicity of one column of one orbit.

- **Sablik (2008).** [Directional dynamics for cellular automata: a sensitivity to initial condition approach](https://doi.org/10.1016/j.tcs.2008.02.052).
  *Theoretical Computer Science* 400(1 to 3), 1 to 18.
  Equicontinuity and expansivity along directions of the space-time diagram.
- **Delacourt, Poupet, Sablik and Theyssier (2011).** [Directional dynamics along arbitrary curves in cellular automata](https://doi.org/10.1016/j.tcs.2011.02.019).
  *Theoretical Computer Science* 412(30), 3800 to 3821; [arXiv:1001.5470](https://arxiv.org/abs/1001.5470).
  Extends directional dynamics to curves; an automaton can be equicontinuous along a parabola and sensitive along every
  line.
- **Dennunzio, Di Lena, Formenti and Margara (2009).** [On the directional dynamics of additive cellular automata](https://doi.org/10.1016/j.tcs.2009.06.023).
  *Theoretical Computer Science* 410(47 to 49), 4823 to 4833.
  Places the linear automata in Sablik's directional classes.
- **Kůrka (1997).** [Languages, equicontinuity and attractors in cellular automata](https://doi.org/10.1017/S014338579706985X).
  *Ergodic Theory and Dynamical Systems* 17(2), 417 to 433.
  Relates three classifications of automata, and proves that positively expansive automata are conjugate to one-sided
  subshifts of finite type and that transitive automata are sensitive.
- **Schüle and Stoop (2012).** [A full computation-relevant topological dynamics classification of elementary cellular automata](https://doi.org/10.1063/1.4771662).
  *Chaos* 22(4), 043143.
  Classifies the elementary rules by sensitivity and chaos; Rule 30 is surjective and chaotic in Devaney's sense.

## The 2-adic view

- **Anashin, Khrennikov and Yurova (2014).** [T-functions revisited: new criteria for bijectivity/transitivity](https://doi.org/10.1007/s10623-012-9741-z).
  *Designs, Codes and Cryptography* 71(3), 383 to 407; [arXiv:1111.3093](https://arxiv.org/abs/1111.3093).
  Criteria for a T-function, a map of the 2-adic integers whose low bits depend only on low bits, to be bijective or
  transitive, from non-Archimedean ergodic theory.
  *Here:* [the 2-adic trace](../findings/frames/two-adic-trace.md) writes Rule 30 as the T-function
  $y \oplus (2y \lor 4y)$ and its center column as the image of 1 under a 2-adic isometry. The search found no source
  that applies T-function theory to Rule 30.

## Checked records, texts not read

The search confirmed these records but could not read the texts; check a claim against the text before citing it.

- **Jen (1988).** [Linear cellular automata and recurring sequences in finite fields](https://doi.org/10.1007/BF01218258).
  *Communications in Mathematical Physics* 119(1), 13 to 28.
- **Cervelle and Guillon (2007).** [Towards a Rice theorem on traces of cellular automata](https://doi.org/10.1007/978-3-540-74456-6_29).
  MFCS 2007, *Lecture Notes in Computer Science* 4708, 310 to 319.
- **Nasu (1995).** [Textile systems for endomorphisms and automorphisms of the shift](https://doi.org/10.1090/memo/0546).
  *Memoirs of the American Mathematical Society* 114(546).
- **Shereshevsky (1992).** [Lyapunov exponents for one-dimensional cellular automata](https://doi.org/10.1007/BF02429850).
  *Journal of Nonlinear Science* 2(1), 1 to 8.
- **Blanchard and Maass (1997).** [Dynamical properties of expansive one-sided cellular automata](https://doi.org/10.1007/BF02760680).
  *Israel Journal of Mathematics* 99(1), 149 to 174.
- **Blanchard and Maass (1996).** [Dynamical behaviour of Coven's aperiodic cellular automata](https://doi.org/10.1016/0304-3975(96)00018-7).
  *Theoretical Computer Science* 163(1 to 2), 291 to 302.
- **Boyle and Lind (1997).** [Expansive subdynamics](https://doi.org/10.1090/S0002-9947-97-01634-6).
  *Transactions of the American Mathematical Society* 349(1), 55 to 102.
- **Cattaneo, Finelli and Margara (2000).** [Investigating topological chaos by elementary cellular automata dynamics](https://doi.org/10.1016/S0304-3975(98)00345-4).
  *Theoretical Computer Science* 244(1 to 2), 219 to 241.
- **Kari (2005).** [Theory of cellular automata: a survey](https://doi.org/10.1016/j.tcs.2004.11.021).
  *Theoretical Computer Science* 334(1 to 3), 3 to 33.
- **Mariot, Leporati, Dennunzio and Formenti (2016).** [Computing the periods of preimages in surjective cellular automata](https://doi.org/10.1007/s11047-016-9586-x).
  *Natural Computing* 16(3), 367 to 381.
- **Törmä (2019).** [Countable sofic shifts with a periodic direction](https://doi.org/10.1007/s00224-019-09962-8).
  *Theory of Computing Systems* 64(6), 1042 to 1066.
