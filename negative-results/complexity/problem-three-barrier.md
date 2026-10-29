---
title: Problem 3 asks for a lower bound beyond current complexity theory
category: complexity
problems: [3, 1]
status: negative
kind: barrier
---

# Problem 3 asks for a lower bound beyond current complexity theory

**The statement.** The kit's
[`Rule30Problem3`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Problem3.lean)
gives three versions, each implying the next, for a one-tape machine that reads the binary digits of $n$: no machine
computes $c(n)$ within $C(n + 1)$ steps (`Problem3`), none in time $o(n)$ (`Problem3Verbal`), and none in time
$n^{o(1)}$ (`Problem3Robust`, the only model-independent one).

**Why an affirmative answer is out of reach.**

- The input has $m = \log_2 n$ digits, so even the weakest version says that $c$ needs time $2^{\Omega(m)}$ for some
  constant in the exponent: an exponential lower bound in the input length. In particular it implies that $c$ is not
  computable in polynomial time as a function of the binary input.
- $c$ is computable in time $O(n^2) = O(4^m)$ by simulation, so it lies in exponential time. Separating an explicit,
  natural function in exponential time from polynomial time needs either a reduction from a problem known to be hard
  (Rule 30 is not known to be computationally universal) or a lower-bound technique for a specific function, and no
  such technique is known.
- A one-tape machine simulates several tapes in quadratic time, so even the strongest version, an $n$-step lower bound
  on one tape, gives only $\sqrt{n}$ on several tapes. A random-access machine with unit-cost bitwise operations
  computes $c(n)$ in $O(n)$ operations, as bit $n$ of $\Phi^n(1)$ with $\Phi(x) = x \oplus (2x \lor 4x)$.

**In space it is the same question.** By Paterson's theorem a one-tape machine that runs in time $C(n + 1)$ can be
replaced by one that uses space $O(\sqrt{n})$, so `Problem3` follows if $c$ needs more space than that, and tree
evaluation computes $c$ in space $O(\sqrt{n} \log n)$ ([the space ladder](../../findings/complexity/space-ladder.md)).
No space lower bound beyond a constant is known for $c$; even that one would say that $c$ is not 2-automatic.

**Why a negative answer needs hidden structure.** It needs an explicit fast algorithm, which every search here failed
to find: [automata](automaton-lower-bounds.md), [linear recurrences](linear-complexity.md),
[learned predictors](../learned-models/digits-to-cell.md) and [exact structure searches](../structure/linear-relations.md).

**Problem 3 contains Problem 1.** If $c$ were eventually periodic with period $P$, a machine could read the digits of
$n$ once, compute $n \bmod P$ with a finite automaton, and look up the answer, in $O(\log n)$ steps. That violates every
version of Problem 3. So Problem 3 is at least as hard as Problem 1. The kit's equivalent forms prove this in Lean,
for one-tape machines reading the digits of $n$ and for the kit's model-independent statement, through "$c$ is not
2-automatic" ([`ProblemThree`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/equivalents/Rule30Equivalents/ProblemThree.lean): `problem1_of_problem3Verbal`, `problem1_of_problem3Robust`).

**What would help.** A reduction showing that computing $c$ is hard for exponential time, or a proof that Rule 30's
center column can simulate arbitrary computation, would turn the question into known separations; neither is in
sight. Hypotheses about satisfiability do not substitute for such a reduction, settled or not:
[the hardness hypotheses](hardness-hypotheses.md).
