---
title: The Unique Games Conjecture and the Exponential Time Hypothesis do not decide Problem 3
category: complexity
problems: [3, 1, 2]
status: negative
kind: barrier
---

# The Unique Games Conjecture and the Exponential Time Hypothesis do not decide Problem 3

**Question.** Two claims about satisfiability appeared in October 2026, both unrefereed and both with Lean
formalizations: a proof of the Unique Games Conjecture, and deterministic algorithms that solve 3-SAT on $N$
variables in time $2^{o(N)}$, which would refute the Exponential Time Hypothesis
([the literature](../../literature/complexity.md#satisfiability-and-unique-games)). Would either, if correct, decide
Problem 3, or open a route to Problems 1 and 2 through satisfiability?

**The statements side by side.**

- The Unique Games Conjecture: for every $\varepsilon, \delta > 0$ there is an alphabet on which it is NP-hard to tell
  unique games (constraints on pairs of variables, each a bijection of the labels) of value at least
  $1 - \varepsilon$ from those of value at most $\delta$. A statement about worst-case instances of a family of
  approximation problems.
- The Exponential Time Hypothesis: 3-SAT on $N$ variables needs time $2^{\delta N}$ for some $\delta > 0$.
- Problem 3 in its weakest form, the kit's `Problem3Robust`: no machine computes $c(n)$ from the $m = \log_2 n$
  digits of $n$ in time $n^{o(1)} = 2^{o(m)}$. Simulation takes time $O(n^2) = 2^{O(m)}$, so this is itself an
  exponential-time hypothesis, for one explicit function computable in exponential time.

**Why neither transfers.**

1. **Lower bounds move along reductions, and these hypotheses are too weak for one.** A lower bound for $c$ from
   either needs a reduction from satisfiability or unique games to computing $c$. None is known, and $c$ has no input
   but $n$ in which an instance could be written. Even with one, the Unique Games Conjecture is a statement of
   NP-hardness: through a reduction of polynomial size it would show at most that $c$ is not computable in time
   polynomial in $m$ unless P = NP, short of the bound $2^{\Omega(m)}$ that every version of Problem 3 asks for. That
   bound needs an exponential hypothesis, such as the Exponential Time Hypothesis, and a reduction with
   $\log n = O(m)$; and the Exponential Time Hypothesis is the one claimed false. A reduction of that size from any
   problem hard for exponential time would give `Problem3Robust` outright, by the time hierarchy theorem, with no
   hypothesis; that is the route [the barrier entry](problem-three-barrier.md) names.
2. **Upper bounds move the other way.** A fast 3-SAT algorithm speeds up $c$ only if $c(n)$ reduces to a formula with
   few variables. The natural formula, the spacetime diagram with the rule as clauses, has about $n^2 = 4^m$ variables,
   each forced from the initial row by unit propagation, so time $2^{o(N)}$ on its $N$ variables is no match for
   simulation. A formula with $O(m)$ variables would be a certificate for $c(n)$ checkable in time polynomial in $m$,
   the kind of shortcut that Problem 3 denies; with one, a $2^{o(N)}$ algorithm would refute `Problem3Robust`. The
   searches in this category found no shortcut of any kind ([automata](automaton-lower-bounds.md),
   [linear complexity](linear-complexity.md), [learned predictors](../learned-models/digits-to-cell.md)).
3. **Rule 30's constraint problems are easy.** A row with a prescribed center column and right half is found cell by
   cell, by left permutivity, in time $O(n^2)$ (the kit's `Rule30Realization`, and
   [LeftWindow.md](../../Rule30Open/RandomRows/LeftWindow.md) for windows), so no hard satisfiability instance arises.
   Read as a constraint problem whose labels are pairs of adjacent columns, the constraint between neighbors is a
   function in one direction only, column $x - 1$ from columns $x$ and $x + 1$: Rule 30 is not permutive on the right,
   so the constraints are not bijections and the problem is not a unique game. The single cell's instance is satisfied
   exactly, by one spacetime diagram, while the Unique Games Conjecture is about telling nearly satisfiable instances
   from far ones. The hard Rule 30 instances in the literature are key recovery for ciphers on finite rings (Wolfram
   1986, Meier and Staffelbach 1991), which no prize problem asks.
4. **Problems 1 and 2 have no instances.** Each is a statement about one infinite sequence, an eventual period or a
   limiting density, not a decision problem with a size, so no hypothesis about the cost of decision problems applies.
   Problem 1 enters only through Problem 3, which contains it.
5. **Hardness over rows does not reach the single cell.** As a function of its cone, the center cell at time $t$
   needs a decision tree of depth at least $2t - 1$ ([the degree finding](../../findings/structure/center-degree.md)),
   and random rows make every center cell a fair coin
   ([the random-row barrier](../random-rows/almost-every-row.md)). For the single cell the row is given, so these
   bounds measure the cost of reading an input that Problem 3 does not have.

**What it means.** Settling either hypothesis changes nothing in [the barrier entry](problem-three-barrier.md). As an
analogy only: if the 3-SAT algorithms hold up, an exponential-time hypothesis for a natural problem has failed, and
`Problem3Robust` is a hypothesis of the same form for $c$, which a speedup of the same kind, to any time $2^{o(m)}$,
would refute. Nothing found here suggests such a speedup exists.

**What would change this.** A reduction to $c$, with input size linear in $m$, from a problem hard for exponential
time (Problem 3 follows), or a reduction of $c(n)$ to a formula with $O(\log n)$ variables (with a $2^{o(N)}$
algorithm, Problem 3 fails).
