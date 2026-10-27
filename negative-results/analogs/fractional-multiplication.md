---
title: Kopra's width-one argument does not transfer to Rule 30
category: analogs
problems: [1]
status: negative
kind: barrier
---

# Kopra's width-one argument does not transfer to Rule 30

**Idea.** Kopra proves that single columns of fractional multiplication automata, such as multiplication by $p/q$ in
base $pq$, are aperiodic ("On the trace subshifts of fractional multiplication automata",
[arXiv:2005.05112](https://arxiv.org/abs/2005.05112), Proposition 2.8). A width-one result of that kind for Rule 30
would be Problem 1.

**Why it does not transfer.** Kopra's Proposition 2.8 rests on Proposition 2.7: a radius-one automaton in time maps
each column to the column on its left. That is left expansivity of width one: one column determines its left neighbor,
because the digit is fixed modulo $q$ by the step below and modulo $p$ by the step above. Rule 30 needs two columns:
$a_t(x - 1) = a_{t+1}(x) \oplus (a_t(x) \lor a_t(x + 1))$. That is why Jen's theorem holds for two adjacent columns
([AdjacentColumns.md](../../Rule30Open/Columns/AdjacentColumns.md)) and width one is open. Refining the lattice to half
steps (Rule 30's three-color square roots) makes the half-integer columns width-one left expansive, but that is masked
Jen again and adds nothing.

**What it means.** A proof of Problem 1 has to say something about how column 1 enters through the OR, which the
fractional multiplication automata do not have.
