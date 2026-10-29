---
title: Problems 1 and 3 follow from space lower bounds for the center column, and space √n log n suffices
category: complexity
problems: [3, 1]
status: paper
formalization: partial
---

# Problems 1 and 3 follow from space lower bounds for the center column, and space √n log n suffices

Measure the work space of a deterministic machine that reads the binary digits of $n$ and outputs the center cell
$c(n)$, as a function of $n$. Three published theorems place both prize problems on this one scale: Problem 1 follows
from any space lower bound that grows, the kit's formal Problem 3 follows from a lower bound larger than order
$\sqrt{n}$, and space of order $\sqrt{n} \log n$ is known to suffice. No space lower bound for $c$ is known at all.

## Statement

1. **Space that suffices.** A deterministic machine computes $c(n)$ in space $O(\sqrt{n} \log n)$.
2. **Problem 3 from space.** If a one-tape machine in the kit's model computes $c(n)$ within $C(n + 1)$ steps for
   every $n$, then a deterministic machine computes $c(n)$ in space $O(\sqrt{n})$. So the kit's `Problem3` holds if no
   machine computes $c$ in space $O(\sqrt{n})$, and `Problem3Verbal` holds if none computes it in space $o(\sqrt{n})$.
3. **Problem 1 from space, in the kit.** If a machine computes $c(n)$ in space $o(\log \log n)$, then $c$ is
   2-automatic. So if the space needed to compute $c$ grows without bound, $c$ is not 2-automatic, and Problem 1 holds.
   The kit proves the sharper equivalence in Lean: Problem 1 holds if and only if no machines decide $c(n)$ from the
   base-2 and from the base-3 digits of $n$ in space $o(\log \log n)$.

## Proof

1. The kit's [`Rule30LightCone`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30LightCone.lean)
   proves the block tree: cut rows into blocks of $b$ cells and time into steps of $b$; block $j$ at time $(k + 1)b$
   is a fixed function of blocks $j - 1$, $j$ and $j + 1$ at time $kb$ (`block_step`), so the center cell at time
   $mb$ is the first cell of the root of a tree of height $m$, fan-in 3 and $b$-bit nodes (`center_eq_root`). Each node
   is computed from its children in space $O(b)$, by running $b$ steps of Rule 30 on $3b$ cells. Write
   $n = mb + r$ with $r < b$ and start the tree from row $r$, whose blocks are computed from the single cell in space
   $O(b)$. The tree evaluation algorithm of Cook and Mertz uses about $(h + b) \log b$ bits on a tree of fixed fan-in,
   height $h$ and $b$-bit nodes. With $b = \lceil \sqrt{n} \rceil$ and $h = m \le \sqrt{n}$ this is
   $O(\sqrt{n} \log n)$; the kit's module docstring makes the same count and formalizes neither algorithm.
2. Paterson's theorem: a language recognized by a one-tape machine, even a nondeterministic one, in time
   $T(m) \ge m^2$ on inputs of length $m$ is recognized by a deterministic machine in space $T(m)^{1/2}$. The input
   $n$ has $m = \lfloor \log_2 n \rfloor + 1$ digits and $n \ge 2^{m - 1}$, so time $C(n + 1)$ is at most
   $T(m) = 2C \cdot 2^m + m^2$, and the space is $O(2^{m/2}) = O(\sqrt{n})$. A machine that halts with the answer
   decides $\{n : c(n) = 1\}$, and conversely. For time $o(n)$ the same count gives space $o(\sqrt{n})$.
3. A machine with a read-only input tape that decides a language in space $o(\log m)$ on inputs of length $m$ decides
   a regular language (Stearns, Hartmanis and Lewis), and here $o(\log m)$ is $o(\log \log n)$. The digits of the
   black times form a regular language exactly when $c$ is automatic in that base, an eventually periodic sequence is
   automatic in every base, and a sequence automatic in bases 2 and 3 is eventually periodic (Cobham). All of this is in
   the kit's equivalent forms:
   [`OfflineGap`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/equivalents/Rule30Equivalents/OfflineGap.lean)
   (`isRegular_iff_exists_small_space_decider`, `problem1_iff_no_small_space_digit_deciders`), `OneTapeRegular`
   (`isRegular_digitLang_iff`), `Automatic` (`problem1_of_not_automatic`) and `Cobham`.

## What it means

The space of $c$ is constant if $c$ is 2-automatic; otherwise it is not $o(\log \log n)$. It is $O(\sqrt{n} \log n)$
either way. Problem 1 sits at the bottom of that range and Problem 3 near its top: a lower bound of
$\sqrt{n} \cdot g(n)$ with any $g$ that tends to infinity gives the kit's `Problem3`, within a factor $\log n$ of what
tree evaluation achieves. If tree evaluation could be improved to space $O(\sqrt{n})$ for this tree, this route to
Problem 3 would close, while Problem 3 itself could still hold. If the claimed simulation of one-tape machines in space
$T^{2/5}$ up to logarithmic factors is correct ([family
137](../../literature/ai-proposed.md#openais-manuscript-collection), unrefereed), a lower bound of $n^{2/5}$ times a
power of $\log n$ would already give `Problem3`, a polynomial factor below the upper bound.

The gap between $\sqrt{n}$ and $\sqrt{n} \log n$ is the gap in tree evaluation itself. Whether tree evaluation runs in
logarithmic space, which for these trees means space $O(h + b)$, is open, and Cook and Mertz's algorithm is within a
factor $\log b$ of it. If it does, the center column is computed in space $O(n / b + b) = O(\sqrt{n})$, and this route
to Problem 3 cannot work. Conversely, a proof that the center column needs space larger than order $\sqrt{n}$ would show
that tree evaluation on the trees of Rule 30's spacetime diagram needs more than logarithmic space, a lower bound that is
not known for any explicit family of trees outside restricted models.

This is a reformulation, not progress toward either problem. Even the weakest space lower bound, that $c$ needs more
than constant space, says that $c$ is not 2-automatic, which is open and implies Problem 1 by the kit. No technique
gives a space lower bound of this kind for an explicit function, for the reasons that block time lower bounds ([the
Problem 3 barrier](../../negative-results/complexity/problem-three-barrier.md)): the input has only $\log_2 n + 1$
digits, so order $\sqrt{n}$ is exponential in the input length. Williams's simulation of multitape time $t$ in space
$O(\sqrt{t \log t})$ is weaker here: simulating Rule 30 row by row takes multitape time of order $n^2$, which gives
space of order $n \sqrt{\log n}$, more than the simulation itself uses.

Statement 3 is proved in Lean in the kit. A Lean proof of statements 1 and 2 would need Cook and Mertz's algorithm and
Paterson's simulation, which can build on the crossing sequences of the kit's `OneTapeGap`; the kit has the block tree.

## Sources

- M. S. Paterson, [Tape bounds for time-bounded Turing machines](https://doi.org/10.1016/S0022-0000(72)80017-5),
  *Journal of Computer and System Sciences* 6(2), 116 to 124 (1972).
- J. Cook and I. Mertz, [Tree evaluation is in space O(log n · log log n)](https://doi.org/10.1145/3618260.3649664),
  STOC 2024, 1268 to 1278.
- R. Williams, [Simulating time with square-root space](https://arxiv.org/abs/2502.17779), STOC 2025.
- [The literature on complexity](../../literature/complexity.md#the-lower-bound-landscape).
