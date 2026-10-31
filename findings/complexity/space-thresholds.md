---
title: The center column is computed in space √(n log n), and each simulation sets a threshold that a space lower bound must pass
category: complexity
problems: [3, 1]
status: paper
formalization: partial
evidence: [computations/space_window.py]
---

# The center column is computed in space √(n log n), and each simulation sets a threshold that a space lower bound must pass

Measure the work space of a deterministic machine that reads the binary digits of $n$ and outputs $c(n)$, as in [the
space ladder](space-ladder.md). No single machine is best for every $n$, so $S$ below is notation for statements about
all machines that compute $c$: $S(n) = O(f)$ means that some machine computes $c$ in space $O(f(n))$; $S(n)$ is not
$O(f)$ means that no machine does; and $S(n) \ge \varepsilon f(n)$ for infinitely many $n$ means that every machine
that computes $c$ uses at least $\varepsilon f(n)$ space for infinitely many $n$, with $\varepsilon > 0$ allowed to
depend on the machine, that is no machine computes $c$ in space $o(f)$. Cook and Mertz's tree evaluation algorithm, in
the form that Williams states it, puts $S(n) = O(\sqrt{n \log n})$, a factor $\sqrt{\log n}$ above $\sqrt{n}$; the
weaker form of their bound gives $\sqrt{n} \log n$. Each simulation of time by space turns a statement of
Problem 3 into a lower bound for $S$ at a different height. No lower bound for $S$ beyond a constant is known, so none of
the thresholds below is passed.

## Statement

1. **Space that suffices.** $S(n) = O(\sqrt{n \log n})$. Sibgatullin and Williams (ECCC TR26-223, unrefereed) prove the
   same bound for every one-dimensional cellular automaton, from the initial row (their Theorem 1.4).
2. **Thresholds.** Each line is a lower bound on $S$ that would give the statement on its left, with the simulation that
   transfers it.

   | Statement | Follows if no machine computes $c$ in space | Simulation |
   |---|---|---|
   | `Problem3` of the kit (one tape, time $C(n + 1)$) | $O(\sqrt{n})$ | Paterson 1972; Hopcroft and Ullman 1968 |
   | `Problem3Verbal` (one tape, time $o(n)$) | $o(\sqrt{n})$ | the same |
   | `Problem3` | $O(n^{2/5} \log^{K} n)$ for any fixed $K$ | OpenAI family 137, unrefereed |
   | time $o(n)$ on multitape machines | $o(\sqrt{n \log n})$ | Williams 2025 |
   | `Problem3Robust` (time $n^{o(1)}$) | $n^{o(1)}$ | space at most time plus input length |
   | Problem 1 | $o(\log \log \log n)$, that is $o(\log \log \ell)$ in the number $\ell$ of digits | the kit's `OfflineGap` |

3. **The windows.** With statement 1, a lower bound for the kit's `Problem3` through Paterson must show that $S(n)$ is not
   $O(\sqrt{n})$ while $S(n) = O(\sqrt{n \log n})$: it has room of a factor $\sqrt{\log n}$ at most. Through family 137, if
   it holds, the room is polynomial, from $n^{2/5}$ to $n^{1/2}$. For multitape time $o(n)$ there is no room: the
   threshold $o(\sqrt{n \log n})$ equals the upper bound, so the statement follows if the upper bound is tight for
   infinitely many $n$, that is if $S(n) \ge \varepsilon \sqrt{n \log n}$ for some $\varepsilon > 0$. For `Problem3Robust` any lower bound $S(n) \ge n^{\delta}$ for infinitely many $n$, with
   $0 < \delta \le 1/2$, would do.
4. **What closes a route.** If tree evaluation with fan-in 3, height $h$ and $b$-bit nodes runs in space $O(h + b)$ on the
   block trees of Rule 30, then $S(n) = O(\sqrt{n})$, and the routes through Paterson's theorem to `Problem3` and through
   Williams's simulation to multitape time $o(n)$ both close. The thresholds below $\sqrt{n}$ stay open: $o(\sqrt{n})$
   for `Problem3Verbal`, $n^{2/5} \log^{K} n$ through family 137, and $n^{o(1)}$ for `Problem3Robust`.
5. **Nothing else gains.** Grouping levels of the tree (Goldreich's account of Stoeckl's improvement), regrouping blocks
   by the light cone, and catalytic space (Henzinger, Pyne and Ragavan) do not lower the order $\sqrt{n \log n}$ of
   the bound of statement 1; regrouping by the light cone changes only its constant.

## Proof

**Statement 1.** The kit's [`Rule30LightCone`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30LightCone.lean)
proves that the center cell at time $m b$ is the first entry of the root of a tree of height $m$ and fan-in 3 whose
nodes are $b$-bit blocks (`center_eq_root`, `block_step`), each node a fixed function of its three children computed by
running $b$ steps of Rule 30 on $3b$ cells, in space $O(b)$. For $n = m b + r$ with $r < b$ start the tree from row $r$,
whose blocks come from the single cell in space $O(b)$. Cook and Mertz's algorithm evaluates a tree of fan-in $d$, height
$h$ and $b$-bit nodes in space $O(d b + h \log (d b))$ (their Theorem 7, as Williams's Theorem 2.2 quotes it; Goldreich
states $O(b + h \log b)$ for $d = 2$). With $d = 3$ and $h = \lceil n / b \rceil$ the space is
$3 b + (n / b) \log_2 (3 b)$ up to constants. Setting the derivative to zero gives $b^2 \approx (n / 3) \log_2 (3 b)$, so
$b \approx \sqrt{n \log_2 n / 6}$, each of the two terms is about $\sqrt{3 n \log_2 n / 2}$, and the total is about
$\sqrt{6 n \log_2 n}$. This is Williams's balance, $b = \Theta(\sqrt{t \log t})$, applied to the block
tree instead of to a Turing machine. The ladder's weaker form, $(h + b) \log b$, is the bound of the ECCC text of Cook and
Mertz (their Theorem 10) and gives $\sqrt{n} \log n$ at $b = \sqrt{n}$.

[`computations/space_window.py`](../../computations/space_window.py) reads the $O$ as equality and minimizes over $b$.
It has no constant of the algorithm, so the ratios show growth, not bit counts:

| $\log_2 n$ | best $b$ | space over $\sqrt{n}$ | over $\sqrt{n \log_2 n}$ | over $n^{2/5}$ | weaker form over this one |
|---:|---:|---:|---:|---:|---:|
| 10 | $4.1 \times 10^{1}$ | 9.27 | 2.93 | 18.5 | 2.10 |
| 20 | $2.0 \times 10^{3}$ | 12.29 | 2.75 | 49.1 | 3.02 |
| 40 | $2.8 \times 10^{6}$ | 16.63 | 2.63 | 266 | 4.32 |
| 80 | $4.1 \times 10^{12}$ | 22.85 | 2.55 | 5,850 | 6.18 |
| 160 | $6.3 \times 10^{24}$ | 31.75 | 2.51 | $2.1 \times 10^{6}$ | 8.82 |
| 240 | $8.5 \times 10^{36}$ | 38.62 | 2.49 | $6.5 \times 10^{8}$ | 10.84 |

The ratio to $\sqrt{n \log_2 n}$ settles near $\sqrt{6} \approx 2.45$, the one to $\sqrt{n}$ grows like $\sqrt{6 \log_2 n}$, and
the one to $n^{2/5}$ grows without bound, which is the polynomial window of statement 3.

**Statement 2.**
- *Paterson.* As in the ladder: time $C(n + 1)$ on inputs of $m = \lfloor \log_2 n \rfloor + 1$ digits is at most
  $T(m) = 2 C \cdot 2^m + m^2$ with $T(m) \ge m^2$, so a deterministic machine uses space $O(\sqrt{T}) = O(\sqrt{n})$; for
  time $o(n)$ the space is $o(\sqrt{n})$.
- *Family 137.* The paper's Theorem 1 gives space $O(T^{2/5} \log^{K} T)$ for a fixed one-tape machine whose initial tape
  may hold the input, with a supplied binary cap $T$; here $T = C (n + 1)$ is computed from $n$ in logarithmic space and
  the digits of $n$ are read by rescanning. The statement is a claim until the paper is checked, and the kit's convention
  that a machine halts by a transition, not in a state, is not traced through it.
- *Williams.* Multitape time $T$ is in space $O(\sqrt{T \log T})$ (Theorem 1.1), so $T = o(n)$ gives space
  $o(\sqrt{n \log n})$. A lower bound $S(n) \ge \varepsilon \sqrt{n \log n}$ for infinitely many $n$ contradicts it.
  Statement 1 shows that this is the largest lower bound that is true, if any is.
- *`Problem3Robust`.* No simulation is needed: a one-tape machine that runs $T$ steps on $\ell$ input cells visits at
  most $T + \ell + 1$ cells, so time $T = n^{o(1)}$ uses space $n^{o(1)}$. So $S(n) \ge n^{\delta}$ infinitely often
  rules out every such machine.
- *Problem 1.* The direction used is the base-2 half of the kit's Lean equivalence
  `problem1_iff_no_small_space_digit_deciders`, whose space is measured in the number $\ell$ of digits: a decider in
  space $o(\log \log \ell)$ makes the digit language regular (`isRegular_iff_exists_small_space_decider`), so $c$ is
  2-automatic (`isRegular_digitLang_iff`), and if $c$ is not 2-automatic Problem 1 holds (`problem1_of_not_automatic`).

**Statement 4.** Tree evaluation in space $O(h + b)$ turns the sum $3 b + h \log (3 b)$ into $O(b + h)$ and $b = h = \sqrt{n}$
gives $O(\sqrt{n})$. Tree evaluation with logarithmic space for $h = \Theta(b)$ is the open problem of whether TreeEval
is in $\mathrm{L}$ (Cook and Mertz are a factor $\log b$ away on the height term only; Henzinger, Pyne and Ragavan reach
logarithmic free space with catalytic space $2^{\log^{\varepsilon} n}$ and polynomial time).

**Statement 5.** Group $h'$ levels of the tree into one node of fan-in $3^{h'}$, each a function computed by evaluating the
subtree in space $O(3^{h'} b)$. Goldreich's Theorem 1 gives space $O(3^{h'} b + h + (h / h') \log b)$. At the best $b$ the sum is
proportional to $\sqrt{3^{h'} / h'} \cdot \sqrt{n \log n}$, and $3^{h'} / h'$ is smallest at $h' = 1$ among the positive
integers (3 against 4.5 at $h' = 2$), so in this model the grouping does not help the block tree; it helps when
$h \gg b / \log b$, and the block tree has $h \approx 3 b / \log_2 b$ at its best $b$, the balanced case. Regrouping by
the light cone does better in the constant only: a $b$-cell block after $h' b$ steps depends on $2 h' + 1$ blocks
(`block_step` is $h' = 1$), so the tree has fan-in $2 h' + 1$, height $n / (h' b)$ and nodes computed in space
$O((2 h' + 1) b)$. Reading the $O$ as equality, $(2 h' + 1) b + (n / (h' b)) \log_2 ((2 h' + 1) b)$ is smallest near
$\sqrt{(2 (2 h' + 1) / h') \, n \log_2 n}$, which falls from $\sqrt{6} \sqrt{n \log_2 n}$ at $h' = 1$ toward
$2 \sqrt{n \log_2 n}$ as $h'$ grows, the same order. Catalytic space is memory that is borrowed and restored, and the
published algorithm uses polynomial time and subpolynomial catalytic space beyond its logarithmic free space; it is not a
bound on the work space of a machine in the sense used here, and it does not lower the sum above.

## What it means

The route "a space lower bound gives Problem 3" has a window of a factor $\sqrt{\log n}$ for the kit's statement, and
none for time $o(n)$ on multitape machines. If tree evaluation is in logarithmic space on these trees, which is open,
the routes through Paterson's theorem to `Problem3` and through Williams's simulation to multitape time $o(n)$ both
close, and only the thresholds below $\sqrt{n}$, such as $o(\sqrt{n})$ for `Problem3Verbal`, stay open. If family 137 holds,
that route has a polynomial window, and a proof of $S(n) \ge n^{2/5 + \varepsilon}$ would be enough for `Problem3`.
Either way the underlying task is the same: a lower bound of polynomial size, $2^{\Omega(m)}$ in the number $m$ of
input digits, for one explicit function, which nothing here moves ([the Problem 3
barrier](../../negative-results/complexity/problem-three-barrier.md)).

The multitape line is the sharpest statement here: a space lower bound that matches the upper bound of statement 1 up
to a constant would give multitape time $\Omega(n)$ with no slack to spare, and that upper bound rests on one algorithm
that may still improve.

## Reproduce

```bash
python -m computations.space_window
```

The test `tests/test_space_window.py` checks the block-size search against the full minimum for small $n$. A Lean proof
of statement 1 would need Cook and Mertz's algorithm, which is not formalized in the kit; the block tree is.

## Sources

- J. Cook and I. Mertz, [Tree evaluation is in space O(log n · log log n)](https://doi.org/10.1145/3618260.3649664), STOC
  2024; SIAM Journal on Computing 2025.
- R. Williams, [Simulating time with square-root space](https://arxiv.org/abs/2502.17779), STOC 2025; Journal of the ACM
  73(3), 2026.
- D. Sibgatullin and R. Williams, [Space-efficient simulations beyond multitape Turing machines](https://eccc.weizmann.ac.il/report/2026/223/),
  ECCC TR26-223, 2026.
- O. Goldreich, [Solving tree evaluation in o(log n · log log n) space](https://eccc.weizmann.ac.il/report/2024/124/), ECCC
  TR24-124, 2024.
- A. Henzinger, E. Pyne and S. Ragavan, [Catalytic tree evaluation from matching vectors](https://arxiv.org/abs/2602.14320),
  arXiv:2602.14320, 2026.
- OpenAI, [family 137](../../literature/ai-proposed.md#openais-manuscript-collection), 2026.
- M. S. Paterson, [Tape bounds for time-bounded Turing machines](https://doi.org/10.1016/S0022-0000(72)80017-5), 1972.
- [The literature on complexity](../../literature/complexity.md#the-lower-bound-landscape).
