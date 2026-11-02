---
title: The local patterns that seemed to kill the forced runs of the wedge hypotheses reduce to one rule, a run dies exactly when c is off an edge of a square, and the four edges occur about equally often
category: period-two
problems: [1]
status: negative
kind: dead-end
evidence: [computations/wedge_hypotheses.py, computations/wedge_hypotheses.c]
---

# The local patterns that seemed to kill the forced runs of the wedge hypotheses reduce to one rule, a run dies exactly when c is off an edge of a square, and the four edges occur about equally often

**Question.** The kit's hypotheses `BWH` and `RW` exclude period two of the center column (with `SmallRW`, which
[WedgeSmall](../../Rule30Open/PeriodTwo/WedgeSmall.md) proves). Each is a statement about $2^n$ forced runs
([the forced runs](../../findings/period-two/wedge-forced-runs.md)): past $n$ free binary symbols, each symbol is the
one that keeps the wedge equal to $c$, and a run dies when that symbol is not binary (or, for `RW`, breaks the hard-core
guard). A finite search settles one $n$ at a time. A proof for every $n$ would want a local reason why runs die, and two
patterns looked like one:

- **The first-argument condition.** For binary $b$, $\varphi(a, b)$ takes the values $\{1, 3\}$, $\{2, 1\}$,
  $\{2, 0\}$, $\{2, 1\}$ for $a = 0, 1, 2, 3$, so the value 3 comes from a binary second argument only when $a = 0$.
- **The $n = 15$ barrier.** At $n = 15$, $c = 3$, the longest runs stop at length 31, where both binary symbols give the
  wedge values 2 and 0.

**What was done.** `edge_census` records, at every forced step of every run, the two wedge values $E_k$ of the binary
choices of $e_k$, the two values $E'_k$ of the second argument of the last $\varphi$, the first argument
$a = P^{n-1}I(k - n)$, and whether the run survives; `forced_runs`, `clumps` and `head_depth` give the survivors and
their clumps. All runs at $n = 14$ for the census, $8 \le n \le 24$ for the clumps.

**Outcome.**

- A step's outcome is decided by one edge. $\varphi(a, \cdot)$ and $\partial$ are symmetries of the square
  $0 - 3 - 1 - 2$ and $\{1, 2\}$ is an edge of it, so $E_k$ is always an edge, and the census confirms that a run
  survives exactly when $c \in E_k$, at every one of the 32,724 ($c = 2$) and 32,374 ($c = 3$) steps at $n = 14$. The
  four edges occur 8156, 8228, 8158, 8182 times ($c = 2$) and 8022, 7968, 8474, 7910 times ($c = 3$): each value of
  $c$ lies on two of them, and the survivors halve at each step.
- The first-argument condition is the special case $E'_k = \{1, 2\}$ of that rule. It holds on 24.2% ($c = 2$) and
  24.8% ($c = 3$) of the steps, and there a run with $c = 3$ survives exactly when $a = 0$, as the table says; on the
  other steps the value 3 comes from the other first arguments. It predicts nothing that the edge rule does not.
- The $n = 15$ barrier is one clump. The 18 runs that reach length 31 agree from position 5 on, so they meet the same
  edge, $E_{31} = \{0, 2\}$, and die together. The deepest clumps at other $n$ die at other lengths and edges (the
  table of $M(n, c)$ in the finding), with no common position relative to $n$ or the horizon.

**Where it stops.** The step that would kill survivors is a statement about the sequence of edges $E_k$ along the
forced runs: that $c$ falls off the edge before the horizon for every free prefix. The edges are products of the
symmetries indexed by the earlier entries of the cone, and over all runs they occur about equally often (each
within 5% of a quarter of the steps at $n = 14$). *Assessment:* so a condition on a few entries is unlikely to force a
death. `BWH` and `RW` are fair-coin statements about these sequences, like the
center-column statements that [no finite certificate settles](no-finite-certificate.md): the data support them (no
witness of `BWH` for $7 \le n \le 31$, none of `RW` for $n \le 26$, where the longest run past the free prefix
falls short of the $n + r + 2 \ge n + 2$ symbols a witness needs by 3 at $n = 9$ and by 13 at $n = 26$), but nothing found here bounds the runs for every $n$. The
growing margin of `RW` is the fair-coin prediction, not a mechanism. A route that wants `BWH` or `RW` needs a
uniform statement about the edge sequence; a larger finite search only adds values of $n$.
