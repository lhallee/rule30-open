---
title: SmallRW, the six small lengths of the kit's rotated wedge hypothesis, holds, so the kit's period-two exclusion needs only BWH
category: period-two
problems: [1]
status: proved
lean: Rule30Open.PeriodTwo.WedgeSmall
headline: [wedge_small_rw, wedge_rw_of_large, wedge_forced, wedge_one_child]
kit: new
kit_modules: [Rule30WedgeBridge, Rule30SEPToPeriodTwo]
evidence: [computations/wedge_hypotheses.py, computations/wedge_hypotheses.c]
---

# SmallRW, the six small lengths of the kit's rotated wedge hypothesis, holds, so the kit's period-two exclusion needs only BWH

The kit's main branch, from commit
[cd5466b](https://github.com/WolframInstitute/Rule30PrizeKit/blob/cd5466bb62874dd15a240ae9fe4891663884f8f1/lean/Ruliology/CellularAutomata/Rule30WedgeBridge.lean)
on ([kit pull requests](../../literature/kit-pull-requests.md), #76), works with streams $e : \mathbb N \to \{0,1,2,3\}$, the
table $\varphi$ of the backward step on pairs of cells, $\partial q = 3 - q$, the inverse cone
$C(0, j) = \partial e_j$, $C(1, j) = \varphi(e_j, \partial e_{j+1})$, $C(t+2, j) = \varphi(C(t, j+1), C(t+1, j+1))$, the
inverse $I(t) = C(t, 0)$, the peel $(Px)(t) = \varphi(x_t, x_{t+1})$ and the wedge $W_n e = P^n I$. A symbol is binary
when it is 1 or 2. `RWWitness n r c e` says: $e_0, \dots, e_{2n+r+1}$ are binary, no 1 follows a 1 at a position
$i \ge n$, $W_n e(t) = c$ for $t < n + r + 2$, and $e_{2n+r-1} = 1$, $e_{2n+r} = 2$. `RW` says no stream is a witness
for $n \ge 1$, $r \le 2$, $c \in \{2, 3\}$, and `SmallRW` is its case $n < 7$. The kit proves
`bwh_implies_rw : BWH → SmallRW → RW` and, in `Rule30SEPToPeriodTwo`,
`center_not_eventually_period_two_of_bwh (hb : BWH) (hs : SmallRW)`: the official center column is not eventually of
period two. It leaves `SmallRW` to finite certificates.

The pinned kit has none of these modules, so `Rule30Open.WedgeKit` restates `Sym`, `phi`, `boundary`, `cone`,
`inverse`, `peel`, `peelPow`, `wedge`, `binary`, `constantTail`, `BinaryPrefix`, `ConstantWedge`, `HardCoreJunction`,
`RWWitness`, `BWH`, `SmallRW` and `RW` verbatim from the kit, with the kit's proofs of `cone_locality`,
`inverse_prefix` and `peelPow_locality`. They are definitionally the kit's: the proof of `wedge_small_rw` proves the
kit's `SmallRW` once the namespace is renamed.

## Results

- **`wedge_small_rw : SmallRW`.** For $1 \le n \le 6$, $r \le 2$ and $c \in \{2, 3\}$ no stream is an
  `RWWitness n r c`. With the kit's `center_not_eventually_period_two_of_bwh`, `BWH` alone excludes an eventual period
  two of the center column.
- **`wedge_rw_of_large`.** `RW` follows from its cases $n \ge 7$.
- **`wedge_forced`** (forced runs). If two streams agree below $k \ge n$ and $W_n e(k - n) = W_n f(k - n)$, then
  $e_k = f_k$. **`wedge_one_child`**: of the four symbols that can follow a prefix of length $k \ge n$, at most one
  gives the wedge value $c$ at $k - n$.

## The argument

**Forced runs.** $\varphi(a, \cdot)$ is a bijection of the four symbols for every $a$ (`wedge_phi_cancel`, by
`decide`), and so is $\partial$. In $W_n e(k - n) = \varphi(P^{n-1}I(k-n), P^{n-1}I(k-n+1))$ the first argument reads
$I$ only below $k$ (`peelPow_locality`), so equal values give $P^{n-1}I(k-n+1)$ equal; by induction on $n$
(`peelPow_newest`) $I_e(k) = I_f(k)$. In $I(k) = C(k, 0) = \varphi(C(k-2, 1), C(k-1, 1))$ the first argument reads $e$
only below $k$ (`cone_locality`), so the same induction on the cone (`cone_newest`) reaches $C(0, k) = \partial e_k$.

**A memoized cone.** The kit's recursion for $C$ recomputes each entry along every path, so its unfolding grows like
the Fibonacci numbers in the length of the word, and $P^n$ doubles it $n$ times. For a finite word $w$ of length $L$, `inverseL w` builds the cone row by row:
row 0 is $\partial w$, row 1 is $\varphi(w_j, \partial w_{j+1})$, and row $t + 2$ is the entrywise $\varphi$ of rows $t$
and $t + 1$ shifted by one (`coneHeads` keeps the head of each row). `peelPowL` peels a list. `coneHeads_spec`,
`inverseL_spec` and `peelPowL_spec` prove, by induction on the rows and the peels, that entry $t$ of
`wedgeL n w` is $W_n e(t)$ for every stream $e$ that starts with $w$ and every $t + n < L$ (`wedgeL_spec`).

**The search.** `rwTest n r c w` checks every condition of `RWWitness n r c` that reads only the first $|w|$ symbols:
the hard-core pairs below $|w|$, the two fixed symbols if they lie below $|w|$, and the wedge values $W_n(t) = c$ for
$t + n < |w|$ and $t < n + r + 2$, through `wedgeL`. `wsearch test f w` is a depth-first search: it succeeds at $w$ when
`test w` fails, or when it succeeds at $w 1$ and at $w 2$ with one symbol less of depth. `wsearch_sound`: if the search
succeeds at the prefix of length $k$ of a stream $e$ whose symbols from $k$ to $k + f - 1$ are binary, then some prefix
of $e$ of length $k$ to $k + f$ fails the test. A witness passes the test at every length up to $2n + r + 2$
(`rwTest_of_witness`, by `wedgeL_spec` and `pre_getD`), so a search of depth $2n + r + 2$ from the empty word that
succeeds excludes every witness (`no_rw_witness_of_search`). The kernel evaluates the six searches of each $n$
(`small_rw_n1`, ..., `small_rw_n6`, by `decide +kernel`).

The search is small because the runs are forced. The first $n$ symbols are free; from there `wedge_one_child` leaves at
most one binary child of each prefix that passes the wedge test, so each case explores at most $2^n \le 64$ forced runs
on words of at most 16 symbols, and the other child of each node fails at once. The module builds in about 10 seconds,
the kernel evaluations included.

## What the kit has

`Rule30WedgeBridge` states `SmallRW` and does not prove it; its controls `small_control_table` and
`small_bwh_control` show that the bound $n \ge 7$ of `BWH` cannot be lowered to 5 and `hard_core_guard_control` that
the guard of `RW` is needed. No module of the pinned kit or of the main branch at
[93d98bb](https://github.com/WolframInstitute/Rule30PrizeKit/commit/93d98bb) proves `SmallRW`, the forced-run property
or the row-by-row cone. `BWH` and `RW` for large $n$ stay open: [the forced runs](../../findings/period-two/wedge-forced-runs.md)
finds no witness of `BWH` for $7 \le n \le 31$ and none of `RW` for $n \le 26$, and
[no local mechanism](../../negative-results/period-two/wedge-survivor-mechanism.md) records why a finite certificate
of this kind does not reach every $n$.
