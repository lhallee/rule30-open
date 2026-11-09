---
title: A closed set of rows that contains the single cell's orbit and no row whose center repeats a block w exists exactly when the w-periodic stretches of the center column are bounded, so no compact certificate excludes a block unless the center column avoids long stretches of it
category: columns
problems: [1, 2]
status: negative
kind: barrier
---

# A closed set of rows that contains the single cell's orbit and no row whose center repeats a block w exists exactly when the w-periodic stretches of the center column are bounded, so no compact certificate excludes a block unless the center column avoids long stretches of it

**Question.** Many routes toward Problem 1 look for a certificate that a block cannot repeat forever in the center
column: a set of rows, defined by local constraints, that contains every row of the single cell's orbit and no row
whose center repeats the block (window locks, sheaf sections, Conley index pairs, traps, backgrounds). Such sets are
closed. When can a closed set do this job?

**Notation.** $X = \{0, 1\}^{\mathbb{Z}}$ with the product topology, $F$ is Rule 30, $\delta$ the single black cell,
$O = \{F^t \delta : t \ge 0\}$ its orbit and $\omega(\delta)$ its omega-limit set, so that the closure of $O$ is
$O \cup \omega(\delta)$ (the kit's `Genericity.infinite_omegaLimit_seed`: $\omega(\delta)$ is infinite). For a
primitive block $w$ of period $P$, $\mathrm{Inv}_w$ is the set of rows whose center trace $k \mapsto (F^k x)_0$ is
$k \mapsto w_{(k + r) \bmod P}$ for some phase $r$: a closed set, not empty (the kit's `Genericity.surjective_trace`).
$\ell_w(c)$ is the supremum of the lengths of the factors of the center column $c$ that are factors of $w^\infty$.

## Outcome

**Theorem (proved on paper).**

1. Problem 1 for $w$ (no eventual repetition of $w$) holds exactly when $O$ misses $\mathrm{Inv}_w$.
2. If $c$ is not eventually $w$-periodic, $\omega(\delta)$ meets $\mathrm{Inv}_w$ exactly when $\ell_w(c) = \infty$.
3. A closed set containing $O$ and missing $\mathrm{Inv}_w$ exists exactly when $\ell_w(c) < \infty$. Then one such set
   is clopen: the rows whose center trace on the times $0, \dots, \ell_w(c)$ is not a factor of $w^\infty$, a single
   finite-window check.
4. The same holds through any continuous readout: if $\pi : Y \to X$ is continuous and a compact $K \subseteq Y$ has
   $\pi(K) \supseteq O$ and $\pi(K) \cap \mathrm{Inv}_w = \emptyset$, then $\ell_w(c) < \infty$.

*Proof.* (1) is the definition: $F^T \delta \in \mathrm{Inv}_w$ exactly when $c$ repeats $w$ from time $T$. (2) If
$\ell_w(c) = \infty$ and $c$ is not eventually $w$-periodic, every stretch is finite, so stretches of every length $n$
start at times $t_n \to \infty$; by pigeonhole infinitely many have one phase $r$, and a limit point $y$ of these
$F^{t_n} \delta$ lies in $\omega(\delta)$ and has $(F^k y)_0 = \lim c(t_n + k) = w_{(k + r) \bmod P}$ for every $k$,
since the center trace up to time $k$ reads only the cells $-k, \dots, k$. Conversely a limit $y \in \mathrm{Inv}_w$ of
rows $F^{t_n} \delta$, $t_n \to \infty$, makes $c(t_n), \dots, c(t_n + k)$ a factor of $w^\infty$ for each $k$ and large
$n$. (3) A closed set containing $O$ contains its closure $O \cup \omega(\delta)$, so one exists exactly when both miss
$\mathrm{Inv}_w$, by (1) and (2) exactly when $\ell_w(c) < \infty$ (an eventually $w$-periodic $c$ has
$\ell_w(c) = \infty$). Every factor of $c$ of length $\ell_w(c) + 1$ breaks $w$, which gives the clopen set. (4)
$\pi(K)$ is compact, hence closed; apply (3). $\square$

**Rows with a leftmost black cell** (proved on paper). The rows with a leftmost black cell are dense in $X$, and
$\mathrm{Inv}_w$ is not empty, so no closed set contains all of them and misses $\mathrm{Inv}_w$, for any block,
unconditionally. Every theorem that excludes a block for all such rows, as the kit's run bounds and this repository's
block exclusions do, needs a property that no closed set has: in practice the finite left end of the row, climbed
through the compact sets $R_m$ of rows white left of $-m$ (with $F(R_m) \subseteq R_{m+1}$). The exclusion of $w$ on
these rows holds exactly when for every $m$ there is a time $H(m)$ by which every row of $R_m$ has broken $w$ in its
center trace; compactness makes each $m$ a finite computation, and the content of the theorem is the uniformity in $m$.
Jen's argument, two periodic columns forcing periodicity against the left edge, is of this kind.

**Automata** (proved on paper). A safety property of $c$ (an omega-regular property recognized by a deterministic
automaton all of whose states accept) that no eventually $w$-periodic word has exists only if $\ell_w(c) < \infty$: in a
stretch longer than $P$ times the number $q$ of states, two of the positions $s, s + P, \dots, s + qP$ have the same
state, and repeating the loop between them forever gives an accepted, eventually $w$-periodic word. Recurrence
properties can exclude $w$ without bounded stretches ("11 occurs infinitely often" excludes alternating tails), but
every nonempty omega-regular language contains an eventually periodic word, so no omega-regular property of $c$
implies Problem 1 for all blocks at once.

**Problem 2** (proved on paper). Every limit of the averages $\frac{1}{N} \sum_{t < N} \delta_{F^t \delta}$ of point
masses is $F$-invariant and carried by $\omega(\delta)$. If $\omega(\delta)$ contains the white row, the point mass
there is an $F$-invariant measure carried by $\omega(\delta)$ with no black cell at 0, so an argument that bounds the
density through the invariant measures that the orbit closure carries cannot prove Problem 2, or even a positive lower
density of black cells; it has to use which measures are limits of the averages. $\omega(\delta)$ contains the white row
exactly when for every $r$ the rows at arbitrarily late times are white on $-r, \dots, r$, which makes the center white
for $r + 1$ steps in a row, since a white cell between two white cells stays white.

## What it means

Whether $\ell_w(c)$ is finite is open for every block. For fair coins the longest stretch of a fixed periodic pattern
among the first $N$ cells grows like $\log_2 N$, so under the fair-coin picture every block has unbounded stretches in
$c$ (a heuristic) and then, by (3) and (4), no compact certificate, in any compact extension with a continuous readout,
excludes any block for the single cell. A certificate that is a closed set of rows can exclude a block only if the
center column has bounded stretches of it, a statement at least as strong as the exclusion and false for fair coins;
and for all rows with a leftmost black cell no closed certificate exists at all. A proof has to use a property that is
not closed, such as the finiteness of the row, as Jen's argument does. The finite-window methods tried in this
category stopped for reasons found case by case ([window locks](window-locks.md), [sheaf sections](sheaf-sections.md),
[the Conley index](conley-index.md)); this criterion bounds what any method of that kind can reach.

The open statements this repository reduces Problem 1 to have the same shape: a nonempty closed set defined by local
constraints, the halves that never enter a trap ([background halves](../../findings/columns/background-halves.md) notes
that this set is closed) or the survivors of a left-half check, contains no finite half. Compactness turns each width
into a finite check, and the uniform statement needs an induction on the width that nobody has.

The repository uses compactness inside single routes ([background halves](../../findings/columns/background-halves.md),
`WedgeLadder`), and the kit has the omega-limit forms of Problem 1 (`Genericity`); neither states the criterion (3) or
its extension (4).
