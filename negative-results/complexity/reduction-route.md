---
title: A proof of Problem 3 by a reduction from a problem hard for exponential time would make the center column constant on an infinite set of times decidable in polynomial time, a structure that fair coins do not have
category: complexity
problems: [3, 1, 2]
status: negative
kind: barrier
---

# A proof of Problem 3 by a reduction from a problem hard for exponential time would make the center column constant on an infinite set of times decidable in polynomial time, a structure that fair coins do not have

**Question.** [The barrier entry](problem-three-barrier.md) names the one known way an affirmative answer to Problem 3
could come within reach: a reduction showing that computing $c$ is hard for exponential time, which with input size
linear in the number of digits gives `Problem3Robust` by the time hierarchy theorem
([the hardness hypotheses](hardness-hypotheses.md)). What would such a reduction say about the center column itself?

**Setting.** Write $\mathrm{bin}(n)$ for the binary digits of $n$, $L_b = \{\mathrm{bin}(n) : c(n) = b\}$ for
$b \in \{0, 1\}$, and $\mathrm{E} = \mathrm{DTIME}(2^{O(m)})$, $m$ the input length. Simulation computes $c(n)$ in time
$O(n^2) = 2^{O(m)}$, so $L_0$ and $L_1$ are in $\mathrm{E}$. A set of times is *decidable in polynomial time* when a
machine decides it in time polynomial in the number of digits.

## Outcome

**Theorem (proved on paper).** If $L_1$ is hard for $\mathrm{E}$ under polynomial-time many-one reductions, then for
each $b \in \{0, 1\}$ there is an infinite set $S_b$ of times, decidable in polynomial time and with at most one element
of each digit length, on which $c$ equals $b$. So $L_1$ is not P-bi-immune.

This is the classical theorem that sets complete for $\mathrm{E}$ under these reductions are not P-immune (Berman,
FOCS 1976, seen as a bibliographic record only), applied to $L_1$ and to $L_0$; the proof below is self-contained.

*Proof.* Write $H = L_1$. Fix an enumeration $f_1, f_2, \dots$ of clocked transducers, $f_i$ stopped after
$|x|^i + i$ steps, such that every function computable in polynomial time equals some $f_e$ on all inputs, and let
$X_i = \{1^i 0 z : z \in \{0, 1\}^*\}$, so that $x \in X_i$ determines $i$. Define a set $D$: for $x \in X_i$ with
$|x|^i + i \le 2^{|x|}$, compute $y = f_i(x)$; if $|y| \le |x|$, put $x$ in $D$ exactly when $y \notin H$, and if
$|y| > |x|$, put $x$ in $D$. Put every other string in $D$. Computing $f_i(x)$ takes at most $2^{|x|}$ simulated steps,
and $H$ is queried only on strings of length at most $|x|$, so $D \in \mathrm{E}$.

By hypothesis $D$ reduces to $H$ by some $f_e$. Let $x \in X_e$ be long enough that $|x|^e + e \le 2^{|x|}$. If
$|f_e(x)| \le |x|$, the definition gives $x \in D$ exactly when $f_e(x) \notin H$ and the reduction gives $x \in D$
exactly when $f_e(x) \in H$, a contradiction. So $|f_e(x)| > |x|$, so $x \in D$, so $f_e(x) \in H$. Put
$h(z) = f_e(1^e 0 z)$: for every $z$ of length at least some $L$, $h(z) \in H$ and $|h(z)| \ge |z| + e + 2$. Iterate
from $z_0 = 0^L$. Every $z_k = h^k(z_0)$ with $k \ge 1$ lies in $H$, so it is the binary expansion of a time at which
$c$ is black, and the lengths increase strictly, so $S_1 = \{z_k : k \ge 1\}$ is infinite with at most one element of
each length. To decide whether $w \in S_1$, compute $z_1, z_2, \dots$ while $|z_k| \le |w|$: at most $|w|$ steps, each
in time polynomial in $|w|$.

For $b = 0$: $\mathrm{E}$ is closed under complement, so every set of $\mathrm{E}$ reduces to the complement of $L_1$
by the maps that reduce its complement to $L_1$. Composed with the map that sends a string that is not a binary
expansion to $\mathrm{bin}(2)$, where $c(2) = 0$, and every other string to itself, these reduce every set of
$\mathrm{E}$ to $L_0$, and the same argument gives $S_0$. $\square$

**One hypothesis behind all three problems** (proved on paper). For a class $\mathcal{C}$ of sets of times, let
$S_{\mathcal{C}}$ say that along every infinite $A \in \mathcal{C}$ the fraction of black cells among the first $N$
elements of $A$ tends to $1/2$. Let $\mathcal{C}_P$ be the sets decidable in polynomial time, and $\mathcal{C}_1$ the
sets that a machine of the kit's model (`Rule30Problem3`) decides within $C(n + 1)$ steps for some $C$;
$\mathcal{C}_P \subseteq \mathcal{C}_1$, since time polynomial in $\log n$ is below $C(n + 1)$ for a large $C$. Then:

- $S_{\mathcal{C}_P}$ implies Problem 2 (take $A$ to be all times) and Problem 1 (if $c$ had period $P$ from $T$, it
  would be constant on the times $n \ge T$ with $n \equiv r \pmod P$, a set decidable in polynomial time).
- $S_{\mathcal{C}_1}$ implies the kit's `Problem3`: a machine that computes $c$ within $C(n + 1)$ steps decides the set
  of black times within the same bound, and that set is infinite (no column of the single cell is eventually white)
  with fraction 1. With the time bounds $o(n)$ and $n^{o(1)}$ in place of $C(n + 1)$, the same argument derives
  `Problem3Verbal` and `Problem3Robust` from $S_{\mathcal{C}}$ for the smaller classes these bounds define.
- $S_{\mathcal{C}_P}$ rules out the reduction route, by the theorem, and gives $L_1 \notin \mathrm{P}$ (otherwise the
  black times themselves form a set of $\mathcal{C}_P$ with fraction 1). So it also gives the rungs below Problem 3 of
  [restricted models](restricted-models.md): $c$ is not 2-automatic, nor $k$-automatic for any $k$, and is constant on
  no dyadic progression, since the sets these would give are decidable in polynomial time.
- $S_{\mathcal{C}}$ holds with probability 1 for the center column of a uniformly random row, for every countable class
  $\mathcal{C}$: that column is a sequence of independent fair coins (the kit's `Mixing.measurePreserving_line`), so
  the strong law of large numbers holds along each infinite $A$.

## What it means

The theorem is unconditional; the barrier is conditional on the center column being as random as every test in this
repository finds. A proof of Problem 3 by a polynomial-time many-one reduction from a problem hard for $\mathrm{E}$,
the form that the barrier entry and the hardness hypotheses name as what would help, would itself be a structure
theorem about the single seed: two explicit infinite families of times, one of each digit length at most, recognized
from their digits in polynomial time, on which $c$ is constant, black on one and white on the other. Nothing of the
kind is known, and the fair-coin statement $S_{\mathcal{C}_P}$, which implies Problems 1 and 2, forbids it. So under
the fair-coin picture the reduction route to Problem 3 is closed, and what remains is:

- a proof of some $S_{\mathcal{C}}$ itself, a statement about fair coins of the kind every route in this repository
  ends at, which with $\mathcal{C}_1$ would give all three problems at once;
- a lower-bound technique for an explicit function in $\mathrm{E}$ that is not complete for it, of which none is known;
- reductions of another kind: the theorem says nothing about truth-table reductions, for instance through a parity of
  several values of $c$, and whether a structure of $c$ would follow from those is not settled here.

The repository's other entries on Problem 3 treat a reduction only as an unavailable tool
([the barrier entry](problem-three-barrier.md), [the hardness hypotheses](hardness-hypotheses.md)); the kit has no
statement about completeness or immunity of the center column.
