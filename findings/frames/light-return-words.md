---
title: Every periodic point of the right-edge map besides 0 and rain leaves rain through one state up to a time rotation, so the conjecture that rain is all is, for each even period, the finiteness of one tree; the two children of a node have children with the parity of the node's last word, the tree for period L contains the tree for L/2 with two children hung on each leaf, and it is finite to period 64 with depths 0, 1, 3, 4, 14, 103
category: frames
problems: [3]
status: paper
formalization: wanted
evidence: [computations/light_return_words.py]
---

# Every periodic point of the right-edge map besides 0 and rain leaves rain through one state up to a time rotation, so the conjecture that rain is all is, for each even period, the finiteness of one tree; the two children of a node have children with the parity of the node's last word, the tree for period L contains the tree for L/2 with two children hung on each leaf, and it is finite to period 64 with depths 0, 1, 3, 4, 14, 103

In the right-edge frame Rule 30 is $\Phi(y) = y \oplus (2y \lor 4y)$ on the 2-adic integers: bit $e$ of $\Phi(y)$ is
$y(e) \oplus (y(e-1) \lor y(e-2))$. A nonzero point with $\Phi^L(y) = y$ is, after dividing by a power of two, an odd
$y$, and its *words* $W_e(t) = $ bit $e$ of $\Phi^t(y)$, $t \in \mathbb{Z}/L$, satisfy $W_{-2} = W_{-1} = 0$,
$W_0 = 1 \cdots 1$ and

$$W_e(t+1) \oplus W_e(t) = (W_{e-1} \lor W_{e-2})(t) \qquad (t \in \mathbb{Z}/L).$$

The right side $R_e = W_{e-1} \lor W_{e-2}$ must have even weight, and then $W_e$ is one of two complementary words.
Call $(W_{e-1}, W_e)$ the *state*. The odd $y$ with $\Phi^L(y) = y$ are the infinite walks from $(0, 1\cdots1)$, and
the odd $y$ modulo $2^n$ with $\Phi^L(y) \equiv y$ are the walks $W_0, \ldots, W_{n-1}$ (checked against applying
$\Phi$ for $L = 2, 4, 8$ and $n \le 11$). *Rain* is the two walks in which every word from $W_1$ on alternates and
consecutive words from $W_1$ on are complementary; they are the points $2^m(\pm 1/3)$ of the conjecture under study,
that rain and 0 are the only periodic points ([edge periodic points](edge-periodic-points.md), proved there for
$128 \nmid L$). With $A$ alternating, the *rain states* are the four states the rain walks pass through after the
start: the two level-1 states $(1\cdots1, A)$ and the two states $(A, \lnot A)$, as in that finding. A node *has
children* when its right side has even weight.

## Proved

**1. Periods are powers of two; odd periods do not occur (known).** This is the kit's
`TFunctionCycles.per_eq_two_pow` (the cycle length modulo $2^n$ is a power of two), and the reduction of an odd period
to a fixed point, with 0 the only fixed point, is reduction (ii) of [edge periodic points](edge-periodic-points.md)
item 2, proved in Lean in [EdgeOddPeriods](../../Rule30Open/Frames/EdgeOddPeriods.md) (`fixed_point_eq_zero`,
`fixed_of_odd_period`, `odd_period_eq_zero`, `pow_two_period`). In words it reads: if $W_{e-1}$ and $W_{e-2}$ have
periods dividing $2^j$, then $W_e(t + 2^j) = W_e(t) \oplus s$ with $s$ the weight parity of $R_e$ over one block of
$2^j$, so $W_e$ has period dividing $2^j$ ($s = 0$) or exactly $2^{j+1}$ ($s = 1$); this is the single-cell step
`Rule30RightPeriods.shift_formula` of the kit read on the words, and it is the form Lemma 4 uses. (It needs the start
$W_{-1} = W_{-2} = 0$; rows black arbitrarily far right return after 12, 15 or 17 steps,
[LightLikeEntropy](../../Rule30Open/RandomRows/LightLikeEntropy.md).)

**2. One branch state.** Let $L \ge 2$ be even and $P = 0101\cdots$ the alternating word. $R_1 = W_0 = 1\cdots1$, so
$W_1 \in \{P, \lnot P\}$; $R_2 = 1\cdots1$ again, so $W_2$ alternates. From a level-1 rain state $(1\cdots1, A)$ and
from a rain state $(A, \lnot A)$, $A$ alternating, the right side is $1\cdots1$ and the two children are a rain state,
$(A, \lnot A)$ or $(\lnot A, A)$, and a *branch state*, $(A, A)$ or $(\lnot A, \lnot A)$. So every walk is rain until
it enters one of the two branch states, and $(\lnot P, \lnot P)$ is $(P, P)$ rotated by one time step, a rotation that
commutes with the recursion. Hence, by König's lemma (two children at most):

> For each even $L$, the only nonzero points of period dividing $L$ are the rain points $2^m(\pm 1/3)$ if and only
> if the tree $\mathcal{T}_L$ of walks from $(P, P)$ is finite. Its depth is the longest non-rain stretch; for
> $L = 2^k$ it is the transient $T_k$ of [edge periodic points](edge-periodic-points.md) item 3, which gives the exact
> bound: an odd seed agreeing with $\pm 1/3$ to exactly $m$ bits fails $\Phi^{2^k}(y) \equiv y \pmod{2^n}$ for every
> $n \ge m + T_k + 2$.

So for each $L$ the conjecture is the finiteness of one tree, and $L = 2^k$ is the only case (by 1). For $L = 4$ this
state analysis is the period-4 argument of that finding ([EdgePeriodFour](../../Rule30Open/Frames/EdgePeriodFour.md));
what is new here is that it holds for every even $L$ with the one branch state up to rotation. Where it stops for
$L \ge 8$ ($(P, P)$ no longer dies after one step) is
[edge-periodic classification](../../negative-results/frames/edge-periodic-classification.md) item 3 and Route 2.

**3. Which children have children.** Let $(u, v)$ have the children $(v, w)$ and $(v, \lnot w)$. Then
$|v \lor w| + |v \lor \lnot w| = 2|v| + (L - |v|) = |v| + L \equiv |v| \pmod 2$ for $L$ even. So if $|v|$ is odd,
exactly one child has children; if $|v|$ is even, both have children or neither does. This is one step only and says
nothing about whether the children's subtrees are infinite. (The identity is checked over all pairs of words of length
$L \le 8$, and the consequence on every node of $\mathcal{T}_L$ for $L \le 64$, `fertility_counts`. The case $|v|$
odd does not occur in $\mathcal{T}_8$ or $\mathcal{T}_{16}$; it occurs at 208 of the 527 inner nodes of
$\mathcal{T}_{32}$ and 20,640 of the 42,943 inner nodes of $\mathcal{T}_{64}$.)

**4. Doubling embeds $\mathcal{T}_{L/2}$ in $\mathcal{T}_L$.** Let $N = L/2$ be even and extend words on
$\mathbb{Z}/N$ periodically to $\mathbb{Z}/L$ (this sends $P$ to $P$). For a state $(u, v)$ on $\mathbb{Z}/N$, the
right side on $\mathbb{Z}/L$ has twice the weight, always even, and the solution satisfies
$W(t + N) = W(t) \oplus s$, $s$ the weight parity of $u \lor v$ on $\mathbb{Z}/N$. If $s = 0$ the children on
$\mathbb{Z}/L$ are the extensions of those on $\mathbb{Z}/N$; if $s = 1$, where $\mathcal{T}_N$ has a leaf, they exist
and are antiperiodic, $W(t + N) = \lnot W(t)$. So $\mathcal{T}_L$ is $\mathcal{T}_N$ with two children hung on each
leaf, followed by the subtrees that start with an antiperiodic word, and
$\operatorname{depth}(\mathcal{T}_{2N}) \ge \operatorname{depth}(\mathcal{T}_N) + 1$. The antiperiodic step is the
kit's `Rule30RightPeriods.antiperiod` and `half_black` read on the tree; the embedding is new. The conjecture for $L$ is
therefore: every subtree of $\mathcal{T}_L$ that starts at a period doubling is finite. (Checked on every node of
$\mathcal{T}_N$ for $N = 2, 4, 8, 16$, `tests/test_light_return_words.py`.)

## Computed

`python -m computations.light_return_words` gives $\mathcal{T}_L$ for $L = 2, \ldots, 64$:

| $L$ | 2 | 4 | 8 | 16 | 32 | 64 |
|---|---|---|---|---|---|---|
| nodes | 1 | 3 | 15 | 31 | 1,055 | 85,887 |
| depth | 0 | 1 | 3 | 4 | 14 | 103 |

All six are finite, so by 2 the only nonzero periodic points of period dividing 64 are rain, which agrees with
[the edge periodic points](edge-periodic-points.md) by a different count. The depths are the transients $T_k$ quoted
there.

## The branching heuristic

The heuristic is that each step has two choices, the next parity is a fair coin, and so the process is a critical
branching process. Lemma 3 shows that it is not a branching process with independent offspring: at a node with
children and $|v|$ odd, exactly one child has children, and with $|v|$ even, both children have children or neither
does. A node with children thus has one child with children, or either zero or two. Criticality would need the two
outcomes of the even case to be equally frequent. That stays a heuristic; it is consistent with the erratic depths
(4, 14, 103). A proof has to find structure the coin model lacks.

## Where it stops

After the first doubling the half-differences $W_e(t) \oplus W_e(t + N)$ start all 1s (by Lemma 4 and
[edge-periodic classification](../../negative-results/frames/edge-periodic-classification.md) item 2) and above that
column they do not form a closed system (Route 1 there). On the longest walk of $\mathcal{T}_{32}$ (depth 14) the
words look like alternating stretches with defects before the walk dies, which suggests a defect picture: rain with
moving defects whose interactions eventually force odd weight. This is an observation by inspection, not produced by
code in `computations/`. No conserved or monotone quantity of the defects is known, and tracking the non-flip sets
$\lnot(W_{e-1} \lor W_{e-2})$ is untried. The induction from $L/2$ to $L$ (Lemma 4)
reduces each period to the finiteness of the subtrees after a doubling, and that step is open.

## Reproduce

```bash
python -m computations.light_return_words --k-max 6     # trees and Lemma 3 counts to L = 64: a few seconds
python -m pytest tests/test_light_return_words.py
```
