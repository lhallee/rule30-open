---
title: Every periodic point of the right-edge map has a power-of-two period, and every one besides 0 and rain leaves rain through one state, so the conjecture that rain is all is, for each period, the finiteness of one tree; the tree for period L contains the tree for L/2 with its leaves doubled, and it is finite to period 64 with depths 0, 1, 3, 4, 14, 103
category: frames
problems: [1]
status: paper
formalization: wanted
evidence: [computations/light_return_words.py]
---

# Every periodic point of the right-edge map has a power-of-two period, and every one besides 0 and rain leaves rain through one state, so the conjecture that rain is all is, for each period, the finiteness of one tree; the tree for period L contains the tree for L/2 with its leaves doubled, and it is finite to period 64 with depths 0, 1, 3, 4, 14, 103

In the right-edge frame Rule 30 is $\Phi(y) = y \oplus (2y \lor 4y)$ on the 2-adic integers: bit $e$ of $\Phi(y)$ is
$y(e) \oplus (y(e-1) \lor y(e-2))$. A nonzero point with $\Phi^L(y) = y$ is, after dividing by a power of two, an odd
$y$, and its *words* $W_e(t) = $ bit $e$ of $\Phi^t(y)$, $t \in \mathbb{Z}/L$, satisfy $W_{-2} = W_{-1} = 0$,
$W_0 = 1 \cdots 1$ and

$$W_e(t+1) \oplus W_e(t) = (W_{e-1} \lor W_{e-2})(t) \qquad (t \in \mathbb{Z}/L).$$

The right side $R_e = W_{e-1} \lor W_{e-2}$ must have even weight, and then $W_e$ is one of two complementary words.
Call $(W_{e-1}, W_e)$ the *state*. The odd $y$ with $\Phi^L(y) = y$ are the infinite walks from $(0, 1\cdots1)$, and
the odd $y$ modulo $2^n$ with $\Phi^L(y) \equiv y$ are the walks $W_0, \ldots, W_{n-1}$ (checked against applying
$\Phi$ for $L = 2, 4, 8$ and $n \le 11$). *Rain* is the two walks in which every word from $W_1$ on alternates and
consecutive words are complementary; they are the points $2^m(\pm 1/3)$ of the conjecture under study, that rain and 0
are the only periodic points.

## Proved

**1. Periods are powers of two; odd periods do not occur.** Each $W_e$ has least period a power of two, by induction on
$e$: if $W_{e-1}$ and $W_{e-2}$ have periods dividing $2^j$, then $W_e(t + 2^j) = W_e(t) \oplus s$ with $s$ the
weight parity of $R_e$ over one block of $2^j$, so $W_e$ has period dividing $2^j$ ($s = 0$) or exactly $2^{j+1}$
($s = 1$). The least period of $y$ is the least common multiple of the periods of its words, hence a power of two, and
it divides $L$. So for odd $L$, $\Phi^L(y) = y$ forces $\Phi(y) = y$, and the only fixed point is 0: at the lowest
black bit $e_0$ of $y$, bit $e_0 + 1$ of $\Phi(y)$ is $y(e_0 + 1) \oplus 1 \ne y(e_0 + 1)$. (This needs the
start $W_{-1} = W_{-2} = 0$; rows black arbitrarily far right return after 12, 15 or 17 steps,
[LightLikeEntropy](../../Rule30Open/RandomRows/LightLikeEntropy.md).)

**2. One branch state.** Let $L \ge 2$ be even and $P = 0101\cdots$ the alternating word. $R_1 = W_0 = 1\cdots1$, so
$W_1 \in \{P, \lnot P\}$; $R_2 = 1\cdots1$ again, so $W_2$ alternates. From a rain state $(A, \lnot A)$, $A$
alternating, $R = 1\cdots1$ and the two children are the rain state $(\lnot A, A)$ and $(\lnot A, \lnot A)$. So every
walk is rain until it enters a *branch state* $(B, B)$ with $B$ alternating, and both branch states are rotations of
$(P, P)$ by one time step, which commute with the recursion. Hence, by König's lemma (two children at most):

> For each even $L$, the only nonzero points of period dividing $L$ are rain if and only if the tree $\mathcal{T}_L$
> of walks from $(P, P)$ is finite. Its depth is the longest non-rain stretch: a point that agrees with rain to bit
> $m$ and then branches fails $\Phi^L(y) = y$ by bit $m + \operatorname{depth}(\mathcal{T}_L) + O(1)$.

So for each $L$ the conjecture is one finite computation, and $L = 2^k$ is the only case (by 1).

**3. The children's fertility.** Let $(u, v)$ have the children $(v, w)$ and $(v, \lnot w)$. For $L$ even,
$|v \lor w| + |v \lor \lnot w| = 2|v| + (L - |v|) \equiv |v| \pmod 2$. So if $|v|$ is odd, exactly one child has
children; if $|v|$ is even, both or neither do. (Checked on the trees for $L = 8, 16, 32$; in $\mathcal{T}_{64}$,
20,640 of the 42,943 inner nodes have $|v|$ odd.)

**4. Doubling embeds $\mathcal{T}_{L/2}$ in $\mathcal{T}_L$.** Let $N = L/2$ be even and extend words on
$\mathbb{Z}/N$ periodically to $\mathbb{Z}/L$ (this sends $P$ to $P$). For a state $(u, v)$ on $\mathbb{Z}/N$, the
right side on $\mathbb{Z}/L$ has twice the weight, always even, and the solution satisfies
$W(t + N) = W(t) \oplus s$, $s$ the weight parity of $u \lor v$ on $\mathbb{Z}/N$. If $s = 0$ the children on
$\mathbb{Z}/L$ are the extensions of those on $\mathbb{Z}/N$; if $s = 1$, where $\mathcal{T}_N$ has a leaf, they exist
and are antiperiodic, $W(t + N) = \lnot W(t)$. So $\mathcal{T}_L$ is $\mathcal{T}_N$ with two children hung on each
leaf, followed by the subtrees that start with an antiperiodic word, and
$\operatorname{depth}(\mathcal{T}_{2N}) \ge \operatorname{depth}(\mathcal{T}_N) + 1$. The conjecture for $L$ is
therefore: every subtree of $\mathcal{T}_L$ that starts at a period doubling is finite. (Checked for $N = 4, 8, 16$.)

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
branching process. Lemma 3 shows that it is not a branching process with independent offspring: at a node with $|v|$
odd the lineage cannot end at the next step, and at a node with $|v|$ even its two children live or die together. A
fertile node thus has one fertile child or an even split between zero and two. Criticality would need the two
outcomes of the even case to be equally frequent. That stays a heuristic, and it explains why the depths are erratic
(4, 14, 103). A proof has to find structure the coin model lacks.

## Where it stops

After the first doubling the half-differences $W_e(t) \oplus W_e(t + N)$ start all 1s and then look unstructured
(the longest walk of $\mathcal{T}_{32}$, depth 14). The words themselves drift toward alternating stretches with
defects before the walk dies, which suggests a defect picture: rain with moving defects whose interactions eventually
force odd weight. No conserved or monotone quantity of the defects was found in the time available, and the idea of
tracking the non-flip sets $\lnot(W_{e-1} \lor W_{e-2})$ was not tried. The induction from $L/2$ to $L$ (Lemma 4)
reduces each period to the finiteness of the subtrees after a doubling, and that step is open.

## Reproduce

```bash
python -m computations.light_return_words --k-max 6     # under a minute
python -m pytest tests/test_light_return_words.py
```
