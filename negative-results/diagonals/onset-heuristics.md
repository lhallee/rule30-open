---
title: Three heuristics for the onsets of the single cell's left diagonals fail on the data; the transient has the density of fair coins, so a budget on reset gaps gives the walk's slope 2, a flipped cell's damage ends by the later onset or becomes a permanent time shift, and a doubling law passes its base test while the onsets spread like a walk
category: diagonals
problems: [2]
status: negative
kind: refuted
evidence: [computations/onset_heuristics.py]
---

# Three heuristics for the onsets of the single cell's left diagonals fail on the data; the transient has the density of fair coins, so a budget on reset gaps gives the walk's slope 2, a flipped cell's damage ends by the later onset or becomes a permanent time shift, and a doubling law passes its base test while the onsets spread like a walk

**Question.** [SettledSlope](../../Rule30Open/Diagonals/SettledSlope.md) turns a bound $T_j \le \gamma j + o(j)$ on the
onsets of the left diagonals $D_j(t) = \mathrm{cell}(t, j - t)$, with a bound on antiphase alternations, into a
black-run slope below $3/5$, and the front walk of [FrontWalker](../../Rule30Open/Diagonals/FrontWalker.md) gives
$\gamma$ about 2.01 from the settled parts alone ([linear settling leads](linear-settling-leads.md)). The onsets
themselves grow like $1.33j$ to depth 200,000. Three heuristics claim a mechanism for a constant below 2; each was
tested on the single cell and on seed rows (white left of a black cell, cells $x_1, x_2, \dots$ right of it), where the
onset is the first time from which $D_j$ repeats with period 64.

## Heuristic 1: a density budget for the reset gaps

**The identity.** If $D_{j+1}(r) = 1$ and $D_{j+1}$ is white on $(r, t]$, then
$D_{j+2}(t + 1) = 1 \oplus D_j(r) \oplus \dots \oplus D_j(t)$: the OR in
$D_{j+2}(s + 1) = D_j(s) \oplus (D_{j+1}(s) \lor D_{j+2}(s))$ is 1 at $s = r$, which gives $\lnot D_j(r)$, and at a
white $D_{j+1}(s)$ the step adds $D_j(s)$. So $D_{j+2}$ forgets its past at every black cell of $D_{j+1}$, and the
heuristic charges each depth the mean wait $1/\rho_j$ for a black cell, with $\rho_j$ the density of black cells in the
transient: $T_j \approx j / \rho_j$, so a constant $1.33$ would need $\rho_j$ near $0.75$.

**The numbers.** For the single cell and $50 \le j \le 200$ (`density`, 3,000 steps), $T_j / j$ has mean 1.3325 and
ranges over $[1.218, 1.471]$, and:

| Interval of $D_j$ | Mean $\rho_j$ | Least | Largest | $\rho_j \le 0.52$ | $1/\rho_j$ within 15% of $T_j / j$ |
|---|---:|---:|---:|---:|---:|
| $[0, T_j)$ | 0.311 | 0.222 | 0.411 | 100% | 0% |
| $[\lceil j/2 \rceil, T_j)$, the light cone | 0.500 | 0.344 | 0.643 | 66% | 2.0% |
| $[j, T_j)$, left of the center | 0.495 | 0.220 | 0.705 | 59% | 4.6% |

**Where it stops.** Inside the light cone the transient has mean density 0.500, that of fair coins, and $1/\rho = 2$ is
the slope of the front walk, which is this budget applied to the settled parts. The identity is the reset of the front
law (`D_periodic_of_black`), and the onsets beat the walk through the defect bits of lead 1 of
[linear settling leads](linear-settling-leads.md), which a density of gaps does not see.

## Heuristic 2: the damage from one flipped cell decays

**The idea.** Rule 30 is permutive in the diagonal direction, so a change of $D_j(t)$ always changes $D_{j+2}(t + 1)$,
and a difference is removed only by cancellation or by the OR. If the damage from one flipped initial cell clears from
diagonal $j$ at a rate $\lambda$ per depth, then $T_j \approx j / \lambda$.

**Two facts on paper.** Flipping $x_k$ changes only the diagonals $j \ge k$, since $D_j$ depends on $x_1, \dots, x_j$.
If two seeds have $D_j$ repeating with period $P$ from onsets $T$ and $T'$ and differ at some time $t \ge \max(T, T')$,
they differ at $t + P, t + 2P, \dots$: so the damage on $D_j$ either ends by the later onset or never ends. By
[DrivenSkeleton](../../Rule30Open/Diagonals/DrivenSkeleton.md) both are the single cell's $D_j$ read with a time shift
(below depth 53,207), so the damage never ends exactly when the two shifts differ modulo the period.

**The numbers** (`damage`; seeds of fair cells $x_1, \dots, x_J$, each run with and without $x_k$ flipped over
$4J + 400$ steps rounded down to a multiple of 64; every diagonal of every seed is the single cell's shifted in time on
the last 64 rows, and the damage is permanent exactly where the shifts differ). The fraction of pairs whose $D_j$
differs forever, among pairs with $k \le j$ (17, 58 and 208 pairs at $j = 3$, 8 and 29 in the first row, 75 at $j = 3$
in the second, all pairs elsewhere):

| $J$, pairs, flip $k$ uniform in | $j = 3$ | 8 | 29 | 40 | 100 | 399 | 400 | 450 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 40, 300, $1 .. 40$ | 0.529 | 0.310 | 0.163 | 0.113 | | | | |
| 450, 200, $1 .. 8$ | 0.413 | 0.410 | 0.660 | 0.660 | 0.660 | 0 | 0.855 | 0.855 |

The period is 2 from depth 3, 4 from 8, 8 from 29 and 16 from 400, and 399 is a white diagonal. Where the damage ends,
it ends by the later onset in every case: 5,081 diagonals at or past the flip at $J = 40$ (at the later onset itself for
25.3% of them) and 31,671 at $J = 450$ (73.8%). Fitted against $j - k$ the clearing time is $1.243(j - k) + 1.84$ at
$J = 40$ and $1.271(j - k) + 1.24$ at $J = 450$, below the light-cone slope 2, so the test's own threshold does not
fire.

**Where it stops.** The damage does not decay; it becomes a time shift. A single flip in the first eight cells leaves
85.5% of the sampled seeds out of phase with their flipped copy at depths 400 and 450, and over the same pairs the
fraction rises from 0.41 at periods 2 and 4 to 0.66 at period 8 and 0.855 at period 16. Where the damage does end, the
time is at most the later of two onsets, so a bound on the onsets of seed rows (the
[seed-uniform](../../findings/diagonals/seed-uniform-onsets.md) question) bounds the clearing time, and the slope 1.24
to 1.27 measures a quantity below those onsets, not a new one; a bound on the clearing time alone does not bound the
onsets.

## Heuristic 3: a doubling law $T_{2j} \le 2T_j + K$

**The idea.** With $S_j = T_j + K$ the law reads $S_{2j} \le 2S_j$, so a base index $j_0$ with $(T_{j_0} + K)/j_0 < 2$
gives $T_j < 2j$ on $j = 2^k j_0$. A renormalization from diagonal $2j$ to $j$ would prove it.

**The numbers** (`doubling`, the onsets of the single cell to depth 200,000 from 300,600 steps, as in
[linear settling leads](linear-settling-leads.md)). The base test passes: $K = \max_{j \le 256}(T_{2j} - 2T_j) = 25$ (at
$j = 35$), and the least $(T_{j_0} + 25)/j_0$ over $16 \le j_0 \le 256$ is 1.3306 (at 245). Over longer ranges the
constant grows:

| $j \le$ | 256 | 1,000 | 4,000 | 10,000 | 50,000 | 100,000 |
|---|---:|---:|---:|---:|---:|---:|
| $\max (T_{2j} - 2T_j)$ | 25 | 93 | 180 | 254 | 311 | 311 |
| $\min (T_{2j} - 2T_j)$ | $-43$ | $-43$ | $-43$ | $-56$ | $-555$ | $-1{,}481$ |

With $K = 311$ the least $(T_{j_0} + K)/j_0$ is 2.459 on $16 \le j_0 \le 256$ and 1.335 on $16 \le j_0 \le 100{,}000$
(at 95,930). The largest value does not grow past $j = 10{,}430$ in this range. The least value is already $-418$ (at
$j = 25{,}256$) while $j$ and $2j$ lie in the regime of depths 400 to 53,206, and it reaches $-1{,}481$ (at
$j = 70{,}948$) after the mean increment of the onsets falls from 1.3373 there to 1.3332 on depths 53,207 to 87,866 and
1.3257 on 87,867 to 199,999 (period 32). Within each regime the increments $T_{j+m} - T_j$ have mean $1.337m$ and
$1.325m$ and

| $m$ | 1 | 4 | 16 | 64 | 256 | 1,024 | 4,096 |
|---|---:|---:|---:|---:|---:|---:|---:|
| variance / $m$, depths 400 to 53,206 | 9.67 | 2.51 | 2.41 | 2.19 | 2.11 | 2.03 | 1.27 |
| variance / $m$, depths 87,867 to 199,999 | 9.35 | 2.45 | 2.28 | 2.16 | 2.16 | 2.44 | 2.53 |

The variance grows in proportion to $m$ from $m = 4$ to 1,024 in the first regime and to 4,096 in the second (the
windows overlap, so the last columns rest on few independent windows, and 1.27 is the one outlier): in this range the
onsets spread like a walk with drift about 1.33 and variance about 2.2 per depth. Read as a heuristic, not proved, this
says that $T_j - 1.33j$ is not bounded by a constant. The frontier $F(t)$, the largest $J$ with $T_j \le t$ for every
$j \le J$, gains at most 14 diagonals at one time and waits at most 16 steps between gains, with mean drift
$200{,}000 / \max_{j} T_j = 0.752$ per step.

**Where it stops.** The test cannot fail: the onsets are close to linear, so any finite range gives a $K$ and a base
index with ratio near 1.33. The heuristic reading of the spread is that $T_{2j} - 2T_j$ varies by order $\sqrt{j}$, so a
doubling law would need $K$ of order $\sqrt{j}$ (which, iterated, still gives a linear bound). The step itself has no
mechanism: the front shows nothing at the depths where the period doubles (lead 2 of
[linear settling leads](linear-settling-leads.md)), and nothing here maps diagonal $2j$ to diagonal $j$. A drift
argument on $F$ (a supermartingale with a potential on the state near the front) needs a potential on the settled pairs
or the transient, and no settled pair repeats up to a time shift (lead 3 there).

## What it means

Each heuristic names a quantity that is the onset again: the density of the transient is a half and gives the walk; the
damage of a flip ends by the later of two onsets or is a permanent phase; and the doubling constant is the spread of the
onsets. The one structural fact the tests add is that a single flip in the first cells of a seed changes the phase of
the settled left side modulo the period for most sampled seeds, more often at longer periods, so two seeds that differ
in one cell need not agree on a deep diagonal.

## Reproduce

```bash
python -m computations.onset_heuristics density                                   # heuristic 1, about 1 s
python -m computations.onset_heuristics damage --depth 40 --pairs 300 --flip 40   # heuristic 2, about 2 s
python -m computations.onset_heuristics damage --depth 450 --pairs 200 --flip 8   # heuristic 2, about 40 s
python -m computations.onset_heuristics doubling --depth 200000                   # heuristic 3, about 2.5 min, 0.2 GB
```
