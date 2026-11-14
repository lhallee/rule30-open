---
title: Down to depth 53,207 the settled left region keeps of the center column one time shift, read in a finite prefix; a link between the onset of an eventual period and its length cannot come from that part, nor from a flux across the center or the entropy of column 1's latch
category: dynamics
problems: [1]
status: negative
kind: barrier
evidence: [computations/settled_phase.py]
---

# Down to depth 53,207 the settled left region keeps of the center column one time shift, read in a finite prefix; a link between the onset of an eventual period and its length cannot come from that part, nor from a flux across the center or the entropy of column 1's latch

**Question.** Suppose the center column $c$ of a row with a leftmost black cell has period $P$ from time $T$. Far left,
every left diagonal is eventually periodic with a power-of-two period and, by
[DrivenSkeleton](../../Rule30Open/Diagonals/DrivenSkeleton.md), settles to the single cell's own diagonals up to a time
shift. Near the center the pattern is driven with period $P$. Does the meeting of the two give an inequality between
$T$ and $P$ ($T \le f(P)$, or $P \ge f(T)$), or a condition on $P$ (odd, a power of two, a gcd)? Two neighboring
questions: does the difference of rows $T$ and $T + P$ obey a flux bound across the center, and does an entropy of
the sequences column 1 may take next to a periodic column separate blocks?

**Outcome.** Not from the settled region down to depth 53,207, for a structural reason; this is a barrier for that
region, not a theorem about $T$ and $P$. The cells left of the center accept every driver (the kit's driven left half),
and by DrivenSkeleton's driven-half paragraph their settled pairs down to depth 53,207 are the single cell's up to one
time shift, which a finite prefix of the driver fixes (on depths 70 to 99, the first 30 values in the computation
below, but not the first 20 or 25). The eventual period and its onset are invisible there, and every constraint on them
lives in the unsettled wedge next to the center, where the check of
[LeftLatch](../../Rule30Open/Columns/LeftLatch.md) reads each diagonal one step after it leaves column 0. Past depth
53,207 the settled part also keeps one bit at each white diagonal not followed by a doubling
([SkeletonTree](../../Rule30Open/Diagonals/SkeletonTree.md)); this entry does not examine whether those bits can carry
information about $T$ or $P$. The flux across the center is LeftLatch's check and shown condition written for a
difference (the masked form of [compositional halves](compositional-halves.md)), and the entropy of column 1's latch
is positive for every block but the white one. Lemmas 1 to 3 are proved on paper, not in Lean; the shift statement is
DrivenSkeleton's, and the tables are computed checks of it on the stated ranges.

## The driven quadrant

Write $x_i(t)$ for cell $i$ at time $t$, $x_i(t+1) = x_{i-1}(t) \oplus (x_i(t) \lor x_{i+1}(t))$. Take a finite left
part $L$, cells $-w, \ldots, 0$ at time 0 with cell $-w$ black, and any sequence $c$ with $c(0) = $ cell 0 of $L$. The
*quadrant* $Q(L, c)$ is a pattern on the cells $i \le 0$, $t \ge 0$, white left of $-w - t$, with column 0 equal to
$c$, that obeys the rule at every cell $i \le -1$. In the left-edge frame $d = i + t + w$ write $D_d(t) = x_{d-t-w}(t)$.

Existence and uniqueness of the driven half are the kit's `Rule30DrivenLeft.L` (a definition by recursion for every
driver) with `cell_eq_L` (the real pattern is the driven half from every time $T$), and its causality in time is
`CoupledHalves.L_causal`; that the half left of the center can be replaced by a causal adversary is "Either half can be
replaced" in [compositional halves](compositional-halves.md). Lemma 1 restates these in the left-edge frame; its
remark that diagonal $d$ reads only $c(0), \ldots, c(d - w)$ is the form used below.

**Lemma 1 (every driver is accepted; causality along diagonals).** $Q(L, c)$ exists and is unique for every $L$ and every sequence
$c$. Diagonal $d$ starts at time $s_d = \max(0, d - w)$ with the cell $d - w$ of $L$ ($d \le w$) or with $c(d - w)$
($d > w$), and then $D_d(t+1) = D_{d-2}(t) \oplus (D_{d-1}(t) \lor D_d(t))$. So diagonal $d$ reads the driver only at
times $0, \ldots, d - w$.

*Proof.* The rule at cell $i = d - t - 1 - w \le -1$ and time $t+1$ reads cells $i - 1, i, i + 1$ at time $t$, which
lie on diagonals $d - 2, d - 1, d$; cell $i + 1 \le 0$, so $D_d(t)$ at cell $i + 1$ is either in the quadrant
($i + 1 \le -1$) or the driver ($i + 1 = 0$, $t = d - w$). Diagonals $d < 0$ are white. Induction on $d$, then on
$t \ge s_d$, defines every cell once, and any quadrant must agree with these values. Diagonal $d$ depends on its own
start and on diagonals $d - 1, d - 2$, so by induction only on $L$ and $c(0), \ldots, c(\max(0, d - w))$. $\square$

In the orbit of a row with a leftmost black cell, the half left of the center from time $T$ is $Q(L_T, c(T + \cdot))$,
where $L_T$ is that half at time $T$. So the half left of the center never constrains the center by itself: every
obstruction is in the update of column 0, whose two cases are LeftLatch's check (at a 1 of $c$, $x_{-1}(t) = \lnot
c(t+1)$) and its shown condition (at a 0, $x_1(t) = c(t+1) \oplus x_{-1}(t)$). The cell $x_{-1}(t) = D_{t+w-1}(t)$ is
diagonal $t + w - 1$ one step after it started, so the check reads every diagonal at age one.

## What the settled part keeps of the driver

For the single cell's left part ($w = 0$) the quadrant driven by the true center column is the single cell's own
left half, the *skeleton* $S$. Driven by other sequences, the quadrant's diagonals were compared with $S$
(`python -m computations.settled_phase`, diagonals 0 to 119, times below 8,000):

| driver | same eventual period as $S$ on every diagonal | largest onset age | shift on depths 70 to 99 |
|---|---|---|---|
| the center column ($S$ itself) | yes | 47 | 0 |
| a random sequence | yes | 20 | 3 |
| $10$ repeated | yes | 30 | 1 |
| $100$ | yes | 23 | 0 |
| $110$ | yes | 41 | 6 |
| $1101$ | yes | 27 | 4 |
| $10110$ | yes | 43 | 4 |
| $1011100$ | yes | 9 | 6 |
| $10000000$ | yes | 54 | 1 |

Here the onset age of diagonal $d$ is the time from its start $d$ to the first time from which it is periodic in the
data, and the shift is the least $k$ with $D_d(t) = S_d(t + k)$ for all 30 diagonals $70, \ldots, 99$ at once (their periods
divide 8, so $k$ is read mod 8). In this frame the single cell's diagonals first reach least periods 2, 4, 8 and 16 at
depths 3, 8, 29 and 400 (diagonals below 600, times below 40,000). At $w = 0$ the frame is the repository's
$D_j(t) = \mathrm{cell}(t, j - t)$, and these are the depths of DrivenSkeleton, [LeftMemory](../../Rule30Open/Diagonals/LeftMemory.md)
and [left records](../../findings/diagonals/left-records.md) (Wolfram's 3, 8, 29, 400; white diagonals 2, 7, 28,
399). The "period 16 from depth 8" of [settled runs](../../findings/diagonals/settled-runs.md) counts 16 as a period,
not the least one (1, 2, 4 and 8 divide it), so the two agree. Least periods are not monotone in the depth (period 4
recurs at deeper diagonals), which is why the band 70 to 99 is described by periods dividing 8.

So, on these ranges: the eventual periods do not depend on the driver, one time shift aligns the whole settled band
with the skeleton, and the largest onset age per driver is 9 to 54 under periodic drivers of periods 2 to 8, against
47 under the true center column. Which prefix fixes the shift: for each prefix length $m$, 60 random prefixes, each
continued by 4 random tails (times below 1,000). The groups whose shifts on depths 70 to 99 differ number 12 for
$m = 20$, 2 for $m = 25$, 3 for $m = 29$, and 0 for $m = 30$ and $m = 40$. So a shared prefix of 20 or 25 values does
not fix the shift (the test has a pair sharing $c(0), \ldots, c(23)$ with shifts 6 and 2), and $c(0), \ldots, c(29)$
fixed it in every trial, as the sketch below predicts: the shift mod 8 is set at depth 29, which reads $c(0),
\ldots, c(29)$. The case the question asks about directly: the true center column up to time $T$ and a block repeated from $T$ on, for $T = 25, 30, 50, 100$ and
the six blocks $10, 100, 110, 1101, 10110, 1011100$, gives on every diagonal below 120 the skeleton's eventual period
and, on depths 70 to 99, shift 0. These diagonals do read the periodic tail (diagonal $d$ reads $c(0), \ldots, c(d)$),
and in each of the 24 cases some diagonal from $T$ on differs from the skeleton's (its transient changed), but their
settled cycles on depths 70 to 99 are exactly those of the true center column: on diagonals below 120, a hypothetical
eventual period of any of these lengths from any of these onsets leaves the settled band 70 to 99 as it is.

*Why.* This is DrivenSkeleton's statement for driven halves: its step lemmas are proved in Lean under
`DiagStepFrom` (with DrivenSkeleton's `Ld_diagStep`, which needs no white side), it gives the base for a driven half
(diagonals 0 and 1 black from times 0 and 2; for $w > 0$ the base is again two black diagonals, since cell $-w$ is
black) and the induction on paper, and its `driver_pairs` finds one class per depth up to 90 over every driver. The
tables here are an independent check on depths 70 to 99. In outline: if the eventual pairs
$(D_j, D_{j+1})$ of two quadrants agree up to a shift $k$ modulo their period $p$, and $D_{j+1}$ has a 1 in its cycle,
then the map of $D_{j+2}$ over one period is constant and $D_{j+2}$ agrees up to the same shift; only a white
$D_{j+1}$ lets the shift move by $p$ (or complements $D_{j+2}$), and DrivenSkeleton's hypothesis is that such a
diagonal is followed by a doubling of the period. That holds for the white diagonals 2, 7, 28 and 399 and fails at
53,207 (DrivenSkeleton, from its computed list of white diagonals), so the induction carries one shift down to depth
53,207. The shift modulo $2^k$ is fixed at the depth $d_k$ where the pair period first reaches $2^k$, and by Lemma 1
that depth reads only $c(0), \ldots, c(d_k - w)$: on depths 29 to 399, the shift mod 8 is a function of $c(0),
\ldots, c(29)$ (for $w = 0$), and down to 53,207 the shift mod 16 is a function of $c(0), \ldots, c(400)$.

## Why this stops the route

An inequality between $T$ and $P$, or a condition on $P$, would have to be visible where the driver acts. By Lemma 1
the cells on diagonals $d \le w$ of $L_T$ (the whole left part at time $T$) do not see the driver after time $T$ at
all, and by DrivenSkeleton the settled cells on deeper diagonals, down to depth 53,207, see it only through one shift
that a finite prefix of the driver fixes (the first 401 values for $w = 0$; on depths below 400, the first 30): a
driver of period 2 and the true center column give the same skeleton with a different shift. Deeper, the driver also
picks a branch of [SkeletonTree](../../Rule30Open/Diagonals/SkeletonTree.md) at each white diagonal not followed by a
doubling (53,207 and later), and from depth 87,867 the period of a diagonal depends on the branch
([skeleton tree](../../findings/diagonals/skeleton-tree.md)); each such bit is again a function of a finite prefix of
the driver, but a late onset $T$ reaches those depths, and this entry leaves them open. What is left is the transient of each diagonal, the wedge between the onset line and column 0, and that is
where the check acts. Constraints on $T$ and $P$ therefore have to come from the transients, which is the chaotic part
that the [finite games](../../findings/columns/coverage.md) and LeftLatch's searches already explore block by block.
In particular none of the conditions asked about (odd $P$, $P$ a power of two, a gcd with the skeleton's period) has a
foothold down to depth 53,207: there the skeleton's periods are the same for every driver, so they meet $P$ nowhere.

## The flux across the center

**Lemma 2.** For two rows whose center columns agree at times $s$ and $s + 1$, write $\delta_j(s)$ for the XOR of
their cells $j$ at time $s$. Then $\delta_{-1}(s) = \lnot c(s) \land \delta_1(s)$.

*Proof.* $c(s+1) = x_{-1}(s) \oplus (c(s) \lor x_1(s))$ in both rows. If $c(s) = 1$ both give
$x_{-1}(s) = \lnot c(s+1)$, so $\delta_{-1}(s) = 0$; if $c(s) = 0$, $x_{-1}(s) \oplus x_1(s) = c(s+1)$ in both, so
$\delta_{-1}(s) = \delta_1(s)$. $\square$ (Checked on 60 pairs of random rows by `interface_identity_holds`.) This is
the masked form of [compositional halves](compositional-halves.md) (item 2 of what an eventual period asks of the two halves, for the period $t' - t$),
written for a difference cell by cell.

So a difference reaching column $-1$ is absorbed at the black steps of $c$ and passes to column 1 at the white
steps. For rows $T$ and $T + P$ of an eventually periodic orbit this is LeftLatch's check and shown condition, read
for a difference: nothing new. By Lemma 1 the two left halves are quadrants with the same driver and left parts that
differ, so the whole left difference comes from the left parts. Heuristically, a flux bound would then have to say
that a difference launched at the left edge cannot always arrive at column $-1$ on white steps only. That is the
instance of the kit's open `EdgeObservable` (finite rows with equal center columns have equal left edges) for the pair
of rows $T$ and $T + P$ that `no_eventuallyPeriodic_of_edgeObservable` uses, and no quantity conserved over a few steps
exists to count it with ([conservation laws](../structure/conservation-laws.md)).

## The entropy of column 1's latch

Next to a column reading the repeated block $b$ of length $P$, column 1 obeys $a(t) = 1 \Rightarrow a(t+1) = \lnot
b(t)$ ([the coupled halves](compositional-halves.md)). The sequences that obey this alone form a shift $X_b$ with
transfer matrices $M_1 = \begin{pmatrix}1&1\\1&0\end{pmatrix}$ and $M_0 = \begin{pmatrix}1&1\\0&1\end{pmatrix}$ on the
states $a(t) \in \{0, 1\}$.

**Lemma 3.** The entropy of $X_b$ is $h(b) = \frac{1}{P} \log \rho(M_{b_0} \cdots M_{b_{P-1}})$. It is 0 for the white
block and at least $\log 2 / P$ (at least $\log 2 / 2$ when $P = 1$) for every block with a 1.

*Proof.* The formula is the usual count of paths. For the white block a 1 is followed by 1s forever, so the words of
length $n$ are $0^m 1^{n-m}$, $n + 1$ of them. If $b(j) = 1$, every sequence that is 0 off the times $j + 2kP$ (or
$j + kP$ when $P \ge 2$) obeys the latch, since a 1 at such a time must be followed by $\lnot b(j) = 0$, which the next
time is. $\square$ (Checked against enumeration of all words of length 16.)

[Left half for every block](../../findings/columns/left-half-every-block.md) computes a different entropy: that of the
readings of column $-1$ allowed by the checks and the latch together, at least $1/P$ bits per step for the blocks
$01^{P-1}$. $X_b$ is column 1 alone under the latch alone, which is why it has a $2 \times 2$ transfer matrix.

So the entropy separates only the white block, which the OR latch and Jen's theorem already exclude
([compositional halves](compositional-halves.md)). The latch shift ignores the shown condition, which ties $a$ at the
white steps to the left half; once that is added the object is LeftLatch's statement, which has no finite transfer
matrix.

## What it means

The three directions meet the same wall from different sides: the half left of the center is free (Lemma 1), its
settled part down to depth 53,207 is the universal skeleton with one shift, and all the information about an eventual period sits in the
young diagonals next to the center, read at age one by the check. A theorem linking $T$ and $P$ would need control of
those transients, the same chaotic region that every Problem 1 route reaches.

## Reproduce

```bash
python -m computations.settled_phase      # the table, the prefix and grafted shifts, the first depths of each period and the latch entropies (about 25 seconds)
python -m pytest tests/test_settled_phase.py
```
