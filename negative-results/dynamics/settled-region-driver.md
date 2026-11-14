---
title: The settled left region keeps of the center column one time shift, read in the first steps; a link between the onset of an eventual period and its length cannot come from it, nor from a flux across the center or the entropy of column 1's latch
category: dynamics
problems: [1]
status: negative
kind: barrier
evidence: [computations/settled_phase.py]
---

# The settled left region keeps of the center column one time shift, read in the first steps; a link between the onset of an eventual period and its length cannot come from it, nor from a flux across the center or the entropy of column 1's latch

**Question.** Suppose the center column $c$ of a row with a leftmost black cell has period $P$ from time $T$. Far left,
every left diagonal is eventually periodic with a power-of-two period and, by
[DrivenSkeleton](../../Rule30Open/Diagonals/DrivenSkeleton.md), settles to the single cell's own diagonals up to a time
shift. Near the center the pattern is driven with period $P$. Does the meeting of the two give an inequality between
$T$ and $P$ ($T \le f(P)$, or $P \ge f(T)$), or a condition on $P$ (odd, a power of two, a gcd)? Two neighboring
questions: does the difference of rows $T$ and $T + P$ obey a flux bound across the center, and does an entropy of
the sequences column 1 may take next to a periodic column separate blocks?

**Outcome.** No, for a structural reason. The cells left of the center accept every driver, and their settled part
remembers the driver only through one time shift relative to the single cell's skeleton; in every quadrant computed,
that shift is already fixed by the driver's first 20 values. The eventual period and its onset are invisible there,
and every constraint on them lives in the unsettled wedge next to the center, where the check of
[LeftLatch](../../Rule30Open/Columns/LeftLatch.md) reads each diagonal one step after it leaves column 0. The flux
across the center is exactly LeftLatch's check and shown conditions written for a difference, and the entropy of
column 1's latch is positive for every block but the white one. Each lemma below is proved; the single shift is
computed, with a proof sketch that leans on DrivenSkeleton's hypothesis.

## The driven quadrant

Write $x_i(t)$ for cell $i$ at time $t$, $x_i(t+1) = x_{i-1}(t) \oplus (x_i(t) \lor x_{i+1}(t))$. Take a finite left
part $L$, cells $-w, \ldots, 0$ at time 0 with cell $-w$ black, and any sequence $c$ with $c(0) = $ cell 0 of $L$. The
*quadrant* $Q(L, c)$ is a pattern on the cells $i \le 0$, $t \ge 0$, white left of $-w - t$, with column 0 equal to
$c$, that obeys the rule at every cell $i \le -1$. In the left-edge frame $d = i + t + w$ write $D_d(t) = x_{d-t-w}(t)$.

**Lemma 1 (every driver is accepted; causality).** $Q(L, c)$ exists and is unique for every $L$ and every sequence
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

| driver | same eventual period as $S$ on every diagonal | largest onset age | shift on depths 70 to 100 |
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
data, and the shift is the one $k$ with $D_d(t) = S_d(t + k)$ for all 31 diagonals $70, \ldots, 100$ at once (their
period is 8, so $k$ is read mod 8). In this frame the single cell's diagonals first reach periods 2, 4, 8 and 16 at
depths 3, 8, 29 and 400 (diagonals below 600, times below 40,000).

So, on these ranges: the eventual periods do not depend on the driver, one time shift aligns the whole settled band
with the skeleton, and onset ages under periodic drivers of periods 2 to 8 fall in the same range as under the true
center column (9 to 54 against 47). Drivers that agree on their first 20 values and differ at random afterwards gave
the same shift in every trial (48 drivers, 6 prefixes, `skeleton_shift` on depths 70 to 100).

*Why (a sketch, not a full proof).* DrivenSkeleton's step lemmas use only the diagonal recursion (the kit's
`Ld_diagStep`, which needs no white side), so they apply to quadrants as written: if the eventual pairs
$(D_j, D_{j+1})$ of two quadrants agree up to a shift $k$ modulo their period $p$, and $D_{j+1}$ has a 1 in its cycle,
then the map of $D_{j+2}$ over one period is constant and $D_{j+2}$ agrees up to the same shift; only a white
$D_{j+1}$ lets the shift move by $p$ (or complements $D_{j+2}$), and DrivenSkeleton's hypothesis is that such a
diagonal is followed by a doubling of the period. Under that hypothesis the shift modulo $2^k$ is fixed at the depth
$d_k$ where the pair period first reaches $2^k$, and by Lemma 1 that depth reads only $c(0), \ldots, c(d_k - w)$.

## Why this stops the route

An inequality between $T$ and $P$, or a condition on $P$, would have to be visible where the driver acts. By Lemma 1
the cells on diagonals $d \le w$ of $L_T$ (the whole left part at time $T$) do not see the driver after time $T$ at
all, and by the computation the settled cells on deeper diagonals see it only through one shift that the first few
driver values already fix: a driver of period 2 and the true center column give the same skeleton with a different
shift. What is left is the transient of each diagonal, the wedge between the onset line and column 0, and that is
where the check acts. Constraints on $T$ and $P$ therefore have to come from the transients, which is the chaotic part
that the [finite games](../../findings/columns/coverage.md) and LeftLatch's searches already explore block by block.
In particular none of the conditions asked about (odd $P$, $P$ a power of two, a gcd with the skeleton's period) has a
foothold: the skeleton's periods are the same for every driver, so they meet $P$ nowhere.

## The flux across the center

**Lemma 2.** For two rows whose center columns agree at times $s$ and $s + 1$, write $\delta_j(s)$ for the XOR of
their cells $j$ at time $s$. Then $\delta_{-1}(s) = \lnot c(s) \land \delta_1(s)$.

*Proof.* $c(s+1) = x_{-1}(s) \oplus (c(s) \lor x_1(s))$ in both rows. If $c(s) = 1$ both give
$x_{-1}(s) = \lnot c(s+1)$, so $\delta_{-1}(s) = 0$; if $c(s) = 0$, $x_{-1}(s) \oplus x_1(s) = c(s+1)$ in both, so
$\delta_{-1}(s) = \delta_1(s)$. $\square$ (Checked on 60 pairs of random rows by `interface_identity_holds`.)

So a difference reaching column $-1$ is absorbed at the black steps of $c$ and passes to column 1 at the white
steps. For rows $T$ and $T + P$ of an eventually periodic orbit this is LeftLatch's check and shown condition, read
for a difference: nothing new. By Lemma 1 the two left halves are quadrants with the same driver and left parts that
differ, so the whole left difference comes from the left parts, and a flux bound would have to say that a difference
launched at the left edge cannot always arrive at column $-1$ on white steps only. That is the kit's open
`EdgeObservable` (finite rows with equal center columns have equal left edges) for a time-shifted pair, and no
quantity conserved over a few steps exists to count it with ([conservation laws](../structure/conservation-laws.md)).

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

So the entropy separates only the white block, which the OR latch and Jen's theorem already exclude
([compositional halves](compositional-halves.md)). The latch shift ignores the shown condition, which ties $a$ at the
white steps to the left half; once that is added the object is LeftLatch's statement, which has no finite transfer
matrix.

## What it means

The three directions meet the same wall from different sides: the half left of the center is free (Lemma 1), its
settled part is the universal skeleton with one shift, and all the information about an eventual period sits in the
young diagonals next to the center, read at age one by the check. A theorem linking $T$ and $P$ would need control of
those transients, the same chaotic region that every Problem 1 route reaches.

## Reproduce

```bash
python -m computations.settled_phase      # the table and the latch entropies (seconds)
python -m pytest tests/test_settled_phase.py
```
