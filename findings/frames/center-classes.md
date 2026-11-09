---
title: On every box [-A, B] of up to 21 cells two rows have the same center column exactly when the kit's stripe relation at time 0 or 1 joins them, so the box reaches the Lean bound of 2^(A+B) + 3 · 2^(A-1) center columns (A, B ≥ 1) and rows with equal center columns have equal left parts
category: frames
problems: [1]
status: computed
formalization: partial
evidence: [computations/center_classes.py, computations/center_classes_census.c, computations/stripe_classes.py]
---

# On every box [-A, B] of up to 21 cells two rows have the same center column exactly when the kit's stripe relation at time 0 or 1 joins them, so the box reaches the Lean bound of 2^(A+B) + 3 · 2^(A-1) center columns (A, B ≥ 1) and rows with equal center columns have equal left parts

A row of the box $[-A, B]$ is a finite row whose black cells lie in $-A, \dots, B$, and its center column is its cell
0 over time. The kit's stripe relation at time 0 or 1 (S01 below) relates rows with equal center columns, and
[StripeClassCount](../../Rule30Open/Frames/StripeClassCount.md) and [StripeClasses](../../Rule30Open/Frames/StripeClasses.md)
prove in Lean that on every box it has exactly
$$N(A, B) = 2^{A+B} + 3 \cdot 2^{A-1} \quad (A, B \ge 1)$$
classes, the fibers of an explicit representative, so that no box has more than $N(A, B)$ center columns. This entry
adds:

- **Completeness up to 21 cells (computed).** On each of the 231 boxes of up to 21 cells, the census finds $N(A, B)$
  rows with pairwise different center columns. By the Lean bound these are all the center columns of the box, so two
  rows have the same center column exactly when S01 joins them, with no horizon assumed. The last two classes to
  separate first differ at time 829, on $[0, 20]$.
- **The classes and their sizes (proved here).** The class of each representative, written out: the stripe words
  after a fixed prefix. For each left part (cells $\le 0$), the nonempty right halves inside $[1, B]$ form
  $2^{B-1-k}$ classes of $k$ rows for $1 \le k \le B - 1$ and one class of $B$ rows, and the empty right half is alone
  or joins the class of $B$ rows. S01 relates any two rows of a class directly.
- **Consequences.** Rows with equal center columns in a box of up to 21 cells have equal left parts, so the kit's
  open `EdgeObservable` holds for them; every box $[-A, 0]$ has $2^{A+1}$ center columns, one per row (proved); and
  Problem 1 follows if, for infinitely many $A$, the rows of $[-A, A]$ have $4^A + 3 \cdot 2^{A-1}$ center columns.

## Setting

- **Rows.** The computations and the Lean modules write a row of $[-A, B]$ as an integer $x < 2^{A+B+1}$ whose bit
  $k$ is cell $B - k$: the frame of the kit's `Rule30StripeMeeting` with center index $B$, in which one step is
  $\Phi(y) = y \oplus ((y \ll 1) \lor (y \ll 2))$ and the center cell at time $t$ is bit $B + t$ of $\Phi^t(x)$. The
  *left part* of a row is its cells $\le 0$, its *left half* the cells $< 0$, its *right half* the cells $\ge 1$, and
  its *left edge* its leftmost black cell. A left part *ends in $0\,1$* when cell $-1$ is white and cell 0 black. A
  *column class* of a box is a set of its rows with one center column.
- **Stripe words.** A stripe word on the cells $q, \dots, B$ reads, from cell $q$ rightward, $(10)^m\,1\,0^k$ or
  $(10)^m\,11\,0^k$ ($m, k \ge 0$) and fills those cells; read from cell $B$ leftward it is the kit's `StripeWord`.
  There are exactly $n$ stripe words of length $n$; $s^*_n$ is the one whose last cell is black, $(10)^m 1$ or
  $(10)^m 11$.
- **S01.** `StripeRelated x y B` holds when $x = y$, or when for some cut cell $q \ge 0$ both rows read stripe words
  on $q, \dots, B$, are white at $q - 1$ and agree on every cell $< q - 1$. S01 relates $x$ and $y$ when
  `StripeRelated x y B` holds (time 0), or when they agree at cell 0 and `StripeRelated (Φ x) (Φ y) (B + 1)` holds
  (time 1); S01 *joins* two rows when a chain of related rows of the box connects them. The kit proves that S01 rows
  have equal center columns (`stripe_related_same_trace`, at time 1 together with the shared cell 0) and that rows that
  become stripe-related at any time while their center cells agree were related at time 0 or 1
  (`stripe_meeting_is_early`). It leaves open whether equal center columns force the relation.

## What Lean proves

- **The bound** ([StripeClasses](../../Rule30Open/Frames/StripeClasses.md)). `box_columns` and `box_center_columns`
  ($A, B \ge 1$): every row of $[-A, B]$ has the center column of one of the $N(A, B)$ rows `boxRep A B i`, the rows
  with cell $B$ black and the rows with an empty right half whose left part does not end in $0\,1$.
  `right_half_columns` and `right_half_center_columns`: the $2^B$ rows with one left part have at most
  $2^{B-1} + 1$ center columns, and at most $2^{B-1}$ when the left part ends in $0\,1$. With the left parts $0$ and
  $1$ this bounds the box $[0, B]$ by $N(0, B) = 2^B + 1$; the box $[-A, 0]$ has $N(A, 0) = 2^{A+1}$ rows.
- **The classes** ([StripeClassCount](../../Rule30Open/Frames/StripeClassCount.md)). `rep_of_S01` and `joined_iff`:
  the S01 classes of a box are the fibers of `rep`, which moves a row by one S01 step to a row with cell $B$ black, or
  leaves it; `s01_class_count`: there are exactly $N(A, B)$ of them; `tail_of_Phi_stripe`: the rows whose image under
  one step reads a stripe word.

So the bound on center columns is exactly the number of S01 classes: completeness of S01 on a box is the statement
that the box has $N(A, B)$ center columns.

## The classes, written out, and their sizes

This section is proved on paper; the Lean modules do not state it.

**Representatives.** Each class holds one row that is its own representative (`rep_cases`, `boxRep_fixed`): a row
with cell $B$ black, or a row with an empty right half whose left part does not end in $0\,1$. A representative of the
second kind is alone in its class, since `rep` takes every other row to a row with cell $B$ black. By its definition
`rep` changes only the cells $1, \dots, B$, so no class mixes left parts.

**The class of a row with cell $B$ black.** Let $r$ have cell $B$ black, let $N$ be the largest $n \le B + 1$ such
that $r$ reads $s^*_n$ on the cells $B - n + 1, \dots, B$, and let $q = B - N + 1$. The class of $r$ is the set of
rows that agree with $r$ left of cell $q$ and read a stripe word on $q, \dots, B$, except the word $1\,0 \cdots 0$
when cell $q - 1$ is black. It has $N$ rows, or $N - 1$ in that case.

*Proof.* Let $p < B$ be the last black cell of a row. If cell $p - 1$ is white and $p \ge 0$, `rep` writes
$s^*_{B-p+1}$ on the cells $p, \dots, B$ (time 0); if cell $p - 1$ is black and $p \ge 1$, it writes
$1\,0\,s^*_{B-p} = s^*_{B-p+2}$ on the cells $p - 1, \dots, B$ (time 1); otherwise it leaves the row. Read backward,
the rows other than $r$ with representative $r$ are, for each $n \le B + 1$ such that $r$ ends in $s^*_n$, the row
$r$ with that suffix replaced by $1\,0^{n-1}$, when $n \ge 2$ and the cell before the suffix is white, and by
$1\,1\,0^{n-2}$, when $n \ge 3$. These $n$ are 1 and the $n \le N$ of the parity of $N$, and for them
$s^*_N = (10)^{(N-n)/2}\,s^*_n$, so the cell before the suffix is white when $n < N$. The rows obtained are
$w\,(10)^i\,1\,0^a$ and $w\,(10)^i\,11\,0^a$ with $w$ the cells of $r$ left of $q$: every stripe word on
$q, \dots, B$ but $s^*_N$, which is $r$, and but $1\,0 \cdots 0$ when cell $q - 1$ is black. $\square$

**S01 relates the rows of a class directly**, not only through a chain. If cell $q - 1$ is white, the time-0 cut at
$q$ relates them all. If it is black, then $N \ge 2$, the rows read $1\,1\,0 \cdots 0$ or $1\,0\,\sigma$ from $q$ on,
with $\sigma$ a stripe word, one step takes these tails to stripe words after a white cell (the table of one step on
stripe tails in [StripeClassCount](../../Rule30Open/Frames/StripeClassCount.md), step 2), and the time-1 cut at
$q + 2$ relates them all. The rows of a class agree left of $q$ and are black at $q \ge 0$, so they have one left
edge.

**The class-size law.** Fix a left part $\lambda$ and $B \ge 1$, and take the $2^B$ rows $\lambda\rho$ with $\rho$ a
right half inside $[1, B]$. A class of a row with cell $B$ black is fixed by $q$ and the cells left of $q$, and $N$ is
the largest length exactly when the cells $q - 2, q - 1$ do not read $1\,0$ (then $s^*_{N+2}$ would fit) and, for
$N = 1$, cell $B - 1$ is white (else $s^*_2 = 11$ fits). Cells $\le 0$ belong to $\lambda$. So the classes are:

- $q \ge 2$ with cell $q - 1$ black: $2^{q-2}$ classes (cells $1, \dots, q - 2$ free) of $B - q$ rows (none when
  $q = B$);
- $q \ge 3$ with cells $q - 2$ and $q - 1$ white: $2^{q-3}$ classes of $B - q + 1$ rows; and for $q = 2$ with cells 0
  and 1 white, one class of $B - 1$ rows;
- $q = 1$: one class of $B$ rows when $\lambda$ is white at 0, of $B - 1$ when it is black there;
- $q = 0$ ($\lambda$ black at 0): one class of $B + 1$ rows when $\lambda$ ends in $0\,1$, which holds the empty right
  half (the word $1\,0 \cdots 0$ on $0, \dots, B$), and of $B$ rows when $\lambda$ ends in $1\,1$;
- the empty right half alone when $\lambda$ does not end in $0\,1$.

Summing over $q$: the nonempty right halves form $2^{B-1-k}$ classes of $k$ rows for $1 \le k \le B - 1$ and one class
of $B$ rows, and the empty right half is alone or joins the class of $B$ rows. For the single black cell
($\lambda = 1$, which ends in $0\,1$) that class is $\{(10)^k1, (10)^k11\}$ inside $[0, B]$, its $B + 1$ stripe seeds,
which have its center column in Lean ([SeedExtensions](../../Rule30Open/Seeds/SeedExtensions.md)). That no other row
of $[0, B]$ has it is the census below for $B \le 20$, and [the extension search](../seeds/no-other-extensions.md)
for this one class to 40 cells.

**Checks.** `family_labels` builds the classes from this description, with no relation and no step of the rule. The
tests compare it with the fibers of `rep` on every box of up to 10 cells, the census compares it with the classes of
the kit's definitions on every box and left part below, and `stripe_classes.class_sizes` checks the class-size law on
every box of up to 13 cells. The tests check the direct relation on every class of $[-3, 4]$.

## Completeness on boxes of up to 21 cells

Rows whose first $H$ center cells differ have different center columns, so for every box and every $H$
$$\#\{\text{prefixes of length } H\} \;\le\; \#\{\text{center columns}\} \;\le\; N(A, B),$$
the second inequality by the Lean bound. A box on which $N(A, B)$ rows have pairwise different prefixes therefore has
exactly $N(A, B)$ center columns, and since each of its $N(A, B)$ S01 classes (`s01_class_count`) has one center
column (the kit's soundness), its column classes are exactly the S01 classes. Finite prefixes decide it; no horizon
is assumed. `center_classes` finds the rows in three steps:

1. the first $T_1$ center cells of every row of the box, and the groups of rows with equal prefixes ($T_1 = 400$ in
   numpy up to 11 cells; $T_1 = 128$ from the C program `center_classes_census.c` for 12 to 21 cells);
2. the S01 classes, by joining the rows that share a key (time, cut cell, the cells left of the cut, and at time 1
   cell 0), with the kit's tail automaton `tailNext` deciding `StripeWord`; there are $N(A, B)$ on every box, and no
   class meets two prefix groups, as the kit's soundness requires;
3. one row of each class in every prefix group that holds two or more classes, all of them stepped together until
   every two have differed, or $T_2 = 20{,}000$.

No pair reached $T_2$: on each of the 231 boxes of up to 21 cells one row per class gives $N(A, B)$ different
prefixes. The *latest separation* of a box is the largest time at which two rows of different classes first differ,
the horizon at which a single count of prefixes would reach $N(A, B)$ there. Up to 11 cells no prefix group of
$T_1 = 400$ needed splitting.

| Cells | Latest separation | on | Rows with different left edges agree on at most | on |
|---:|---:|---|---:|---|
| 4 | 8 | $[0, 3]$ | 3 | $[-3, 0]$ |
| 5 | 16 | $[0, 4]$ | 6 | $[-3, 1]$ |
| 6 | 58 | $[0, 5]$ | 6 | $[-4, 1]$ |
| 7 | 59 | $[0, 6]$ | 13 | $[-5, 1]$ |
| 8 | 95 | $[0, 7]$ | 14 | $[-3, 4]$ |
| 9 | 167 | $[0, 8]$ | 14 | $[-4, 4]$ |
| 10 | 274 | $[0, 9]$ | 16 | $[-7, 2]$ |
| 11 | 275 | $[0, 10]$ | 21 | $[-6, 4]$ |
| 12 | 283 | $[0, 11]$ | 23 | $[-6, 5]$ |
| 13 | 362 | $[0, 12]$ | 24 | $[-10, 2]$ |
| 14 | 431 | $[0, 13]$ | 24 | $[-11, 2]$ |
| 15 | 436 | $[0, 14]$ | 27 | $[-12, 2]$ |
| 16 | 459 | $[0, 15]$ | 27 | $[-14, 1]$ |
| 17 | 674 | $[0, 16]$ | 30 | $[-15, 1]$ |
| 18 | 677 | $[0, 17]$ | 32 | $[-15, 2]$ |
| 19 | 678 | $[0, 18]$ | 34 | $[-16, 2]$ |
| 20 | 826 | $[0, 19]$ | 37 | $[-18, 1]$ |
| 21 | 829 | $[0, 20]$ | 40 | $[-17, 3]$ |

Up to 3 cells the latest separation is at most 3. From 4 cells on, the latest separation of each width is attained on
$[0, W - 1]$ alone, and it rises from 275 at 11 cells to 829 at 21. The last column is the longest common prefix of the
center columns of two rows of a box of that width with different left edges: on every box of up to 21 cells two rows
with different left edges differ at the center by time 40, while two rows with one left edge in different classes can
agree up to time 828.

The 21 boxes of 21 cells (the time-0 relation alone leaves as many classes or more):

| Box | Classes | Time 0 alone | Groups split | Latest separation | Different left edges agree on at most |
|---|---:|---:|---:|---:|---:|
| $[-20, 0]$ | 2,097,152 | 2,097,152 | 0 | 20 | 20 |
| $[-19, 1]$ | 1,835,008 | 1,835,008 | 226 | 311 | 37 |
| $[-18, 2]$ | 1,441,792 | 1,572,864 | 479 | 311 | 37 |
| $[-17, 3]$ | 1,245,184 | 1,441,792 | 1,278 | 311 | 40 |
| $[-16, 4]$ | 1,146,880 | 1,376,256 | 3,215 | 401 | 35 |
| $[-15, 5]$ | 1,097,728 | 1,343,488 | 6,884 | 478 | 34 |
| $[-14, 6]$ | 1,073,152 | 1,327,104 | 13,565 | 415 | 39 |
| $[-13, 7]$ | 1,060,864 | 1,318,912 | 25,277 | 489 | 37 |
| $[-12, 8]$ | 1,054,720 | 1,314,816 | 43,211 | 489 | 37 |
| $[-11, 9]$ | 1,051,648 | 1,312,768 | 67,466 | 491 | 31 |
| $[-10, 10]$ | 1,050,112 | 1,311,744 | 96,466 | 568 | 27 |
| $[-9, 11]$ | 1,049,344 | 1,311,232 | 125,991 | 568 | 27 |
| $[-8, 12]$ | 1,048,960 | 1,310,976 | 151,589 | 613 | 24 |
| $[-7, 13]$ | 1,048,768 | 1,310,848 | 166,708 | 588 | 23 |
| $[-6, 14]$ | 1,048,672 | 1,310,784 | 169,989 | 629 | 23 |
| $[-5, 15]$ | 1,048,624 | 1,310,752 | 160,596 | 632 | 22 |
| $[-4, 16]$ | 1,048,600 | 1,310,736 | 141,727 | 674 | 17 |
| $[-3, 17]$ | 1,048,588 | 1,310,728 | 117,346 | 701 | 16 |
| $[-2, 18]$ | 1,048,582 | 1,310,724 | 93,866 | 824 | 17 |
| $[-1, 19]$ | 1,048,579 | 1,310,722 | 70,440 | 826 | 18 |
| $[0, 20]$ | 1,048,577 | 1,310,720 | 50,668 | 829 | 19 |

"Groups split" counts the prefix groups of $T_1 = 128$ that held two or more classes. The time-0 relation alone also
leaves 12 classes on $[-1, 2]$ and 24 on $[-2, 2]$, against 11 and 22: time 1 adds the joins of the classes whose cell
$q - 1$ is black, which join a row ending in $1\,1\,1$ at $q - 1, q, q + 1$ to the rows ending in
$1\,1\,0\,\sigma$, with $\sigma$ a stripe word from $q + 2$.

**Per left part.** The census also checks the class-size law on every left part of every box above, and on longer
left parts: the left parts of the single cell's rows $R_1, \dots, R_{10}$ (that of $R_{10}$, on cells
$-10, \dots, 0$, is the integer 1602), every left part of up to four cells, and 2741 (an arbitrary one of 12 cells),
each with $B = 1, \dots, 10$ (240 runs); the left parts of $R_1, \dots, R_{14}$ and 2741 with $B = 16$ (latest
separations 489 to 666); and that of $R_{10}$ with $B = 20$ ($2^{20}$ rows, 524,289 classes, latest separation 689).
By `right_half_columns` each run is exact in the same way: every one has $2^{B-1} + 1$ center columns, or $2^{B-1}$
when the left part ends in $0\,1$, in classes of the sizes of the class-size law.

**A late pair.** The last pair of $[-10, 10]$ to differ, the rows `1..1.1.11..1.1..1111` and `1..1.11...1..11....1` on
cells $-9, \dots, 10$, differ at time 0 on cells $-3, -2, -1$ and on six cells of the right half. From time 1 on their
left halves agree (one step of Rule 30 merges the two left halves), and the leftmost cell of the difference stays
between cells 1 and 36 until the difference reaches the center at time 568. The kit's `Rule30TraceMerge` and
`Rule30TraceAmbiguity` build merges of this kind for rows with left edge $-3$ and show that no fixed horizon recovers
the left half from the center column; the census needs none, since it runs each pair to its own separation.

## Three facts about equal columns

These are proved on paper and not in Lean. For two configurations $x, y$ (finite or not) write
$d_j(t) = x_j(t) \oplus y_j(t)$.

- **Masking.** If $x$ and $y$ have the same column 0, $c$, then $d_{-1}(t) = (1 - c(t))\,d_1(t)$ for every $t$.
  *Proof.* $c(t + 1) = x_{-1}(t) \oplus (c(t) \lor x_1(t))$, and the same for $y$. If $c(t) = 1$ both give
  $x_{-1}(t) = y_{-1}(t) = \lnot c(t + 1)$; if $c(t) = 0$ they give
  $x_{-1}(t) \oplus x_1(t) = y_{-1}(t) \oplus y_1(t)$. $\square$
- **The right half fixes the row.** If $x$ and $y$ have the same column 0 and agree on every cell $\ge 1$, then
  $x = y$. *Proof.* Otherwise let $-k \le 0$ be their rightmost difference. One step moves it to $-k + 1$: cell
  $-k + 1$ at time 1 is $x_{-k} \oplus (x_{-k+1} \lor x_{-k+2})$, whose OR part is common, and every cell right of it
  reads only common cells. So the rows differ at cell 0 at time $k$. $\square$ So the rows of a column class have
  distinct right halves, and **completeness holds on every box $[-A, 0]$**: its $2^{A+1}$ rows have $2^{A+1}$ center
  columns, two of them differing by time $A$. This is the step of the rightmost difference in
  [reformulations](../../negative-results/dynamics/reformulations.md).
- **When left halves agree.** If $x$ and $y$ have the same column 0, $c$, their left halves agree at every time
  exactly when $d_1(t) = 0$ at every $t$ with $c(t) = 0$. *Proof.* One way by masking. The other way, masking gives
  $d_{-1} = 0$, and columns $0$ and $-1$ fix every column to their left, since
  $x_{i-1}(t) = x_i(t + 1) \oplus (x_i(t) \lor x_{i+1}(t))$. $\square$ Since the left half at time $t + 1$ reads only
  the left half and $c(t)$ at time $t$, the left halves agree at every time exactly when they agree at time 0. So
  "rows with equal center columns have equal left halves" says exactly: their columns 1 agree at every white time of
  the center column.

The tests check masking and the distinct right halves on every pair of rows with equal center columns of $[-3, 4]$, to
120 steps, and the boxes $[-A, 0]$ for $A \le 7$.

## Consequences

**Rows with equal center columns keep the left part.** On every box of up to 21 cells, rows with equal center columns
are joined by S01, so they agree on every cell $\le 0$ and have the same left edge: the kit's `EdgeObservable` holds
for every two rows supported in one box of up to 21 cells.

**Problem 1 from a count.** Let $C(A)$ be the number of distinct center columns of the rows supported in $[-A, A]$.
Then $C(A) \le N(A, A) = 4^A + 3 \cdot 2^{A-1}$ for every $A \ge 1$ (`box_columns`), and if $C(A) = N(A, A)$ for
infinitely many $A$, the center column is not eventually periodic. *Proof.* If $C(A) = N(A, A)$, the column classes
of $[-A, A]$ are its S01 classes (as above), and every row of a box inside $[-A, A]$ is a row of $[-A, A]$. Two finite
rows with equal center columns lie in such a box for large $A$, so they are joined, have one representative and one
left part, and so one left edge (if the left parts are white, both left edges are at least 1 and the kit's
`edges_equal_of_nonnegative` applies). That is `EdgeObservable`, and the kit's `problem1_of_edgeObservable` gives
Problem 1. Directly: an eventual period $P$ from $T$ would give the single cell's rows $R_T$ and $R_{T+P}$, with left
edges $-T$ and $-(T + P)$, equal center columns inside $[-(T + P), T + P]$. $\square$ The hypothesis is a lower bound
on the size of the image of a finite map, from the $2^{2A+1}$ rows of a box to center columns. It is not a statement
about one orbit, but a single missing column on a single box breaks it: it says again that every two rows that S01
does not join differ at the center.

## What it means

- **What is proved and what is open.** The upper bound is a theorem in Lean: at most $N(A, B)$ center columns on every
  box, and at most $2^{B-1} + 1$ from the $2^B$ right halves of one left part. The lower bound is the open part, the
  completeness of S01, which the kit leaves open. It is proved here for the boxes $[-A, 0]$ and found by computation
  on every box of up to 21 cells. It is a statement about every pair of rows, and its horizon grows with the width,
  from 275 steps at 11 cells to 829 at 21, the longest waits being on the boxes $[0, W - 1]$, which have no cell left
  of the center.
- **Where a proof would have to work.** In the late pair the left halves merge after one step. From then on the
  difference lies in cells $\ge 1$, the cells $\le 0$ agree, and the center columns stay equal until the first time
  $t$ at which cell 1 differs while the center is white; they differ at $t + 1$ (masking). Completeness says this
  happens for every two rows that S01 does not join. A proof needs that first-passage statement for differences in
  the right half; the kit's other open route to `EdgeObservable`, `ObserverCriterion` of `Rule30DividedDifference`,
  asks for the same kind of observation of a difference.
- **Formalization.** The classes, their number and the bound on center columns are in Lean
  ([StripeClassCount](../../Rule30Open/Frames/StripeClassCount.md), [StripeClasses](../../Rule30Open/Frames/StripeClasses.md)).
  Not yet: the written-out classes and the class-size law (finite combinatorics on `rep`), the direct relation within
  a class, the three facts above, and the reduction of Problem 1 to $C(A) = N(A, A)$, which needs only `box_columns`,
  `s01_class_count`, `joined_iff`, that `rep` keeps the left part, and the kit's `problem1_of_edgeObservable`. The
  census itself, $2^{21}$ rows over hundreds of steps per box, is beyond the kernel.

## The kit

`Rule30StripeMeeting` defines the stripe relation and proves its soundness (`stripe_related_same_trace`,
`stripe_related_preserves_two`) and that it is entered at time 0 or 1 if at all (`stripe_meeting_is_early`,
`no_delayed_stripe_meeting`, `eventually_stripe_iff_early`); its docstring leaves completeness for equal infinite
traces open. It does not describe or count the classes. `Rule30TraceEdge` states `EdgeObservable` as open and proves
`problem1_of_edgeObservable` and `edges_equal_of_nonnegative`; `Rule30DividedDifference` gives a second open route to
it (`ObserverCriterion`). The equivalent forms prove the stripe seeds (`TransformsSeeds`, `stripeSeed_center`) and
check numerically that among the nonzero seeds in $[0, 13)$ exactly they reproduce the column for 300 steps, which is
the single cell's class on the box $[0, 12]$ here; `AlgebraicDegree.card_trace` counts prefixes (each word of length
$n + 1$ is the trace of exactly $2^n$ of the configurations on $[-n, n]$), not whole columns of finite rows. Neither
part counts the center columns of a box.

## Reproduce

```bash
python -m computations.center_classes boxes                       # every box of up to 11 cells, T1 = 400: 5 s
python -m computations.center_classes boxes --widths 12-21 --c    # every box of 12 to 21 cells: 15 to 30 min, 0.5 GB
python -m computations.center_classes parts                       # 24 left parts, B = 1 .. 10: 10 s
python -m computations.center_classes parts --c --B 16 \
    --parts 3,6,13,25,55,100,222,401,891,1602,3558,6428,14259,25646,2741   # 15 left parts: 17 s
python -m computations.center_classes parts --c --B 20 --parts 1602      # 2^20 rows: 35 s, 0.3 GB
python -m computations.center_classes pair 612687 615009 --B 10   # the late pair of [-10, 10]: 2 s
python -m computations.stripe_classes --sizes 13                  # the class-size law to 13 cells: about 10 s
```

`--c` takes the prefix groups from [center_classes_census.c](../../computations/center_classes_census.c), compiled on
first use (`cc -O2 center_classes_census.c -o center_classes_census` builds it by hand). Each line of output is one box
or left part; `boxes` ends with a line per width, and on the boxes of up to 6 cells also joins every pair with the
kit's relation transcribed literally (`stripe_classes.classes_all_pairs`).
[tests/test_center_classes.py](../../tests/test_center_classes.py) checks the counts against every row of the boxes of
up to 7 cells and of $[-4, 4]$ run with `rule30.step`, the keyed classes against every pair and against the fibers of
`rep`, the written-out classes and their sizes, the split (with survivors at a short horizon), the C program against
numpy, and the facts about equal columns.
