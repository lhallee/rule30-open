---
title: The routing lemma for the least certificate of the center fails at t = 12, and the sets that one step maps into themselves are too weak for an induction
category: complexity
problems: [3]
status: negative
kind: refuted
evidence: [computations/min_certificate.py, tests/test_min_certificate.py]
---

# The routing lemma for the least certificate of the center fails at t = 12, and the sets that one step maps into themselves are too weak for an induction

**Question.** Write $c_t$ for the center after $t$ steps of Rule 30 as a function of the cone cells
$x_{-t}, \dots, x_t$ of a row given as input, and $m(t)$ for the least number of fixed cells of a subcube (a partial
row) on which $c_t$ is constant. [MinCertificate](../../Rule30Open/Complexity/MinCertificate.md) proves
$m(t) \le t - 1$ for $t \ge 9$ and computes $m(t) = t - 1$ for $9 \le t \le 15$. Can a lemma about one free cell give
$m(t) \ge t - 1$ for every $t$?

**The routing lemma.** Every constant subcube fixes $x_{-t}$, so it has a leftmost free cell $u = -t + k$ with
$k \ge 1$, and all $k$ cells left of $u$ are fixed. On a constant subcube the derivative
$D_u c_t(x) = c_t(x) \oplus c_t(x \text{ with } x_u \text{ flipped})$ is identically 0. Let $R(t, k)$ be the least
number of fixed cells right of $u$ over subcubes with $u$ free, every cell left of $u$ fixed, and $D_u c_t \equiv 0$.
The lemma is $R(t, k) \ge t - k - 1$ for every $k$; it gives $m(t) \ge k + (t - k - 1) = t - 1$.

**Outcome.** The lemma holds for $t \le 11$ and fails at $t = 12$, $k = 1$, and at $t = 13$ and $14$, $k = 2$. The
conjecture $m(t) = t - 1$ survives, since $m(12) = 11$, $m(13) = 12$ and $m(14) = 13$: the subcubes that break the lemma make the derivative
vanish without making $c_t$ constant. The one-step reduction behind the lemma keeps $k$ and lowers $t$, but it maps a
subcube to a set that is not a subcube, and the class of sets it does preserve is far too weak.

## 1. The table

`routing` computes $R(t, k)$ exactly, over all $2^k$ values of the cells left of $u$ and all subcubes of the cells
right of $u$, by the same breadth-first pass as the least sizes (MinCertificate, item 4). The excess
$R(t, k) - (t - k - 1)$:

| $t$ \ $k$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 8 | 0 | 0 | 1 | 2 | 1 | 2 | 1 | 1 | | | | | |
| 9 | 1 | 0 | 1 | 1 | 1 | 1 | 2 | 0 | 1 | | | | |
| 10 | 0 | 0 | 1 | 1 | 2 | 1 | 2 | 2 | 0 | 1 | | | |
| 11 | 0 | 0 | 1 | 1 | 2 | 1 | 2 | 1 | 1 | 0 | 1 | | |
| 12 | **−1** | 0 | 0 | 0 | 1 | 1 | 2 | 1 | 1 | 1 | 0 | 1 | |
| 13 | 0 | **−1** | 0 | 0 | 1 | 1 | 2 | 1 | 1 | 1 | 0 | 0 | 1 | |
| 14 | 0 | **−1** | 0 | 0 | 1 | 1 | 0 | 0 | 1 | 1 | 1 | 0 | 0 | 1 |

For $t \le 7$ the excess is at least 0 everywhere, with 0 only at $(t, k) = (4, 1), (5, 2)$. The values $R(t, k)$
themselves, for $t = 12$: 9, 9, 8, 7, 7, 6, 6, 4, 3, 2, 0, 0. The zero at $k = t - 1$ is the stripe of
MinCertificate: with $x_{-t}, \dots, x_{-2}$ fixed as there, $D_{-1} c_t \equiv 0$ with no cell right of $-1$ fixed.

**The counterexamples.** At $t = 12$, $u = -11$: take $x_{-12}$ either color, $x_j = [j \text{ odd}]$ for
$-7 \le j \le 1$ (so $x_{-7} = 1$, $x_{-6} = 0$, ..., $x_1 = 1$), and every other cell free. These are 9 fixed cells
right of $u$, one fewer than $t - k - 1 = 10$, and $D_{-11} c_{12} \equiv 0$ on the subcube, while $c_{12}$ is not
constant on it. Another is the odd stretch $x_j = [j \text{ odd}]$ for $-9 \le j \le -1$, from the wall at $-1$,
with every other cell right of $u$ free. At $t = 13$, $u = -11$: $x_{-13}$ either color, $x_{-12} = 0$ and $x_j = [j \text{ even}]$ for
$-10 \le j \le -2$, again 9 fixed cells right of $u$ where the lemma needs 10.

## 2. Where the induction stops

**The one-step reduction (proved here on paper, checked by the test on random rows).** If $x_{u+1} = 1$, and
$x_{u-1} = 1$ or $u = -t + 1$, then $D_u c_t(x) = D_{u+1} c_{t-1}(x')$, with $x'$ the row after one step. Proof: the
cell $u + 1$ at time 1 reads $x_u$ through the XOR with its left parent, so it flips. The cell $u$ reads $x_u \lor x_{u+1}$,
which is 1 either way. The cell $u - 1$ reads $x_{u-1} \lor x_u$, which is 1 either way, or lies outside the cone of
$c_{t-1}$ when $u = -t + 1$. No other cell reads $x_u$. Since $u + 1 = -(t - 1) + k$, the reduction keeps $k$ and lowers
$t$ by one.

**What it needs and does not have.** The bound $t - k - 1$ drops by one with $t$, so each step must use up one fixed
cell right of $u$. It does not. The cell $x'_j = x_{j-1} \oplus (x_j \lor x_{j+1})$ is free in the image when $x_{j-1}$
is free, and constrained when $x_{j-1}$ is fixed, so the constrained cells of the image right of $u + 1$ are the fixed
cells of the subcube shifted right by one, plus the cell $u + 2$ when the adversary sets a free $x_{u+1}$ to 1; only the
fixed cells among $x_{t-1}, x_t$ leave the cone. And a constrained cell of the image is not fixed: $x'_j$ is
$x_{j-1} \oplus (x_j \lor x_{j+1})$, a function of the row to its right. So the image of a subcube is a set in which each
cell, given the cells to its right, is either free or restricted, and the induction hypothesis about subcubes does not
apply to it.

**The class that one step preserves is too weak.** Call a set of rows right-determined with constrained cells $P$
when each cell outside $P$ takes both values above every allowed choice of the cells to its right. One step maps such a
set into one of the same kind with constrained cells at most $P + 1$. The least number of constrained cells right of $u$
that makes $D_u c_t$ vanish on such a set, `routing(t, right_determined=True)`, is a game in which each constrained cell
is chosen as a function of the cells to its right. It stays small:

| $t$ | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| right-determined, $k = 1$ | 1 | 2 | 1 | 2 | 1 | 4 | 1 | 2 | 1 | 4 | 1 | 2 |
| the lemma needs $t - 2$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |

It stays small for every $k$: at $t = 14$ the values for $k = 1, \dots, 14$ are 2, 4, 4, 4, 4, 3, 3, 3, 3, 3, 2, 1, 0, 0,
against $t - k - 1 = 12, 11, \dots$.

At $k = 1$ and odd $t$ one cell suffices, for every odd $t$: by the front recursion of
[SecondCells](../../Rule30Open/Complexity/SecondCells.md),
$D_{-t+1} c_t = t \oplus \bigoplus_{s < t} x(s, -t + 2 + s)$, and each of the $t$ cells $x(s, -t + 2 + s)$ has
$x_{-t+2}$ as the leftmost cell of its cone, so it flips with $x_{-t+2}$ (ConeScreening's `front_xor`). For odd $t$ the
derivative flips with $x_{-t+2}$ on every row, and choosing $x_{-t+2}$ as a function of the cells to its right makes it
0. So an induction that keeps only the count of constrained cells cannot work; it must keep the form
$x_{j-1} \oplus (x_j \lor x_{j+1})$ of the constraints, and after $s$ steps that form is the full $s$-step map.

## 3. What remains

The conjecture $m(t) = t - 1$ for every $t \ge 9$ is open; MinCertificate has the upper bound for every $t$ and the
lower bound for $t \le 15$. The least subcubes are not only stripes from $t = 12$ on (16 at $t = 12$, 14 at $t = 13$,
46 at $t = 14$, 72 at $t = 15$), so a proof must handle partial rows with free cells inside the fixed stretch. A lower bound that
replaces the routing lemma must use more than the leftmost free cell: at $(12, 1)$ the derivative along $u$ vanishes,
and what keeps $c_{12}$ from being constant is a free cell further right.

## Reproduce

```bash
python -m computations.min_certificate --max-t 8 --controls-t 1 --routing-t 14 --stripe-t 9 --dp-t 1 --list-t 8
```

The routing table takes about four minutes, most of it at $t = 14$ (under 1 GB). The test `tests/test_min_certificate.py` checks
$R(3, k)$ and its right-determined form against listings of partial rows and games, the subcube of the counterexample
at $t = 12$ (the derivative along $x_{-11}$ vanishes and $c_{12}$ is not constant), and the one-step reduction.
