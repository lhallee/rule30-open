---
title: Read from the left, the cells -t to -3 of the cone are pairwise distinguishable for 3 ≤ t ≤ 17, so left-to-right ordered decision diagrams of the center have width 2^(t-2) there, and not at t = 18
category: complexity
problems: [3]
status: proved
lean: Rule30Open.Complexity.LeftCut
headline: [left_cut, left_cut_at, left_cut_factor, left_cut_width, left_cut_fails_18, stripe_three_18, stripe_four_18,
  left_cut_of_check, separates_of_refineMasks, testBit_sliceCenter]
kit: new
kit_modules: [Rule30Equivalents.QueryComplexity, Rule30Equivalents.TFunction]
evidence: [computations/left_cut.py, tests/test_left_cut.py]
---

# Read from the left, the cells -t to -3 of the cone are pairwise distinguishable for 3 ≤ t ≤ 17, so left-to-right ordered decision diagrams of the center have width 2^(t-2) there, and not at t = 18

A row is a map from the integers to colors, one step of Rule 30 is $x'_j = x_{j-1} \oplus (x_j \lor x_{j+1})$, and
$c_t(x)$ is cell 0 after $t$ steps, a function of the cells $x_{-t}, \dots, x_t$. Write $\mathrm{splice}_a(x, z)$ for
the row equal to $x$ left of cell $a$ and to $z$ from cell $a$ on (`spliceAt`).

## Statement

Let $3 \le t \le 17$.

- `left_cut`: if the rows $x$ and $y$ differ at some cell $i$ with $-t \le i \le -3$, there is a row $z$ with
  $c_t(\mathrm{splice}_{-2}(x, z)) \ne c_t(\mathrm{splice}_{-2}(y, z))$.
- `left_cut_at`: the same for every cut $a \le -2$: rows that differ at some cell $i$ with $-t \le i < a$ have a common
  $z$ with $c_t(\mathrm{splice}_a(x, z)) \ne c_t(\mathrm{splice}_a(y, z))$.
- `left_cut_factor`: if $c_t(\mathrm{splice}_a(x, z)) = G(F(x), z)$ for all rows $x, z$, for some set $S$ and maps
  $F$ from rows to $S$ and $G$ from $S$ and rows to colors, then $F(x) = F(y)$ forces $x_i = y_i$ for $-t \le i < a$.
- `left_cut_width`: with the cut after the $k$ leftmost cells of the cone, $a = -t + k$ and $0 \le k \le t - 2$, the
  rows carrying the bits of $P < 2^k$ on the cells $-t, \dots, -t + k - 1$ have pairwise different states $F$: $S$ has
  at least $2^k$ elements.

So the number $N_{\mathrm{L}}(t, k)$ of distinct functions that the center leaves after the $k$ leftmost cells are fixed
is $2^k$ for every $k \le t - 2$ and $3 \le t \le 17$. Read as models of computation: an ordered binary decision
diagram that reads $x_{-t}, x_{-t+1}, \dots$ in this order and computes $c_t$ has at least $2^k$ nodes at level $k$
(its nodes at that level are a set $S$ as above, $F$ the path from the root and $G$ the rest of the diagram), and a
one-way protocol in which one party holds the $k$ leftmost cells and sends one message to the party holding the rest
uses at least $2^k$ messages, so exactly $k$ bits.

The range is sharp:

- `stripe_three_18`: if $x_{-j} = 1$ exactly for the odd $j$ with $3 \le j \le 18$, then $c_{18}(x) = 0$, whatever the
  cells $-2, -1, 0, \dots$ are.
- `stripe_four_18`: if $x_{-j} = 1$ exactly for the even $j$ with $4 \le j \le 18$, then $c_{18}(x) = 1$, whatever the
  cells $-3, -2, \dots$ are.
- `left_cut_fails_18`: the first of these rows and the second with cell $-18$ flipped differ at cell $-4$ and have the
  same center after 18 steps for every completion from $-2$ on. So `left_cut` is false at $t = 18$.

## Argument

**Reduction to numbers.** The prefix $x_{-t}, \dots, x_{-3}$ is the number $P < 2^{t-2}$ with bit $k$ equal to
$x_{-t+k}$ (`enc` of [ConeScreening](ConeScreening.md)), and a completion is a number $r$ with bit $k$ equal to the
cell $-2 + k$ of $z$ (`rowN r (-2)`). The center of the spliced row is bit 0 of `nevo` applied $t$ times to
$2^{t-2} r + P$ (`cutCenter`, `evo_splice_cut`, through `evo_local` and `evo_rowN`). So `left_cut` at $t$ follows from:
for every two numbers $P \ne Q$ below $2^{t-2}$ some completion $r$ of a fixed list gives different values
(`left_cut_of_check`).

**The check.** `cutCheck t rs` holds the list `rs` of completions (`cutCert3` to `cutCert17`) and checks, by
`decide +kernel`, that every $r$ is below $2^{t+3}$ and that splitting the class of all $2^{t-2}$ prefixes by the
value at the first completion, each part by the value at the second, and so on, leaves no part of two or more prefixes.

- The prefixes are evaluated all at once: place $k$ of a *sliced row* is a number whose bit $P$ is cell $k$ of the row
  of prefix $P$ (a pattern of the bits of $P$ for a prefix cell, `cellPattern`, and all ones or all zeros for a
  completion cell, `rowCell`). Rule 30 acts on sliced rows by the formula of `nstep`, bitwise (`sliceStep`,
  `nth0_sliceStep`), so bit $P$ of the sliced center is the center of prefix $P$ (`testBit_sliceEvo`,
  `testBit_sliceCenter`).
- A class of prefixes is a mask, and `refineMasks` splits each mask $m$ by a column $C$ into $m \land C$ and
  $m \oplus (m \land C)$, dropping a part $u$ with $u \land (u - 1) = 0$, which has at most one bit (`eq_of_lowOne`).
  If the list of masks is empty at the end, every two bits of the starting mask differ at some completion
  (`separates_of_refineMasks`, by induction on the list of completions).

The completions are chosen by `computations/left_cut.py` (`certificate`): from the rows with any colors on the cells
$-2, -1$ and at most one black cell in the right half $x_0, \dots, x_t$ for $t \le 12$, and at most two for
$13 \le t \le 17$, in the order that leaves the fewest unseparated pairs at each step. The lists have
1, 2, 3, 4, 6, 8, 10, 13, 14, 19, 18, 22, 24, 26, 32 completions for $t = 3, \dots, 17$, against the lower limit of
$t - 2$ that $2^{t-2}$ prefixes force. The module builds in about 45 seconds, with a peak of about 2.6 GB.

**The failure at 18.** With the prefix fixed, the completions are sliced instead: place $k$ is all ones or all zeros by
the prefix for $k < t - 2$ and the pattern of completion cell $k - (t - 2)$ over the $2^{t+3}$ completions otherwise
(`rowCellC`), and bit $r$ of `completionCenters t P` is the center for completion $r$ (`testBit_completionCenters`).
The kernel finds `completionCenters 18 P` equal to 0 for the odd stripe ($P = 43690$) and to all ones for the even
stripe with cell $-3$ white or black ($P = 21845, 54613$): numbers of $2^{21}$ bits. `center_of_prefix` reads the
center of any row through its prefix and its cells $-2, \dots, t$, and `flip_center` of
[ConeScreening](ConeScreening.md) turns the even stripe's black into white for the flipped row.

**Every cut.** For a cut $a \le -2$ apply `left_cut` to $x$ and the row that is $y$ left of $a$ and $x$ from $a$ on;
the completion $z$ found for the cut at $-2$, preceded by the cells of $x$ between $a$ and $-3$, separates $x$ and $y$
at the cut $a$ (`left_cut_at`). `left_cut_factor` is the contrapositive, and `left_cut_width` applies it to the rows
`rowN P (-t)`, which differ on the first $k$ cells when $P \ne Q$.

## What it means

This is a statement about all rows, in the row model of [cone screening](../../findings/complexity/cone-screening.md),
and does not bound the cost of computing the center column of the single black cell, which is one row. Two facts keep
it apart from the bounds that [restricted models](../../negative-results/complexity/restricted-models.md) found to hold
for Rule 90 as well. Every linear rule makes $c_t$ a sum over GF(2) of the cells, so fixing any $k$ cells leaves at most
two functions (the rest of the sum, and its complement): Rule 30 has width $2^{t-2}$ where Rules 90 and 150 have 2. And
the exact range is short. By [ConeScreening](ConeScreening.md) the settings of the full left half $x_{-t}, \dots, x_{-1}$
are not pairwise distinguishable for $t \ge 9$; those of $x_{-t}, \dots, x_{-2}$ are not for $13 \le t \le 16$, by
computation; those of $x_{-t}, \dots, x_{-3}$ are for $t \le 17$ and are not at $t = 18$, by the stripes above. Each
failure comes from an alternating stretch that ends in a black cell next to the cut, and
[the left cut](../../negative-results/complexity/left-cut.md) records the counts to $t = 20$ and the route that stops
there.

The kit has no ordered decision diagram, branching program or communication bound for Rule 30, in its core or in its
equivalent forms (pinned commit and main branch); its `QueryComplexity` bounds the depth of decision trees for the same
function by its algebraic degree, and its `TFunction` reads rows as 2-adic numbers whose lowest differing bit Rule 30
keeps, which concerns the rightmost difference, not the leftmost. The statement and its proof are new.
