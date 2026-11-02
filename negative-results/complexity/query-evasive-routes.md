---
title: The derivative along the second cell, gates after restrictions and measures other than adaptive certificates do not prove that the center needs its whole cone for every t
category: complexity
problems: [3]
status: negative
kind: dead-end
evidence: [computations/query_evasive.py, computations/query_evasive_sums.c, tests/test_query_evasive.py]
---

# The derivative along the second cell, gates after restrictions and measures other than adaptive certificates do not prove that the center needs its whole cone for every t

**Question.** Write $c_t$ for the center after $t$ steps of Rule 30 as a function of the $2t + 1$ cells
$x_{-t}, \dots, x_t$ of an arbitrary row, $D(f)$ for the least depth of a decision tree for $f$, and
$\mu(f) = \sum_x (-1)^{|x|} f(x)$ for the top coefficient of the real polynomial of $f$, up to sign.
[CornerOr](../../Rule30Open/Complexity/CornerOr.md) proves that $D(c_t) = 2t + 1$ if and only if $G_t$, the center with
$x_{-t}$ and $x_{t-1}$ white, needs all its $2t - 1$ cells, and computation gives this for $t \le 22$. Its GF(2)
adversary wins against every tree that reads $u = x_{-t+1}$ before the last query. Can one of three routes prove
$D(G_t) = 2t - 1$ for every $t$: (1) an adversary for the trees that read $u$ last, from the derivative
$\partial_u G_t$, combined with one for the other trees; (2) a recursive adversary that finds, after each forced answer,
a new cell that enters by XOR or a new pair that enters through a gate, and repeats at $t - 1$; (3) a lower-bound
measure other than the adaptive certificates of [QueryDepth](../../Rule30Open/Complexity/QueryDepth.md)?

This is a question about the query model for an arbitrary row. Its answer, either way, does not bound the cost of the
single black cell's column, the row of the prize, where a tree reads nothing.

**Outcome.** Each route stops at a step named below. The structure each route uses is proved for every $t$ in Lean
([SecondCells](../../Rule30Open/Complexity/SecondCells.md)); the stops are computed on the ranges given, except the stop
of the linear measures in route (3), which is proved. Other routes are in
[query-depth routes](query-depth-routes.md) and [adversary routes](query-adversary-routes.md).

## (1) The derivative along $u$

Write $S$ for the $2t - 2$ cells of $G_t$ other than $u$, $P_a$ for $G_t$ with $u = a$, and $Q_t = P_0 \oplus P_1$, the
derivative. A tree that reads $u$ last has read all of $S$ when it asks for $u$, and it asks only if $Q_t = 1$ at the
row it has read. SecondCells proves that $Q_t$ is $t$ plus the parity of the $t$ cells $(s, -t + 2 + s)$, that it flips
with $L = x_{-t+2}$ on every row for odd $t$ and ignores $L$ for even $t$, and that $Q_t$ with $L$ white is $G_{t-1}$
(shifted one cell right) plus nested centers that do not see $x_t$.

- *The case $u$ last alone.* If $Q_t$ needs all of $S$, an adversary for $Q_t$ keeps it non-constant until the last
  cell of $S$ and answers that cell so that $Q_t = 1$; then the tree must read $u$. For odd $t \le 21$ this holds
  ($\mu$ of $Q_t$ with $L$ white is nonzero for $4 \le t \le 21$, and the exact depth settles $t = 3$). For even $t$
  it fails at every $t$, since $Q_t$ ignores $L$. The game on $S$ itself (`u_last_games`, `u_last`), in which the tree
  must find $(P_0, P_1)$ and the adversary wins at a full row of $S$ with $Q_t = 1$, is won by the adversary for
  $2 \le t \le 9$, as it must be, since $G_t$ needs all its cells there.
- *The two orders together.* An adversary does not know whether the tree will read $u$ last. Keeping both $Q_t$ and
  one of $P_0, P_1$ needing all of the free cells of $S$ is possible at the start for odd $t$, and no adversary keeps
  both through the game for $2 \le t \le 9$ (`joint_game`): at some query the answers that keep $Q_t$ hard and those
  that keep $P_0$ or $P_1$ hard are different.
- *CornerOr's GF(2) adversary.* It answers each cell of $S$ so that the GF(2) coefficient of the product of the free
  cells of $S$ in $P_0$ stays 1; the answer is forced at every query, and the adversary wins at once if the tree reads
  a cell after which $Q_t$ has full GF(2) degree. It wins against every tree at $t = 2$ and loses against some tree
  that leaves $u$ for last for $3 \le t \le 9$ (`gf2_game`).

**Where it stops.** The case $u$ last reduces, for odd $t$, to the evasiveness of $Q_t$ with $L$ white, a function of
$2t - 3$ cells of the same kind as $G_t$, a copy of $G_{t-1}$ plus a sum of nested centers. Its top coefficients
($0, -2, 2, -2, -10, -6, 6, 4, 10, -52, 50, 6, -46, -96, 38, -418, 98, 224, 818$ for $t = 3, \dots, 21$) follow no
pattern, as those of $G_t$ do not. For even $t$ the reduction does not apply, and for every $t \ge 3$ checked the
adversaries for the two orders do not combine into one.

## (2) Gates after restrictions

`structure` lists the cells with which a function flips on every row and the pairs of cells it reads through a gate of
two inputs (the four cofactors at the pair are at most two functions).

- $G_t$ itself has neither for $3 \le t \le 12$.
- Its restrictions to one cell: for $5 \le t \le 12$ the only one with either is $x_{t-3} = 1$, which leaves the pair
  $(x_{t-2}, x_t)$ joined by an AND. SecondCells proves this for every $t$ (`center_second_and`), and with
  `center_second_shield` it forces an answer as CornerOr's OR does: once $x_{t-3}$ is black, the first of
  $x_{t-2}, x_t$ to be read must be answered black, or the other one no longer matters. At $t = 3, 4$ a few other
  restrictions have a gate or a flip cell (listed by the code).
- The function after that step, $F_t$ ($G_t$ with $x_{t-3}$ black and the pair merged into its AND, $2t - 3$ cells),
  has no flip cell and no gate pair, and neither has any of its restrictions to one cell, for $5 \le t \le 9$. Its
  exact depth is $2t - 3$ for $t = 6, 7, 8$ and $6 < 7$ at $t = 5$.

**Where it stops.** The corner step of CornerOr repeats once, one step into the cone, and only after the tree has
read $x_{t-3}$ and the adversary has answered it black; a tree can read $x_{t-2}$ or $x_t$ first. After that step no
further gate or XOR cell appears on the computed range, so the argument does not descend to $t - 2$.

## (3) Other measures

- *Linear certificates* (proved). The indicator vectors of the subcubes with at least one free cell span the functions
  $f$ with $\mu(f) = 0$: the edges $\{x, x \oplus e_i\}$ of the cube already do, since the cube is a connected
  bipartite graph and the sums of the two ends of its edges span the vectors orthogonal to $(-1)^{|x|}$
  (`linear_certificate_rank` gives rank $2^n - 1$ for $n \le 5$). A tree of depth below $n$ is a sum of such indicators
  over its 1-leaves, so every linear functional that vanishes on all trees of depth below $n$ is a multiple of $\mu$.
  This covers the real polynomial method, the polynomial method over $\mathbb{Z}/4$, $\mathbb{Z}/8$ or any ring (the
  multilinear representation of a function is unique over any ring, and its top coefficient is $\pm\mu$ reduced), and
  the reduced Euler characteristic of the topological criterion. All of them fail at $t = 14$, where $\mu(c_{14}) = 0$,
  and give no all-$t$ statement, since nothing is known about $\mu$ in general.
- *Approximate degree* (computed). The least degree of a real polynomial within $1/3$ of $G_t$ is $t$ for
  $2 \le t \le 6$, far below the $2t - 1$ cells (`approximate_degree`, linear programming; $t = 6$ takes about five
  minutes with `--adeg 6`).
- *Certificates* (proved in [RightCorner](../../Rule30Open/Complexity/RightCorner.md)). Randomized certificate
  complexity, block sensitivity and sensitivity are at most the certificate complexity, which is at most $2t$ for
  $c_t$.
- *Symmetry* (computed). The Kahn-Saks-Sturtevant criterion needs a monotone function with a transitive group of
  symmetries. $G_t$ is monotone in no cell, increasing or decreasing, for $3 \le t \le 8$ (`monotone_cells`), and no
  permutation of its cells with negations of cells, other than the identity, fixes it for $t = 3, 4, 5$
  (`automorphisms`). With the trivial group the criterion reduces to the Euler characteristic, the linear certificate
  above.

**Where it stops.** Every linear measure is a multiple of $\mu$, and each other measure tried here is below the number
of cells: the certificate measures for every $t$, the approximate degree for $t \le 6$. What reaches $2t + 1$ on the
computed range is adaptive: QueryDepth's certificates, which fix one or two cells and read $\mu$ of the restriction.

## What it means

The structure near the four ends of the cone is proved for every $t$: $x_{-t}$ enters by XOR, the derivative along
$x_{-t+1}$ is $t$ plus the parity of a diagonal that ends in a copy of $c_{t-1}$, $x_{t-1}, x_t$ enter by an OR, and
$x_{t-2}, x_t$ by an AND once $x_{t-3}$ is black. None of it yields a proof for every $t$, because the open case needs
one adversary that serves a tree reading $u$ last and a tree reading it earlier at once, and on the computed range the
natural adversaries for the two cases give different answers. As a heuristic, a proof would have to control the
derivative $Q_t$ and the restrictions $P_0, P_1$ together, through the dynamics of the diagonal that $Q_t$ sums, rather
than through a coefficient.

## Reproduce

```bash
python -m computations.query_evasive --max-t 9 --structure 12 --sums 21 --threads 1   # about ten minutes
```
