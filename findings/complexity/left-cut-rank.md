---
title: The GF(2) rank of the cone across a left cut after a cells is 2 + floor(2^a / 3) for every a ≤ t - 3 and t ≤ 14, spanned by the settings without an alternating stripe ending 11, and no window of fixed width carries it to every t
category: complexity
problems: [3]
status: computed
formalization: partial
evidence: [computations/left_cut_rank.py, tests/test_left_cut_rank.py]
---

# The GF(2) rank of the cone across a left cut after a cells is 2 + floor(2^a / 3) for every a ≤ t - 3 and t ≤ 14, spanned by the settings without an alternating stripe ending 11, and no window of fixed width carries it to every t

Write $c_t$ for the center cell after $t$ steps as a function of the cells $x_{-t}, \dots, x_t$ of an arbitrary row,
with $x'_j = x_{j-1} \oplus (x_j \lor x_{j+1})$. Cut the row after its $a$ leftmost cells: the *left setting* $u$ is
$x_{-t}, \dots, x_{-t+a-1}$, the *right setting* $v$ the rest. $\mathrm{rank}(t, a)$ is the GF(2) rank of the matrix
$[c_t(u, v)]$, and $N_{\mathrm{L}}(t, a)$ the number of its distinct rows, the width at level $a$ of every ordered
decision diagram that reads the row from the left ([LeftCut](../../Rule30Open/Complexity/LeftCut.md)). Independent rows
are distinct, so $\mathrm{rank}(t, a) \le N_{\mathrm{L}}(t, a)$ (Lean, `width_of_independent` of
[LeftCutRank](../../Rule30Open/Complexity/LeftCutRank.md)). Let $\rho(a) = 2 + \lfloor 2^a / 3 \rfloor$: 2, 3, 4, 7, 12,
23, 44, 87, 172, 343, 684, 1367 for $a = 1, \dots, 12$, with $\rho(a) - 2 = 2(\rho(a - 1) - 2) + [a \text{ even}]$. Every
linear rule has rank at most 2 at every cut.

## Results

1. **The rank, exactly.** $\mathrm{rank}(t, a) = \rho(a)$ for every $a \le t - 3$ and $t \le 14$, and for $a = t - 2$
   when $t \le 11$. At $a = t - 2$ it falls below $\rho$ from $t = 12$ on, in the range computed:

   | $t$ | 9 | 10 | 11 | 12 | 13 | 14 |
   |---|---:|---:|---:|---:|---:|---:|
   | $\mathrm{rank}(t, t - 3) = \rho(t - 3)$ | 23 | 44 | 87 | 172 | 343 | 684 |
   | $\mathrm{rank}(t, t - 2)$ | 44 | 87 | 172 | 295 | 387 | 557 |
   | $\rho(t - 2)$ | 44 | 87 | 172 | 343 | 684 | 1367 |
   | $\mathrm{rank}(t, t - 1)$ | 79 | 104 | 153 | 202 | 295 | |

   Every entry is exact: from the truth table for $t \le 12$ and every $a \le t - 1$, and from the bit-packed table for
   $t = 13, 14$ and $a \le 12$. Since $N_{\mathrm{L}}(t, t - 2) = 2^{t-2}$ for $t \le 17$, the rank is far below the
   width: about a third of $2^a$.

2. **An explicit basis.** Let $B_a$ be the left setting with $x_{-t}$ black and every other cell white, together with the
   settings with $x_{-t}$ white whose word $x_{-t+1} \cdots x_{-t+a-1}$ has no prefix $(10)^k 11$, $k \ge 0$: an
   alternating stripe that ends in two black cells. $B_a$ has $\rho(a)$ members, and it is closed under turning black
   cells white. At every $(t, a)$ computed ($t \le 12$ and $a \le t - 1$; $t = 13, 14$ and $a \le 12$) the rows of
   $B_a$ span the row space: their rank is $\mathrm{rank}(t, a)$. So they are a basis exactly where
   $\mathrm{rank}(t, a) = \rho(a)$. The reason, in the algebraic normal form: for $3 \le t \le 10$ and $2 \le a \le t - 1$,
   every monomial in the left cells (without $x_{-t}$) whose word has a prefix $(10)^k 11$ has a coefficient function of
   the right cells that is 0 or the constant 1; by Moebius inversion over the down-set $B_a$, every row outside $B_a$
   is then a sum of rows of $B_a$ (the all-ones row is the sum of the rows of the two settings of $B_a$ that are white
   right of $x_{-t}$).

3. **The windowed witness.** On the rows whose right setting is a word $w$ of $L$ cells followed by white, $c_t$ is
   bit $a + L - 1$ of $\Phi^t(N)$, $\Phi(x) = x \oplus (2x \lor 4x)$ the kit's T-function and $N$ the window read with
   $x_{-t}$ as the top bit (Lean, `window_center`), so the windowed rank costs $2^{a+L}$ numbers whatever $t$ is. It is a
   lower bound for $\mathrm{rank}(t, a)$. With $L = a + 2$ it equals $\rho(a)$ at every $t$ from $a + 4$ to $a + 12$ for
   $a = 3$ and $5 \le a \le 12$; for $a = 4$ it is 6 and 5 at $t = 15, 16$. The first $t \ge a + 4$ with windowed rank
   below $\rho(a)$, scanning a full period of $\Phi$ modulo $2^{2a+2}$:

   | $a$ | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
   |---|---:|---:|---:|---:|---:|---:|---:|---:|
   | first $t$ with windowed rank $< \rho(a)$ | 16 | 15 | 31 | 32 | 62 | 64 | 125 | 128 |
   | period of $\Phi$ modulo $2^{2a+2}$ | 32 | 64 | 64 | 256 | 512 | 1024 | 2048 | 4096 |

   So $\mathrm{rank}(t, t - 4) \ge \rho(t - 4)$ for $7 \le t \le 16$ from windows alone, and the first $t$ at which
   the window loses $\rho(a)$ doubles every two cells in this range.

4. **Why fixed windows stop.** $\Phi^{2^j}$ fixes the lowest $j + 1$ bits, so after $2^j$ steps a row white right of
   cell $-2^j + j$ has the center of its cell $-2^j$ (Lean, `center_two_pow`, the kit's `orbit_two_pow_mod` read on
   the center). Every windowed matrix with $a + L \le j + 1$ has rank 1 at $t = 2^j$. A lower bound on the rank that
   holds for every $t$ must therefore use right settings that reach past cell $-t + \log_2 t$, and the windows above,
   which hold the rank only up to the first $t$ of item 3, cannot be extended to every $t$ by periodicity.

5. **The lifting test.** For $3 \le a \le 10$, on the windows of $2a + 4$ cells (a right word of $a + 4$ cells at
   level $a$, of $a + 5$ cells at level $a - 1$): the greedy family of left
   settings at level $a - 1$, taken in index order and kept when independent at every $t$ from $a + 3$ to $a + 11$, has
   $\rho(a - 1)$ members and is the stripe basis $B_{a-1}$ for every such $a$.
   Appending the cell next to the cut, white and black, to each member gives $2\rho(a - 1)$ settings at level $a$ whose
   rank is $\rho(a)$ at every $t$ from $a + 4$ to $a + 12$, and a greedy subfamily of $\rho(a)$ of them is independent at
   all these $t$ at once. In terms of $B_a$ the rule is: lift every member with $x_{-t}$ white by both colors, keep
   the black-$x_{-t}$ member with the new cell white, and, for odd $a = 2k + 3$, drop the lift $0(10)^k 11$; this gives
   $\rho(a) = 2\rho(a - 1) - 2 + [a \text{ even}]$. The stripe basis $B_a$ is independent on these windows at every $t$
   from $a + 3$ to $a + 12$ for $2 \le a \le 10$. No uniform rule failed, so the inductive route is not refuted on this
   range; it is not proved.

6. **The ceiling of the rank method.** One step moves the left setting by one of the three states of the kit's
   automaton 2369 (`AutomatonGroup`: $\Phi$, and $\Phi$ followed by a change of the two lowest bits), chosen by the two
   right cells next to the cut. So every row space of the cut lies in the span of the top bits of all products of the
   three states acting on $a$ bits, for every $t$. That span has dimension

   | $a$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 |
   |---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
   | dimension | 2 | 3 | 5 | 8 | 14 | 25 | 47 | 90 | 176 | 347 | 689 | 1372 | 2738 |

   which is $\rho(a) + \lfloor (a - 1)/2 \rfloor$ for $a \le 13$. So for $a \le 13$ the rank of the cut after $a$
   cells is at most $\rho(a) + \lfloor (a - 1)/2 \rfloor$ at every $t$: the rank method can certify at most about
   $2^a/3$ states at level $a$, never the $2^a$ that $N_{\mathrm{L}}$ has for $a \le t - 2$, $t \le 17$.

## What it means

The conjecture these tables support, open: for every $t$ and every $a \le t - 3$ the rows of $B_a$ are independent, so
$N_{\mathrm{L}}(t, a) \ge \mathrm{rank}(t, a) = \rho(a)$. At $a = t - 3$ it would give every ordered decision diagram
that reads the row from the left a level of width at least $2 + \lfloor 2^{t-3}/3 \rfloor$, for every $t \ge 4$, where
Rules 90 and 150 have width 2; no ordered model has a lower bound for every $t$ yet
([LeftCut](../../Rule30Open/Complexity/LeftCut.md) is exact only to $t = 17$, and the exact distinctness fails from
$t = 18$, [the left cut](../../negative-results/complexity/left-cut.md)). The explicit basis turns the question into
the independence of an explicit family for every $t$; the windowed witness gives $\mathrm{rank}(t, a) \ge \rho(a)$ for
every $t$ from $a + 4$ up to one less than the first $t$ of item 3, which contains $a = t - 4$ for $7 \le t \le 16$, and
item 4 shows that no witness of fixed width reaches every $t$.
A proof has to control cells of the right setting at distance about $\log_2 t$ or more from the cut, through the
products of the automaton's states that the right setting selects; the lifting test found no obstruction to an
induction on $a$, but the induction needs the ranks of the column blocks with the first right cell fixed, which the
computation does not explain.

The kit has no ordered decision diagram, branching program, communication or cut-rank bound for Rule 30 (pinned commit
and main branch); its `QueryComplexity` bounds decision trees, `TFunction`, `TFunctionCycles` and `AutomatonGroup` give
the T-function, its cycles of length a power of two and the three states used in items 3, 4 and 6. The cut ranks for
$t \le 11$ and the formula $2 + (J_{a+1} - 1)/2 = \rho(a)$ for $a \le t - 2$, $t \le 11$, are in
[hidden algebra](../../negative-results/structure/hidden-algebra.md), which also finds the same left ranks for Rule 45
for $a \le 8$: the value $\rho(a)$ belongs to the left-permutive shape of the rule, not to Rule 30 alone. The basis,
the range $t \le 14$, the windows and the ceiling are new. All of this is about $c_t$ as a function of an arbitrary row. It bounds nothing about the center
column of the single black cell, which is one row, so it does not bear on the kit's Problem 3.

## Reproduce

```bash
python -m computations.left_cut_rank --full 12                 # rank(t, a), t <= 12, every a <= t - 1 (minutes, 1 GB)
python -m computations.left_cut_rank --packed 14 --max-a 12     # rank(14, a), a <= 12 (1 min, 2 GB); --packed 13 likewise
python -m computations.left_cut_rank --window 12                # windowed rank, length a + 2, t = a + 4 .. a + 12 (minutes)
python -m computations.left_cut_rank --drops 10                 # first t below rho(a), a = 3 .. 10 (minutes)
python -m computations.left_cut_rank --basis 10                 # the stripe basis on windows of length a + 4 (2 min)
python -m computations.left_cut_rank --lift 10 --extra 2        # the lifting test, a = 3 .. 10 (1 min)
python -m computations.left_cut_rank --coefficients 10          # the stripe monomials' coefficients, t <= 10 (1 min)
python -m computations.left_cut_rank --closure 13               # the ceiling, a <= 13 (20 s)
```

The rank of $B_a$ on the full tables comes from `subset_rank(packed_rows(cut_matrix(cone_table(t), t, a)),
stripe_basis(a))` for $t \le 12$ and from `packed_center` with `reverse_index` for $t = 13, 14$.
[tests/test_left_cut_rank.py](../../tests/test_left_cut_rank.py) checks the windowed values against the truth table
and plain runs, the ranks against the subfunction counts of `cone_screening` and the packed table, the stripe basis at
$t = 6$, the closure dimension against the span over every product of at most 8 states, and the window at $t = 8$.
