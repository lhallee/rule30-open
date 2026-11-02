---
title: Beside 0001, column 1 moves in blocks of four along a graph of 13 edges, and a repeated block forces the ether
category: columns
problems: [1]
status: paper
formalization: partial
---

# Beside 0001, column 1 moves in blocks of four along a graph of 13 edges, and a repeated block forces the ether

Take any rule 30 right half driven by $0001$: columns $j \ge 1$ start from an arbitrary row, and column 0 is
prescribed, $c_0(t) = 1$ exactly when $t \equiv 3 \pmod 4$. Call times $4n, \dots, 4n + 3$ block $n$ and $t \bmod 4$
the phase. Three statements hold for every such half, with no hypothesis on the center and no use of Jen's theorem.
They concern blocks that lie after the start: the block form needs $4n$ at or after the start time, and the table
below, (A) and (B) need the same of $4n$ and of $4(n + 1)$.

- **(A) Blocks and transitions.** On each block, column 1 reads $0^a 1^{4-a}$ for some $a = a_n \in \{0, 1, 2, 3, 4\}$.
  Every pair of consecutive blocks follows an edge of the graph

  $$0 \to \{1, 2, 3, 4\}, \quad 1 \to \{2, 3, 4\}, \quad 2 \to \{1, 2\}, \quad 3 \to \{2, 3\}, \quad 4 \to \{0, 1\}.$$

  The graph is a necessary condition, an upper bound on the sequences column 1 can follow. All 13 edges occur in small
  halves; that every infinite path of the graph is realized by some half is not shown.
- **(B) Forcing.** If $a_n = a_{n+1} = 3$, columns 1 to 4 on block $n$ read $0001$, $0011$, $0110$, $1101$: the kit's
  ether with alignment $(5, 0)$, ending in its B3 column. If $a_n = a_{n+1} = 2$, columns 1 to 3 read $0011$, $0110$,
  $1101$: the ether with alignment $(6, 0)$, ending in B3. In both cases the column after this B3 is white at phase 2.
- **(C) Period-four rigidity.** If column 1 is eventually periodic with period 4, then $a_n$ is eventually constant 3
  or constant 2. The same holds if column 1 is periodic with period 4 only at the white times of the drive, phases 0, 1
  and 2, because the readings at the white phases determine $a_n$.

A consequence for traps. Here a trap is a finite set of windows, the states of columns 1 to $W$ with the phase counted
modulo some multiple $4p$ of 4, that the rule never leaves whatever the cell beyond does, and on which column 1 at the
white phases is a fixed function of the phase. A trap is disjoint from the kit's ether-and-wall family when none of its
windows, at its phase modulo 4, is the $W$-cell cut of a member at any depth. By the repository's computed reach test
at 26 cells ([kit absorption reach](kit-absorption-reach.md)), every node of the game of at most 26 cells reaches such
a cut, so every trap for $0001$ disjoint from the family is wider than 26 cells. On it, column 1 takes one of two forms:

1. $a_n$ is eventually periodic of least period $m \ge 2$, with $m$ dividing $p$, following a closed walk of the graph
   other than the loop at 2 or at 3 repeated. At $m = 2$ the walk is the cycle $(1, 2)$, $(4, 0)$ or $(4, 1)$. The
   trap is at least 27 cells wide.
2. $a_n$ is eventually constant 3 or 2, so the aligned ether is forced on columns 1 to $k$, with $k = 4$ or $k = 3$,
   at every later block. The trap is at least 27 cells wide, so its strip beyond column $k$ is at least 23 cells for
   $k = 4$ and at least 24 for $k = 3$.

No trap for $0001$ disjoint from the family was constructed, and none wider than 26 cells was excluded.

## What the kit and this repository already have

- **The restriction of (A) to $\{1, 2\}$.** The kit's
  [`Rule30PeriodFourSkeleton`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30PeriodFourSkeleton.lean)
  proves, for the true center column eventually equal to $0001$ repeated: `skeleton_0001`, eventually column 1 is
  white at phase 0 and black at phases 2 and 3, so each block reads $0011$ or $0111$ ($a_n \in \{1, 2\}$); and
  `no11_0001`, a black cell of column 1 at phase 1 is followed four steps later by a white one, so no $0111$ block
  follows another ($1 \not\to 1$). That is the graph of (A) restricted to $\{1, 2\}$: $2 \to \{1, 2\}$ and
  $1 \to \{2\}$. The kit reaches it through its rank certificates and masked Jen, for the true center only. Statement
  (A) holds for every driven half, has all five values, and needs neither. The kit's further conclusion, that $a_n$
  eventually stays in $\{1, 2\}$, is not part of (A). `skeleton_0001` also fixes column 2 (black at phase 1, white at
  phase 3) and column 3 (black at phase 0). For $a_n \in \{1, 2\}$ these agree with the column-2 table below wherever it
  fixes a value, and with column 3 of Theorem B at $a = 2$, so that part of the table is in the kit for the true
  center. Since `skeleton_0001`
  eventually excludes $a_n = 3$, for the true center the alignment $(5, 0)$ of (B) is eventually ruled out.
- **Traps of the strip.** The kit's
  [`Rule30EtherTrap`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30EtherTrap.lean)
  defines a trap (`Trap`) as a set of strip nodes, phase modulo 4, closed under every input, on which column 1 at the
  white phases is eventually periodic along every path: the notion masked Jen uses. That is broader than the trap here,
  where column 1 at the white phases is a fixed function of the phase. The two-form argument below still applies to
  each path of a kit trap, since $a_n$ is then eventually periodic along it, and the reach bound applies to the closed
  set. [`Rule30EtherTrapWidth20`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30EtherTrapWidth20.lean)
  proves that no trap of width at most 20 contains a pure-ether node (`pure_ether_not_in_trap_0001`). A pure-ether
  window is the cut of a member whose B3 depth lies beyond the window, so a trap disjoint from the family in the sense
  here contains none; the kit's theorem covers the complementary case of traps that meet the pure ether.
- **The ether and its family.** The kit's
  [`Rule30Ether`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Ether.lean)
  has the ether table ($B_1 = 0011$, $B_2 = 0110$, $B_3 = 1101$, $B_4 = 0101$, $B_5 = 0011$, $c = 0001$, $c = 0001$),
  the alignments $(5, 0)$ and $(6, 0)$ of $0001$ (`aligned_0001_5`, `aligned_0001_6`), the 109 wall states, the trap
  invariant of the family (`trap_invariant`), and the requirement that a wall state carry the $B_4$ value when B3 is
  white (`wall_facts`). Its members put the wall after a B3 column at depth $k = 4, 11, 18, \dots$ for alignment
  $(5, 0)$ and $k = 3, 10, 17, \dots$ for $(6, 0)$. Entry into the family for every finite half is its open conjecture
  `Absorption`. What (B) adds is that the ether up to the first B3, and the white cell after it at phase 2, are forced
  in every driven half as soon as a block value 2 or 3 repeats.
- **The certificate core.** The core seed of [the period-four certificate](period-four-certificate.md) for $0001$ is
  columns 1 to 3 equal to $B_1 B_2 B_3$, the pattern (B) forces when $a_n = a_{n+1} = 2$.
- **The 80-cell background.** Its columns that repeat $0001$ have column 1 beside them reading $00000111$ or
  $01110000$ over 8 steps, the cycle $(4, 1)$ of form 1. The half beside such a column is in the family at no time
  (proved in Lean, [BackgroundHalves](../../Rule30Open/Columns/BackgroundHalves.md)), it has no wall of 1 to 20 cells
  (computed, [background halves](background-halves.md)), and it has the glide symmetry
  $B(j + 10, \varphi) = B(j, \varphi + 1)$.

New here: the paper proofs of (A) for every driven half, of (B), and of (C) for every driven half without Jen, and the
list of the three 2-cycles of the graph. No column-1 block graph appears in the kit, in `findings/`, in
`negative-results/` or in `Rule30Open/`; the kit's results above are its restriction to $\{1, 2\}$ for the true
center.

## Proof

Rule 30 on the right half reads, for $j \ge 1$,

$$c_j(t + 1) = c_{j-1}(t) \oplus \bigl(c_j(t) \lor c_{j+1}(t)\bigr).$$

Two consequences are used throughout, for $j \ge 1$:

- **(K) at a black cell.** If $c_j(t) = 1$, then $c_j(t + 1) = \lnot c_{j-1}(t)$, whatever $c_{j+1}(t)$ is.
- **(W) at a white cell.** If $c_j(t) = 0$, then $c_j(t + 1) = c_{j-1}(t) \oplus c_{j+1}(t)$, so
  $c_{j+1}(t) = c_{j-1}(t) \oplus c_j(t + 1)$.

So a white cell of column $j$ determines the cell to its right from the column on its left and the next value of
column $j$. On block $n$ the drive reads $c_0 = 0, 0, 0, 1$ at phases 0 to 3.

### The block form

Suppose $c_1(t) = 1$ at a time $t$ of block $n$ with phase below 3. Then $c_0(t) = 0$, and (K) gives
$c_1(t + 1) = 1$. Repeating this up to phase 3, column 1 stays black from $t$ to $4n + 3$. So the black cells of
column 1 on a block form a final segment, and the block reads $0^a 1^{4-a}$.

### Column 2 on a block

Applying (W) at column 1 wherever it is white, and the rule at column 2 elsewhere, column 2 on block $n$ is:

| $a_n$ | column 1 | column 2 at phases 0, 1, 2, 3 |
|---|---|---|
| 1 | $0111$ | $1, 1, 0, 1 \oplus c_3(4n + 2)$ |
| 2 | $0011$ | $0110$ |
| 3 | $0001$ | $0011$ |
| 4 | $0000$ | $0, 0, 0, \lnot[a_{n+1} = 0]$ |

For $a = 1$: (W) at $4n$ gives $c_2(4n) = c_0(4n) \oplus c_1(4n + 1) = 1$. Then
$c_2(4n + 1) = c_1(4n) \oplus (1 \lor \cdot) = 1$, $c_2(4n + 2) = c_1(4n + 1) \oplus (1 \lor \cdot) = 0$, and
$c_2(4n + 3) = c_1(4n + 2) \oplus (0 \lor c_3(4n + 2)) = 1 \oplus c_3(4n + 2)$.

For $a = 2$: (W) at $4n$ and $4n + 1$ gives $c_2(4n) = c_1(4n + 1) = 0$ and $c_2(4n + 1) = c_1(4n + 2) = 1$. Then
$c_2(4n + 2) = c_1(4n + 1) \oplus (1 \lor \cdot) = 1$ and $c_2(4n + 3) = c_1(4n + 2) \oplus (1 \lor \cdot) = 0$.

For $a = 3$: (W) at $4n$, $4n + 1$ and $4n + 2$ gives $c_2 = c_1(4n + 1), c_1(4n + 2), c_1(4n + 3) = 0, 0, 1$. Then
$c_2(4n + 3) = c_1(4n + 2) \oplus (1 \lor \cdot) = 1$.

For $a = 4$: (W) at every phase gives $c_2(4n + i) = c_0(4n + i) \oplus c_1(4n + i + 1)$, which is $0, 0, 0$ at phases
0 to 2 and $1 \oplus c_1(4n + 4)$ at phase 3; and $c_1(4n + 4) = 1$ exactly when $a_{n+1} = 0$.

The value $a = 0$ leaves column 2 undetermined; it is not needed.

### Theorem A: the transitions

Write $b = a_{n+1}$. Each exclusion below is a contradiction between the table, (W) and the rule.

- **Only 4 leads to 0.** If $b = 0$, then $c_1(4n + 4) = 1$. The rule at $4n + 3$ gives
  $c_1(4n + 4) = 1 \oplus (c_1(4n + 3) \lor c_2(4n + 3))$, so $c_1(4n + 3) = 0$, which means $a_n = 4$.
- **4 leads to 0 or 1.** If $a_n = 4$ and $b \ge 1$, the table gives $c_2(4n + 3) = 1$, so
  $c_2(4n + 4) = c_1(4n + 3) \oplus (1 \lor \cdot) = 1$. As $c_1(4n + 4) = 0$, (W) gives
  $c_1(4n + 5) = c_0(4n + 4) \oplus c_2(4n + 4) = 1$, so $b \le 1$, hence $b = 1$.
- **1 does not lead to 1.** If $a_n = b = 1$, the table for block $n + 1$ gives $c_2(4n + 4) = 1$. The rule gives
  $c_2(4n + 4) = c_1(4n + 3) \oplus (c_2(4n + 3) \lor c_3(4n + 3)) = 1 \oplus (c_2(4n + 3) \lor c_3(4n + 3))$, so
  $c_2(4n + 3) = c_3(4n + 3) = 0$. From the table for block $n$, $c_2(4n + 3) = 0$ means $c_3(4n + 2) = 1$. Then the
  rule at column 3 gives $c_3(4n + 3) = c_2(4n + 2) \oplus (1 \lor \cdot) = 0 \oplus 1 = 1$, a contradiction.
- **2 does not lead to 3 or 4.** Let $a_n = 2$ and $b \ge 3$, so column 1 is white at $4n + 4$, $4n + 5$, $4n + 6$.
  (W) gives $c_2(4n + 4) = c_0(4n + 4) \oplus c_1(4n + 5) = 0$ and $c_2(4n + 5) = c_0(4n + 5) \oplus c_1(4n + 6) = 0$.
  The rule at $4n + 3$, with $c_1(4n + 3) = 1$ and $c_2(4n + 3) = 0$ from the table, gives
  $c_2(4n + 4) = 1 \oplus c_3(4n + 3)$, so $c_3(4n + 3) = 1$. The rule at $4n + 4$ gives
  $c_2(4n + 5) = c_1(4n + 4) \oplus (c_2(4n + 4) \lor c_3(4n + 4)) = c_3(4n + 4)$, so $c_3(4n + 4) = 0$. But the rule at
  column 3 gives $c_3(4n + 4) = c_2(4n + 3) \oplus (c_3(4n + 3) \lor \cdot) = 0 \oplus 1 = 1$.
- **3 does not lead to 1.** If $a_n = 3$, the table gives $c_2(4n + 3) = 1$, so
  $c_2(4n + 4) = c_1(4n + 3) \oplus (1 \lor \cdot) = 0$, while $b = 1$ needs $c_2(4n + 4) = 1$.
- **3 does not lead to 4.** Let $a_n = 3$. Column 3 on block $n$ is $0110$: (W) at column 2, white at $4n$ and
  $4n + 1$, gives $c_3(4n) = c_1(4n) \oplus c_2(4n + 1) = 0$ and $c_3(4n + 1) = c_1(4n + 1) \oplus c_2(4n + 2) = 1$;
  then $c_3(4n + 2) = c_2(4n + 1) \oplus (1 \lor \cdot) = 1$ and $c_3(4n + 3) = c_2(4n + 2) \oplus (1 \lor \cdot) = 0$.
  Let $b = 4$, so column 1 is white on block $n + 1$. As above, $c_2(4n + 4) = 0$, and (W) at column 1 gives
  $c_2(4n + 5) = c_1(4n + 6) = 0$ and $c_2(4n + 6) = c_1(4n + 7) = 0$. The rule at column 2 gives
  $c_2(4n + 5) = c_1(4n + 4) \oplus (0 \lor c_3(4n + 4)) = c_3(4n + 4)$, so $c_3(4n + 4) = 0$; and the rule at column 3
  gives $c_3(4n + 4) = c_2(4n + 3) \oplus (0 \lor c_4(4n + 3)) = 1 \oplus c_4(4n + 3)$, so $c_4(4n + 3) = 1$. In the same
  way the rule $c_2(4n + 6) = c_1(4n + 5) \oplus (0 \lor c_3(4n + 5))$ gives $c_3(4n + 5) = 0$, and $c_3(4n + 5) = c_2(4n + 4) \oplus (0 \lor c_4(4n + 4)) = c_4(4n + 4)$, so
  $c_4(4n + 4) = 0$. But the rule at column 4 gives
  $c_4(4n + 4) = c_3(4n + 3) \oplus (1 \lor \cdot) = 0 \oplus 1 = 1$.

Removing these leaves $0 \to \{1, 2, 3, 4\}$ (0 does not follow 0, since only 4 leads to 0), $1 \to \{2, 3, 4\}$,
$2 \to \{1, 2\}$, $3 \to \{2, 3\}$ and $4 \to \{0, 1\}$: 13 edges.

### Theorem B: a repeated block forces the ether

Let $a_n = a_{n+1} = 3$. Columns 1 to 3 on block $n$ are $0001$, $0011$, $0110$ by the table and the computation in
the last exclusion. Column 4 follows from (W) at column 3 and the rule: $c_4(4n) = c_2(4n) \oplus c_3(4n + 1) = 1$,
$c_4(4n + 1) = c_3(4n) \oplus (1 \lor \cdot) = 1$, $c_4(4n + 2) = c_3(4n + 1) \oplus (1 \lor \cdot) = 0$, and, as
$c_3(4n + 3) = 0$, $c_4(4n + 3) = c_2(4n + 3) \oplus c_3(4n + 4) = 1 \oplus c_3(4n + 4)$. This last cell needs block
$n + 1$: there $a_{n+1} = 3$ gives $c_2(4n + 4) = c_2(4n + 5) = 0$, and the rule
$c_2(4n + 5) = c_1(4n + 4) \oplus (0 \lor c_3(4n + 4))$ gives $c_3(4n + 4) = 0$. So $c_4(4n + 3) = 1$ and column 4 is
$1101 = B_3$. Column 4 is white at phase 2, so (W) gives $c_5(4n + 2) = c_3(4n + 2) \oplus c_4(4n + 3) = 1 \oplus 1 = 0$.

Let $a_n = a_{n+1} = 2$. Columns 1 and 2 are $0011$ and $0110$. Column 3: $c_3(4n) = c_1(4n) \oplus c_2(4n + 1) = 1$ by
(W), $c_3(4n + 1) = c_2(4n) \oplus (1 \lor \cdot) = 1$, $c_3(4n + 2) = c_2(4n + 1) \oplus (1 \lor \cdot) = 0$, and, as
$c_2(4n + 3) = 0$, $c_3(4n + 3) = c_1(4n + 3) \oplus c_2(4n + 4) = 1 \oplus 0 = 1$, using $c_2(4n + 4) = 0$ from
$a_{n+1} = 2$. So column 3 is $1101 = B_3$, and (W) gives $c_4(4n + 2) = c_2(4n + 2) \oplus c_3(4n + 3) = 0$.

Reading the kit's ether table with column $p$ equal to ether column $j_0 + p \bmod 7$ at phase $t \bmod 4$, these are
the alignments $(5, 0)$ and $(6, 0)$ on columns 1 to 4 and 1 to 3, and the white cell at phase 2 is the $B_4$ value.

### Theorem C: period-four rigidity

If column 1 is eventually periodic with period 4, its blocks are eventually all equal, so $a_n$ is eventually a
constant $a$ with the loop $a \to a$ in the graph. Only 2 and 3 have one.

For the white times: at phases 0, 1, 2 column 1 reads $111$, $011$, $001$, $000$, $000$ for $a = 0, 1, 2, 3, 4$. The
reading $r_n$ fixes $a_n$ except that $000$ leaves $a_n \in \{3, 4\}$, and then the graph decides: $a_n = 4$ exactly
when $a_{n+1} \in \{0, 1\}$, that is when $r_{n+1} \in \{111, 011\}$, and $a_n = 3$ exactly when
$a_{n+1} \in \{2, 3\}$, that is when $r_{n+1} \in \{001, 000\}$. So $a_n$ is a function of $(r_n, r_{n+1})$. If column 1
is periodic with period $4m$ at the white times, $r_n$ is eventually periodic with period $m$, and so is $a_n$. At
$m = 1$, $a_n$ is eventually constant, hence 2 or 3. A half in the family at any depth carries the aligned ether column
$0001$ or $0011$ in column 1, so it has $a_n$ eventually 3 or eventually 2.

### The two forms of a trap

First the width. The windows of a trap, with the phase reduced modulo 4, form a set of nodes of the finite game that no
move leaves, since the drive has period 4. If the trap is disjoint from the family, this set contains no window that
is the cut of a member. The reach test finds that every node of the game of 26 cells, and so of every smaller game,
reaches such a cut; so the trap is wider than 26 cells, whatever column 1 does on it.

A trap fixes column 1 at the white phases as a function of the phase modulo $4p$, so once a half is inside it, $a_n$
is periodic with period $p$, and so with its least period $m$, which divides $p$; it follows a closed walk of the
graph. If that walk is not the loop at 2 or at 3 repeated, the trap has form 1. The cycles of length 2 are the pairs $\{x, y\}$ with $x \to y$ and $y \to x$, $x \ne y$; from the edge
list they are $(1, 2)$, $(4, 0)$ and $(4, 1)$, and the other seven pairs each miss an edge ($1 \not\to 0$,
$2 \not\to 0$, $3 \not\to 0$, $3 \not\to 1$, $2 \not\to 3$, $2 \not\to 4$, $3 \not\to 4$). If the walk is the loop at 3
or at 2, Theorem B applies at every later block, so columns 1 to $k$ carry the aligned ether from then on, with
$k = 4$ or $k = 3$, which is form 2.

## What it means for the route

The kit reduces least period 4 for $0001$ to `Rule30Ether.Absorption`, entry of every finite right half into the
ether-and-wall family, and [the absorption census](absorption-census.md) supports entry for every half of up to 20
cells. This finding describes the left boundary of that question. Every driven half has column 1 moving along the
13-edge graph, and halves in the family are among those where it settles on the loop at 3 or at 2; settling there
forces the ether up to the first B3 column and the white cell after it, the part of the family the kit's wall states
assume. So entry
reduces to two separate questions: that column 1 reaches the loop at 3 or 2, and that, once it has, the strip beyond
B3 reaches a wall state at some depth. A trap that would refute the absorption picture for $0001$ by being disjoint
from the family is wider than 26 cells and has form 1, with column 1 periodic of period at least 8 along a closed
walk such as the cycle $(1, 2)$, $(4, 0)$ or $(4, 1)$, or form 2, with a strip beyond column $k$ wider than $26 - k$
cells.
Each step of (A) to (C) evaluates the rule on a few cells of two consecutive blocks, so the statements suit a Lean
proof by case analysis.

## Where it stops

- **No trap was constructed, and none wider than 26 cells was excluded.** Form 1 at period 8 is realized by the
  80-cell background for the cycle $(4, 1)$, but that background has no wall of 1 to 20 cells ([background halves](background-halves.md)), so
  it gives no trap at those widths. The reach test excludes a trap of either form up to 26 cells. Wider, no trap of
  form 1 or form 2 was found and no argument rules one out; that is a finite question at each width, with exponentially
  many windows, and it was not searched beyond 26 cells.
- **(A) is an upper bound.** All 13 edges occur, but it is not shown that every infinite path of the graph is the
  column 1 of some half.
- **Halves outside every trap.** A half whose $a_n$ is never eventually periodic is in no trap, since a trap fixes
  column 1 at the white phases. Such a half would be a counterexample to `Absorption` that the trap analysis does not
  reach.
- **The reach bound is on width only.** The reach test bounds the trap's width, $W > 26$; it says nothing about where
  along the ether the trap's strip begins.

## Computed, not proved

These come from scratch scripts that are not in the repository.

- If columns 1 to 16 of a half driven by $0001$ are all periodic with period 8 from a common time, then column 1 reads
  $00010001$ or $00110011$ (as in the ether) or $00000111$ or $01110000$ (as in the 80-cell background, cycle
  $(4, 1)$): these are the column-1 readings on the cycles of the period-8 leftward column map beside the drive, and
  the chains with column 1 on the cycles $(1, 2)$ and $(4, 0)$ die out within 10 and 14 levels of the map. The exact
  number of columns needed is not pinned down beyond this. This does not exclude traps of form 1 with the cycles $(1, 2)$ or $(4, 0)$: a trap fixes only
  column 1 at the white phases, and rule 30 is not permutive in its right cell, so columns 0 and 1 do not determine
  column 2.
- A row $y$ with $F^s(y) = S^k y$, for $F$ the rule and $S$ the shift, is a cycle of a deterministic shift register,
  since $F^s$ is affine in its leftmost cell. Within the classes searched ($s = 1$ with $1 \le k \le 16$, and $s \le 4$
  with a register of at most 13 bits, $|k| \le 12, 11, 10, 9$ for $s = 1, 2, 3, 4$), the only such backgrounds with a
  column repeating $0001$ are the ether and the 80-cell background. This says nothing about backgrounds outside those
  classes.

## Check

Statements (A), (B) and (C) are proved in Lean for every half driven by $0001$, with each of the 13 edges shown to occur
from a half supported in cells 1 to 8 ([ColumnOneBlocks](../../Rule30Open/Columns/ColumnOneBlocks.md)); the two forms of
a trap are argued on paper, and the width bound rests on the computed reach test. A check that is not in the repository
runs every right half with support in cells 1 to 10, driven by $0001$ from each of the 4 phases, for 72 steps, and finds
no violation of the block form, of the graph, of the forcing (B) on repeated blocks, or of the white cell after B3 at
phase 2; all 13 edges occur.
