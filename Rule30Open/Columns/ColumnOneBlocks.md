---
title: Beside 0001, column 1 moves in blocks of four along a graph of exactly 13 edges, and a repeated block forces the ether
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ColumnOneBlocks
headline: [column_one_blocks, column_one_white_period_four, column_one_period_four, column_one_period_four_ether, drv_column_one_blocks, drv_column_one_white_period_four, cob_edges_realized, cob_loops, cob_two_cycles]
kit: new
kit_modules: [Rule30Ether, Rule30StripCertificates]
---

# Beside 0001, column 1 moves in blocks of four along a graph of exactly 13 edges, and a repeated block forces the ether

This module proves statements (A), (B) and (C) of the finding
[column 1 beside 0001 moves in blocks of four](../../findings/columns/column-one-blocks.md) for every rule 30 right
half driven by $0001$, finite or not, with no hypothesis on the center and no use of Jen's theorem. It also proves
that each of the 13 edges occurs, so the graph is exactly the set of one-step transitions.

## Statement

Let $F(t, p)$, $p \ge 0$, follow rule 30 on the columns $p \ge 1$ (the kit's `IsR30 F`) with column 0 reading $0001$
from a time $T$ on: $F(t, 0) = 1$ exactly when $t \equiv 3 \pmod 4$, for $t \ge T$ (`wordAt w0001 t`). The kit's
driven half `drv (wordAt w0001) x` is such an $F$ with $T = 0$, for every right half $x$. Block $n$ is the times
$4n, \dots, 4n + 3$; `colOneWord F (4n)` is column 1 on it and `colOneVal F (4n)` $= a_n$ the number of its white
cells. The graph `cobEdges` is

$$0 \to \{1, 2, 3, 4\}, \quad 1 \to \{2, 3, 4\}, \quad 2 \to \{1, 2\}, \quad 3 \to \{2, 3\}, \quad 4 \to \{0, 1\}.$$

- `column_one_blocks`: for every block with $T \le 4n$,
  - **(A)** column 1 on block $n$ reads $0^{a_n} 1^{4 - a_n}$ (`cobWord`), and $(a_n, a_{n+1})$ is an edge of the graph;
  - **(B)** if $a_n = a_{n+1} = 3$, then $F(4n + \varphi, p) = \mathrm{ether}(5 + p, 4n + \varphi)$ for $p = 1, \dots, 4$
    and $\varphi < 4$ (columns $0001, 0011, 0110, 1101$, the kit's ether with alignment $(5, 0)$, ending in B3), and
    $F(4n + 2, 5) = 0$; if $a_n = a_{n+1} = 2$, then $F(4n + \varphi, p) = \mathrm{ether}(6 + p, 4n + \varphi)$ for
    $p = 1, 2, 3$ (columns $0011, 0110, 1101$, alignment $(6, 0)$), and $F(4n + 2, 4) = 0$.
- **(C)** `column_one_white_period_four`: if $F(t + 4, 1) = F(t, 1)$ for every $t \ge N$ with $t \bmod 4 < 3$ (the
  white phases of the drive), then $a_n$ is eventually constant 3 or eventually constant 2.
  `column_one_period_four` is the same under period 4 at all times, and `column_one_period_four_ether` adds that the
  aligned ether of (B) is then forced at every later block.
- `drv_column_one_blocks`, `drv_column_one_white_period_four`: (A), (B) and (C) for `drv (wordAt w0001) x`, every
  $x : \mathbb{N} \to \mathrm{Bool}$ and every $n$.
- `cob_edges_realized`: for each of the 13 edges there is an $x$ supported in cells 1 to 8 whose driven half has
  $(a_0, a_1)$ equal to that edge.
- `cob_loops`: $(a, a)$ is an edge exactly when $a \in \{2, 3\}$. `cob_two_cycles`: the pairs $x < y$ with
  $x \to y$ and $y \to x$ are $(0, 4)$, $(1, 2)$ and $(1, 4)$. `cobEdges_length`, `cobEdges_nodup`: 13 distinct edges.

## Argument

1. **A light cone of 8 cells.** Column 1 on blocks $n$ and $n + 1$ (times $4n$ to $4n + 7$) and columns 1 to 5 on
   block $n$ depend only on columns 1 to 8 at time $4n$ and on the drive, which reads $0001\,000$ at times $4n$ to
   $4n + 6$. `cobRows r k` computes columns 1 to $8 - k$ at time $4n + k$ from the row $r$ of columns 1 to 8, one
   step at a time with the kit's list form of the rule (`lin3`), and `cob_rows` proves that it is the evolution,
   through the kit's `rowOf_succ`. `cob_cell` reads a single cell of the cone.
2. **The check.** `cobCheck r` tests, on the cone of $r$, the block form of block $n$, the edge
   $(a_n, a_{n+1})$, and the ether and the white cell of (B) when $a_n = a_{n+1} = 3$ or $= 2$. `cobCheck_all` proves
   it for all $2^8 = 256$ rows by kernel evaluation. Since the row at time $4n$ is arbitrary, this gives (A) and (B)
   for every $F$ (`col_one_block_form`, `col_one_block_edge`, `col_one_force_three`, `col_one_force_two`), and
   `column_one_blocks` restates them at the times $4n \ge T$.
   This is the case analysis of the finding's paper proof, done by the kernel on the 8 cells it reads.
3. **Period four.** At phases 0, 1, 2 the block $0^a 1^{4-a}$ reads $111, 011, 001, 000, 000$ for
   $a = 0, \dots, 4$. `cob_white_rigid` checks over the 13 edges that equal readings on an edge force $a_n = a_{n+1}$
   and $a_n \in \{2, 3\}$: the only edge between the two values with reading $000$ is the loop at 3, since
   $3 \not\to 4$ and $4 \not\to 3, 4$. So under period 4 at the white phases, from the block where both the drive and
   the periodicity hold, $a_{n+1} = a_n \in \{2, 3\}$ at every block (`cob_step`), and induction gives a constant value
   (`column_one_white_period_four`).
4. **Every edge occurs.** `cobWitness e` is the first row of 8 cells in `cobAllRows 8` whose cone follows the edge
   $e$; `cobWitness_ok` checks by kernel evaluation that one exists for each edge, and `cob_edges_realized` turns it
   into a driven half with the row at time 0.

## In Lean

The module builds in about 5 seconds. The kernel checks are `decide +kernel` over 256 rows (`cobCheck_all`) and over
the 13 edges (`cobWitness_ok`, `cob_white_rigid`). No `sorry`, no `native_decide`, and no axioms beyond `propext` and
`Quot.sound`.

## What it does not say

- (A) is the set of one-step transitions; `cob_edges_realized` shows each edge for one step from a finite half. It is
  not shown that every infinite path of the graph is column 1 of some half.
- The trap consequences of the finding (the two forms of a trap disjoint from the family, and the width bound from the
  computed reach test) are not formalized here: the reach bound is a computation, and the notion of trap there is the
  finding's, not the kit's `Rule30EtherTrap.Trap`.
- (C) needs period 4 itself. A column 1 eventually periodic with a longer period follows a closed walk of the graph,
  and nothing here excludes the 2-cycles $(1, 2)$, $(4, 0)$, $(4, 1)$ or longer walks.
- Nothing here bears on whether $0001$ is the tail of the center column: that needs entry into the ether-and-wall
  family, the kit's open `Rule30Ether.Absorption`.

## Relation to the kit

The kit's [`Rule30PeriodFourSkeleton`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30PeriodFourSkeleton.lean)
proves, for the true center column eventually $0001$ and through masked Jen and rank certificates, that column 1 is
eventually in blocks $0011$ or $0111$ with no $0111$ after $0111$ (`skeleton_0001`, `no11_0001`): the graph restricted
to $\{1, 2\}$. This module proves the whole graph for every driven half, with all five values, and that each edge
occurs. The ether, its alignments $(5, 0)$ and $(6, 0)$ (`aligned_0001_5`, `aligned_0001_6`), `IsR30`, `rowOf` and
`drv` are the kit's
[`Rule30Ether`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Ether.lean);
`lin3` and `seg` are from `Rule30StripCertificates`. No column-1 block graph appears in the pinned kit or in the kit's
main branch.
