---
title: The sheaf of patches beside a repeating column gives back the finite game, and its cohomology is weaker than the limit windows one cell narrower
category: columns
problems: [1]
status: negative
kind: dead-end
evidence: [computations/sheaf_sections.py, computations/limit_windows.py, computations/game.py]
---

# The sheaf of patches beside a repeating column gives back the finite game, and its cohomology is weaker than the limit windows one cell narrower

**Question.** Eventual periodicity of the center column can be posed as a problem of global sections: the patches of
space-time right of a column that repeats a block form a presheaf over the half-plane, or over the cylinder of the
time circle $\mathbb{Z}/P$ times the half-line, and the column condition is a sub-presheaf. Does its limit over windows,
its Cech cohomology, or the functorial view of the column as a natural transformation say more than the
[finite game](../../Rule30Open/Columns/FiniteGame.md) and the [limit windows](../../findings/columns/limit-windows.md)?

**Outcome.** No. The limit of the presheaf over windows is the family of limit-window tests, its sections over the
cylinder are the cycles of the game, and the game's test is a property of the traces of plays. Cohomology needs the
presheaf linearized, and the linearized limit is coarser: its test at $K$ cells excludes no block that the exact limit
at $K - 1$ cells leaves (a lemma, below), and at widths 6 to 12 it excludes fewer blocks (29 against 60 at 12 cells, to
period 14), none new. Every invariant of the presheaf also holds on the spatially periodic backgrounds, which defeat the
game for $01$, $0001$ and seven other blocks, so no invariant of it excludes those. This is where the route stops.

## The presheaf

Let column $k$ repeat a block $w$ of period $P$. For a finite set $U$ of cells $(t, j)$ with $j \ge k + 1$, a section
over $U$ is an assignment of 0s and 1s to $U$ that obeys $x_{t+1}(j) = x_t(j - 1) \oplus (x_t(j) \lor x_t(j + 1))$ at
every cell of $U$ whose three parents lie in $U$, with column $k$ read from $w$. Restriction is restriction of
functions. Each constraint involves four cells, so the presheaf glues over any cover in which each constraint lies in
one member; its Cech $H^0$ is the set of sections, and higher Cech cohomology needs coefficients in a group, which a presheaf of
sets does not carry.

1. **Slabs are plays.** Over the slab of times $t - m, \dots, t$ and columns $k + 1, \dots, k + K + 1$, a section is a
   play of length $m$ of the game of width $K$: column $k + K + 1$ has its right parent outside the slab, so it is the
   free cell. Restriction to the top row is the play's last window.
2. **The limit over time is the limit windows.** The windows at phase $i$ that extend over slabs of every depth are the
   sets $S_i(K)$ of `limit_windows.limit_sets` (finite sets, so the decreasing images stop at a finite depth).
3. **The limit over widths adds nothing.** Call a section over all cells $j \ge k + 1$, $t' \le t$ an eternal right
   half. By König's lemma, the windows of $j$ cells of eternal halves are $\bigcap_{K \ge j} \mathrm{prefix}_j\, S_i(K)$,
   a decreasing intersection of finite sets. So cell $k + 1$ is constant at phase $i$ on every eternal half if and only
   if it is constant on $S_i(K)$ for some $K$: the global-section test at infinite width is the union of the
   limit-window tests.
4. **The cylinder is the game.** A section over $\mathbb{Z}/(mP)$ times the slab is a closed walk of length $mP$ of the
   game, and the windows on such walks are the nodes of the components that hold a play. The game asks the column left
   of $k$ to be a function of the phase on each of them, which is the same as asking that every infinite play read an
   eventually $P$-periodic left column: a component that shows both values at a phase has a play visiting both
   infinitely often. That is a property of the language of traces, so it is invariant under bisimulation, and the
   bisimulation quotient of the driven right half (its final coalgebra) is the causal map $\Psi_w$ of the strobed form
   in [the reformulations](../dynamics/reformulations.md), the kit's `CoupledHalves.problem1_iff_coupled_halves`.
5. **What the presheaf cannot see.** The hypothesis that the row has a leftmost 1 is not a condition on finite patches
   right of the column; the game uses it only through [the adjacent-column theorem](../../Rule30Open/Columns/AdjacentColumns.md).
   A spatially periodic background is a section over the cylinder of the whole half-line, so any test that every
   global section must pass is passed by it. For $01$ (the ether), $0001$, $00101$, $000101$, $001011$, $0000011$,
   $0010011$, $0011101$ and $0011111$ such a background has a left column that does not repeat with the block
   ([ring orbits](ring-orbits.md)), so no invariant of this presheaf, at any width, excludes these blocks.

## The linearized limit

Cech cohomology with coefficients needs an abelian group, so each set of sections is replaced by the GF(2) vector
space on it, as in the cohomological obstruction of Abramsky, Mansfield and Barbosa (*The cohomology of non-locality
and contextuality*, QPL 2011). One step beside a column value becomes the linear relation
$\{(\mathrm{tail}(a), \mathrm{head}(a)) : a \in \mathrm{GF}(2)^{\text{moves}}\}$, which is the cover by
slabs of one step that meet in rows; the obstruction of a window $y$ over
$m$ steps vanishes when $e_y$ lies in the image $L^{(m)}$ of the whole space under $m$ such steps, and $L_i$ is the
limit at phase $i$. Call $T_i$ the windows whose obstruction vanishes at every depth.

- **Its structure** (`linear_step`). A functional $\varphi$ annihilates the image of a subspace $U$ exactly when
  $\varphi(y) = \psi(x)$ on every move $x \to y$ for some $\psi$ annihilating $U$. So the annihilator of $L_i$ is spanned
  by the indicators of disjoint sets of windows, found by union-find over the connected components of each step's graph
  of moves. The linearization keeps only these components: the direction of a move and which of two windows a move
  reaches is lost. The same holds over any field, so GF(2) is not a special choice. `dense_linear_limit` computes $L_i$
  by Gaussian elimination instead, and the two agree (`tests/test_sheaf_sections.py`).
- **The components.** The windows after a step that lie in one component share their first $K - 1$ cells: the cell
  $k + K$ after the step is the only one that the free cell reaches. So a component's windows after the step are $y'0$
  and $y'1$, or one of them.
- **Two tests.** The pointwise test asks cell $k + 1$ to be constant on $T_i$ at every 0 of the block (`linear_good`),
  the strongest test a vanishing obstruction gives. The functional test asks cell $k + 1$ plus a constant to annihilate
  $L_i$ (`functional_good`), so that every linear section reads one value. Both are sound, since $S_i(K) \subseteq T_i$.

**Lemma** (one cell short). For every block, width $K \ge 2$ and phase $i$, and every window $y'$ of $S_i(K - 1)$, the
window $y'1$ is in $T_i(K)$, and so is $y'0$ when the last cell of $y'$ is 0. Hence if the pointwise test at $K$ cells
excludes a block, so does the exact limit at $K - 1$ cells.

*Proof.* If $e_x \in L^{(m)}$ and $y$ is joined to $x$ by a path of moves taken in either direction, the alternating sum
of the moves along the path has tail $e_x$ and head $e_y$, so $e_y \in L^{(m+1)}$. Induct on $m$, with $T^{(0)}$ all
windows. Let $y'$ be reached at $K - 1$ cells from $x' \in S^{(m)}(K - 1)$ with the free cell $u$; at $K$ cells the
window $x'u$ has after-windows with first cells $y'$. If the last cell of $x'$ is 1, the first $K - 1$ cells after the
step do not depend on cell $k + K$, so $x'0$ and $x'1$ both lead to $y'$, $x'0$ reaches both $y'0$ and $y'1$, and $x'1$,
which is in $T^{(m)}$ by induction, lies in their component. If the last cell of $x'$ is 0, both $x'0$ and $x'1$ are in
$T^{(m)}$ by induction. For $u = 0$, $x'0$ reaches $y'0$ and $y'1$. For $u = 1$, $x'1$ reaches $y'1$; the last cell of
$y'$ is then 0 only if the next-to-last cell of $x'$ is 1, and then $x'$ with its last cell set to 1, followed by 0, also
leads to $y'$ and reaches both $y'0$ and $y'1$, so $y'0$ is in the component of $x'1$. In each case the windows the lemma names are joined to a window of
$T^{(m)}$. Cell $k + 1$ of $y'1$ is that of $y'$, so constancy on $T_i(K)$ gives constancy on $S_i(K - 1)$. $\square$

The lemma and items 1 to 5 of the presheaf are proved by hand, not in Lean. The lemma concerns the cover by
one-step slabs and says nothing about a cover by deeper slabs. `one_cell_short` checks the lemma's statement
directly: it holds for all 747 primitive blocks of period at most 12 at every width from 2 to 10 (`--lemma`).

**Counts** (`survey`): primitive blocks excluded, by width $K$ and period, by the functional and pointwise linear tests
at $K$, the exact limit at $K - 1$ and at $K$, and the game at $K$. Every block passes the chain
functional $\Rightarrow$ pointwise $\Rightarrow$ exact at $K - 1$ $\Rightarrow$ exact at $K$ $\Rightarrow$ game.

| Width $K$ | Functional at $K$ | Pointwise at $K$ | Exact at $K - 1$ | Exact at $K$ | Game at $K$ |
|---:|---:|---:|---:|---:|---:|
| 6 | 1 | 1 | 32 | 42 | 58 |
| 8 | 25 | 27 | 42 | 48 | 69 |
| 10 | 29 | 29 | 53 | 58 | 72 |
| 12 | 29 | 29 | 60 | 63 | 74 |

These are totals over the 2,538 primitive blocks of period 1 to 14. At 12 cells, by period from 8 to 14, the pointwise
test excludes 1, 0, 1, 2, 4, 8 and 12 blocks, the exact limit at 11 cells 1, 0, 3, 6, 7, 18 and 24, and the game 3, 0,
3, 7, 9, 21 and 29.

The pointwise test excludes two blocks more than the functional one at 8 cells and the same blocks at 6, 10 and 12. At
6 cells the linear tests exclude only the constant block $1$. At 10 and 12 cells they exclude the same 29 blocks: $1$,
$01111111$ and 27 blocks with a run of at least nine 1s, every one of which the kit or
[WallSets](../../Rule30Open/Columns/WallSets.md) already excludes in Lean; no block with only short black runs and a
long white run, the families of [the limit windows](../../findings/columns/limit-windows.md), passes. The linear limit
is also much larger than the exact one: at 12 cells, 626 to 641 of 4,096 windows are in the exact limit for $0001$
against 1,095 to 1,220 with a vanishing obstruction, and 296 to 365 against 677 to 1,053 for $00000011$ (`--sizes`).

**What it means.** Gluing local patches into global sections is exactly what the finite game and the limit windows
already compute: the limit over windows and the sections over the cylinder are those two objects, and the step where
the categorical view stops is item 5, the same place as every right-side method, since a background is a global
section. Cohomology, the one invariant the categorical view adds, is a linear relaxation of the same limit that merges
the two windows a free cell can produce, and so loses at least one cell of width. The functorial view adds nothing
either: the map from rows to their center column commutes with the rule and the shift ($\Phi \circ F = \sigma \circ
\Phi$) for every cellular automaton, Rules 90, 150 and 210 among them, whose center columns from one cell are
eventually constant (the kit), and by the kit's `Realization.problem1_iff_realization` every sequence is the center
column of some row, so naturality constrains no periodic column; only the finiteness of the row, through Jen's
argument, does.

## Reproduce

```bash
python -m computations.sheaf_sections --survey 14 --widths 6,8,10,12   # the counts, about 10 min
python -m computations.sheaf_sections --lemma 12 --widths 2,3,4,5,6,7,8,9,10   # the lemma, a few minutes
python -m computations.sheaf_sections --sizes 01,0001,001,00000011,01111111 --widths 6,8,10,12
```

[computations/sheaf_sections.py](../../computations/sheaf_sections.py) builds the linearized limit by union-find
(`linear_limit`) and by elimination (`dense_linear_limit`), and checks the lemma (`one_cell_short`); its test compares
the two constructions, the exact limit with plays enumerated cell by cell, the shape of the components, the chain of
tests on every block of period at most 8 at 6 cells, and the lemma at small widths.
