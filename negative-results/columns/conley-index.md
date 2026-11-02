---
title: The Conley index of the windows beside a repeating column excludes no block, and over GF(2) it vanishes for a block that a background repeats
category: columns
problems: [1]
status: negative
kind: refuted
evidence: [computations/conley_index.py, computations/game.py, computations/space_time_periodic.py]
---

# The Conley index of the windows beside a repeating column excludes no block, and over GF(2) it vanishes for a block that a background repeats

**Idea.** Hold a column to a block $w$ of period $P$ and look at the windows beside it as a multivalued map: the cells
the window cannot see are free, so a window has two successors in [the finite game](../../Rule30Open/Columns/FiniteGame.md)
(cells $1, \dots, K$ right of the column) and up to four with two-sided windows (cells $-r, \dots, r$, the center held
to $w$, both edge cells free). If the column of the single cell were eventually $w$, the windows it visits would stay
in the maximal invariant set of this map. The proposal: a nonempty isolated invariant set has a nontrivial Conley index,
so a trivial index at some width would exclude $w$ there, and a limit over widths might become an obstruction.

**Outcome.** The proposed implication is false, and the index excludes nothing.

- **The index of a finite graph.** For a finite directed graph the whole node set is an isolating neighborhood of the
  maximal invariant set with no exit. The windows map to sets of two or four windows, not to acyclic sets, so no
  standard theory fixes the induced map; this entry takes the Conley index over a field to be the shift-equivalence
  class of the adjacency matrix $A$ of the relation (two moves between the same windows count once), which is the
  class of its non-nilpotent part. $A$ is block triangular in an order of the strongly connected components, so the index splits
  over the components that hold a cycle (`index_dimension` in
  [computations/conley_index.py](../../computations/conley_index.py) gives its dimension over GF(2), the rank of a
  high power of $A$).
- **Over the rationals the index is the existence of a cycle.** $\operatorname{tr} A^k$ counts the closed walks of length
  $k$, so a nonnegative integer matrix is nilpotent exactly when its graph has no cycle (an argument). Every one of the
  71 primitive blocks of period at most 8 has a cycle in the game at 6, 8 and 10 cells and in the two-sided graph at
  radii 3, 4, 5 and 6, so the index over $\mathbb{Q}$ is nontrivial in every case and excludes no block. The game
  excludes 4 of the 71 at these widths ($0$, $1$, $00000011$, $01111111$), through the column left of the repeating
  one rather than through an empty invariant set, and their index stays nontrivial (dimension over GF(2) 7, 5, 8 to
  104 and 56 to 160). The index is weaker than the game.
- **Over GF(2) a trivial index does not mean an empty invariant set.** A component with cycles can have a nilpotent
  matrix over GF(2), when it has an even number of closed walks of every length: the three windows of the game of $0$
  at 3 cells, with two cycles of length 2 through one window, are an example. Such components occur
  for 13, 19 and 22 of the 71 blocks in the game at 6, 8 and 10 cells, and for 1, 17, 25 and 18 with two-sided windows
  at radii 3 to 6. For $001111$ at 8 cells every one of its three components (273, 7 and 11 windows) is of this kind,
  so the whole index is trivial, and yet a background of period 6, a configuration of the whole line, has a column that
  repeats $001111$ forever ([space-time backgrounds](../../findings/columns/space-time-backgrounds.md)); its windows
  right of that column make a closed walk of this graph. So a trivial index excludes a block that Rule 30 does repeat
  on the line. At 4 to 7, 9 and 10 cells the index of $001111$ is nontrivial again (dimension 6, 36, 42, 42, 102 and
  120), so it is not monotone in the width either. $001111$ at 8 cells is the only case of a trivial index in the
  survey.
- **The counterexample needs the relation.** With the transfer matrix in place of $A$, which counts the two values of
  a free cell that reach the same window twice, no block of period at most 8 has a trivial index over GF(2) in the
  game at 4, 6, 8 or 10 cells, $001111$ at 8 cells included (`--transfer`). The statements over $\mathbb{Q}$ are the
  same for both matrices, since they depend only on which entries are positive.

**Why.** Conley's theorem goes one way: a nontrivial index forces a nonempty invariant set (Ważewski's principle). A
nonempty invariant set may have a trivial index, so "trivial index, hence no repeating column" is not a theorem, and
$001111$ is a counterexample for the index of the relation. The direction that is a theorem only says that plays survive forever, which the
backgrounds already show. Like every invariant of the windows beside the column, the index is also passed by the
spatially periodic backgrounds, which no invariant of this kind can exclude
([sheaf sections](sheaf-sections.md), item 5; [ring orbits](ring-orbits.md)); the hypothesis that the row has a
leftmost black cell, which the game uses through [the adjacent-column theorem](../../Rule30Open/Columns/AdjacentColumns.md),
is invisible to it.

**What it means.** The Conley index of the window graphs gives back, over $\mathbb{Q}$, the existence of a cycle, which
is weaker than the finite game, and over GF(2) a parity of closed walks that is not an obstruction. A topological
index of the window dynamics would need an input that the backgrounds fail, as every route through finite windows does.

**Reproduce.** `python -m computations.conley_index --max-period 8 --widths 6,8,10 --radii 3,4,5,6` (about 140 s), and
`python -m computations.conley_index --max-period 8 --widths 4,6,8,10 --radii "" --transfer` (about 90 s).
[tests/test_conley_index.py](../../tests/test_conley_index.py) checks the elimination against Python integers, the
splitting over components against a power of the whole matrix, the nilpotent component of $0$ and the trivial index of
$001111$ at 8 cells against exact integer powers, the transfer matrix against a power of the whole matrix, and the
two-sided moves cell by cell.
