---
title: Behind a left diagonal that is white from some time on, flipping one cell complements the next diagonal, so both candidate classes are realized and the settled skeletons of the rows white left of a black cell form a binary tree
category: diagonals
problems: [2]
status: proved
lean: Rule30Open.Diagonals.SkeletonTree
headline: [flip_white_complements, Ld_reanchor, branch_realized, branch_not_shift, walk_phase_transfer, shifted_walk_close]
kit: new
kit_modules: [Rule30FiniteDiagonals, Rule30FiniteConfigs, Rule30LightCone]
evidence: [computations/skeleton_tree.py, computations/front_walker.py]
---

# Behind a left diagonal that is white from some time on, flipping one cell complements the next diagonal, so both candidate classes are realized and the settled skeletons of the rows white left of a black cell form a binary tree

[DrivenSkeleton](DrivenSkeleton.md) proves that every row white left of a black cell settles to the single cell's
pairs of left diagonals up to a time shift, as long as each white diagonal is followed by a doubling period. At the
single cell's white diagonal 53,207 there is no doubling, and its step leaves two candidate classes for diagonal
53,208: the single cell's, and its complement. This module shows that the second one is realized, by a row obtained
from the single cell's in one flip, and that the same holds behind every white diagonal of every such row.

## Statement

Let $b(i, t) = \mathrm{cell}_t(lo - t + i)$ be the left diagonals of a row $x$ white left of $lo$ (the kit's
`Rule30FiniteDiagonals.Ld`), and write $D_i$ for $b(i, \cdot)$.

- `flip_white_complements`: if $D_w$ is white at every time, the row $x$ with the cell $lo + w + 1$ flipped
  (`flipCell`) is white left of $lo$, has the same diagonals $D_0, \dots, D_w$, and has $\lnot D_{w+1}(t)$ as its
  diagonal $w + 1$ at every time $t$.
- `Ld_reanchor`: the row $\mathrm{evol}^s(x)$, read from the cell $lo - s$, has diagonal $i$ at time $t$ equal to
  $D_i(s + t)$. It is white left of $lo - s$ (`evol_white_left`, from the kit's
  `Rule30FiniteConfigs.evol_eq_false_of_lt`).
- `branch_realized`: if $x$ is white left of a black cell $lo$ and $D_w$ is white from time $s$ on, there is a row $y$
  white left of a black cell $lo'$ with $D^y_i(t) = D_i(t + s)$ for every $i \le w$ and every $t$, and
  $D^y_{w+1}(t) = \lnot D_{w+1}(t + s)$ for every $t$.
- `branch_not_shift`: if $g(t) = \lnot f(t + s)$ for every $t$, and no time shift carries $f$ to its complement from
  some time on (for every $d$ and $U$ some $u \ge U$ has $f(u + d) = f(u)$), then $g$ is not $f$ read with any time
  shift $h$ from any time $T$ on.
- `walk_phase_transfer`, `walk_advance_close`: let `IsFrontStep f t t'` say that $t'$ is one past the first black cell
  of $f$ at or after $t$, or $t' = t$ if $f$ is white from $t$ on (the step of the least front walk of
  [FrontWalker](FrontWalker.md)). If every diagonal repeats with period $P$ from $T$, two front walks $u, v$ along the
  same diagonals with $T \le u_0 \le v_0 \le u_0 + P$ satisfy $u_j \le v_j \le u_j + P$ at every depth $j$, so their
  advances over any stretch of depths differ by at most $P$.
- `shifted_walk_close`: if the diagonals $g$ are the diagonals $f$ read $h$ steps later from $T$ on, a front walk $u$
  along $g$ from $u_0 \ge T$ is, shifted by $h$, a front walk along $f$ (`IsFrontStep.shift`), and so stays within
  $P$ of every front walk $v$ along $f$ with $u_0 + h \le v_0 \le u_0 + h + P$.

## Argument

1. **Light cone.** Diagonal $i$ of a row white left of $lo$ depends only on the cells $lo, \dots, lo + i$
   (`Ld_agree_of_prefix` of [PrefixWalk](PrefixWalk.md)), so the flip at $lo + w + 1$ changes no diagonal $i \le w$.
2. **The flip persists.** At time 0 diagonal $w + 1$ is the flipped cell. If $w \ge 1$, the step `Ld_step` with
   $i = w - 1$ reads $D_{w+1}(t + 1) = D_{w-1}(t) \oplus (D_w(t) \lor D_{w+1}(t)) = D_{w-1}(t) \oplus D_{w+1}(t)$,
   since $D_w$ is white; $D_{w-1}$ is the same in both rows, so the two values of $D_{w+1}$ differ at every time by
   induction. For $w = 0$, `Ld_one_succ` gives $D_1(t + 1) = D_0(t) \lor D_1(t) = D_1(t)$.
3. **Re-anchoring.** $\mathrm{evol}^t(\mathrm{evol}^s x) = \mathrm{evol}^{s + t} x$ (`evol_evol`), and cell
   $lo - s - t + i$ at time $t$ of the new row is cell $lo - (s + t) + i$ at time $s + t$ of $x$.
4. **Realization** (`branch_realized`). Take the row at time $s$, anchored at $lo - s$: its diagonal $w$ is white from
   time 0 by step 3, and its cell $lo - s$ is $D_0(s)$, black because $D_0$ is black at every time
   (`DrivenSkeleton.base_pair`). Flip its cell $lo - s + w + 1$ and apply steps 1 and 2.
5. **Not a shift** (`branch_not_shift`). If $g(t) = f(t + h)$ for $t \ge T$, then $f(t + h) = \lnot f(t + s)$ for
   $t \ge T$, so $f$ is carried to its complement by the shift $|h - s|$ from $T + \min(h, s)$ on.
6. **Phase transfer.** The front step is monotone in its start (`IsFrontStep.mono`: the first black cell after a
   later time is not earlier) and, on a sequence of period $P$ from $T$, commutes with adding $P$
   (`IsFrontStep.add_period`). So $u_j \le v_j \le u_j + P$ passes from depth $j$ to $j + 1$: $u_{j+1} \le v_{j+1}$
   by monotonicity, and $v_{j+1}$ is at most the step from $u_j + P$, which is $u_{j+1} + P$.

**The tree (paper, from the Lean lemmas).** Call the eventual words of a row its *skeleton*. By DrivenSkeleton's
`skeleton_step`, at each diagonal $w$ that is white from some time on, the next diagonal of any second row whose pair
$(D_{w-1}, D_w)$ is a time shift of the first row's is that diagonal shifted or its complement shifted; by
`skeleton_step_of_flip` the two coincide when the period doubles (the weight of $D_{w-1}$ per period is odd), and
otherwise they are different classes unless the complement of $D_{w+1}$ is one of its rotations. `branch_realized`
realizes the complement by a row white left of a black cell whose diagonals $0, \dots, w$ are the first row's
shifted, and whose diagonal $w$ is white from time 0. Its later diagonals follow the pair map from that pair
(`shift_of_black` along the non-white diagonals), so at its next white diagonal $w'$ the same argument applies to it.
By induction on the white diagonals, every path of the pair map to a finite depth that chooses one of the two classes
at each white diagonal without a doubling is, to that depth, the skeleton of some row white left of a black cell, and
every such row's skeleton is one of these paths. So the skeletons form a binary tree that branches at the white
diagonals with even weight before them (the realizing row changes with the depth; that a single row realizes an
infinite path is not shown here).

**The instance at 53,207 (by computation).** The single cell's diagonal 53,207 is white from time 107,310 on: the
least front walk reaches it at $w_{53207} = 107{,}310$ and reads a whole period of white cells there, and
`pair_repeats_of_walk` of FrontWalker makes the pair $(D_{53206}, D_{53207})$ repeat from that time, so one white
period is white forever. That reading is the computation of [FrontWalker](FrontWalker.md) (`front_walker`, the walk to
depth 200,000 on 300,600 steps; `skeleton_tree` reproduces its walk on the settled words, $w_{200{,}000} = 402{,}228$).
`branch_realized` with $s = 107{,}310$ then gives a row, the single cell's row at time 107,310 with its cell
$-107{,}310 + 53{,}208 = -54{,}102$ flipped, whose diagonals up to 53,207 are the single cell's read 107,310 steps
later and whose diagonal 53,208 is the complement. The single cell's $D_{53206}$ has weight 6 of 16, so $D_{53208}$
has period 16, and its complement is not one of its 16 rotations (`skeleton_tree` checks it): no time shift carries
$D_{53208}$ to its complement, and `branch_not_shift` says the new row's diagonal 53,208 is not the single cell's
under any time shift. So the second class that [DrivenSkeleton](DrivenSkeleton.md) leaves open at depth 53,208 is
realized. The Lean statements are general and take the eventually white diagonal as a hypothesis; only this instance
rests on the computation.

## What it means

The tree is followed to depth 250,000 in [the skeleton tree](../../findings/diagonals/skeleton-tree.md): 8 branches,
which differ in their white diagonals, their doublings, their largest antiphase alternation and their walks. A
statement about every row white left of a black cell, or every driven left half, is a statement about every branch of
the tree from depth 53,208 on, not about the single cell's skeleton alone. The phase transfer makes the front walk a
property of the branch: two rows on the same branch, or one branch walked from two phases, differ in their walk's
advance by at most one period over any stretch of depths.

## The kit

The kit proves that the left diagonals of every row with a left edge settle with period $2^j$
(`Rule30FiniteDiagonals.Ld_uniform_period`) and the light cone (`Rule30LightCone.evol_window`); its main branch has the
accumulation behind a white diagonal for the single cell (`Rule30LeftReset.D_white_shift`, `white_period_iff`) and the
period or anti-period dichotomy (`Rule30LeftAntiPeriod`). It has no comparison of the skeletons of two rows, no flip
that realizes the complemented class, and no statement on the phase of the front walk (`Rule30FrontLaw.frontBound` is
the walk of the single cell). The kit's evolution semigroup `Rule30WhiteEnd.evol_add` is the statement of
`evol_evol`, reproved here so as not to import that module.
