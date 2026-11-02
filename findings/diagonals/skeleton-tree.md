---
title: To depth 250,000 the settled skeletons of the rows white left of a black cell form a tree of 8 branches that leave the single cell's at 53,207; no branch doubles its period before the single cell's, but their antiphase alternations reach 11 against its 9 and their walks advance 1.99 to 2.02 per depth
category: diagonals
problems: [2]
status: computed
formalization: partial
evidence: [computations/skeleton_tree.py]
---

# To depth 250,000 the settled skeletons of the rows white left of a black cell form a tree of 8 branches that leave the single cell's at 53,207; no branch doubles its period before the single cell's, but their antiphase alternations reach 11 against its 9 and their walks advance 1.99 to 2.02 per depth

A row white left of a black cell has left diagonals $D_j(t) = \mathrm{cell}_t(lo - t + j)$, and each settles to a
periodic word. [SkeletonTree](../../Rule30Open/Diagonals/SkeletonTree.md) proves, with
[DrivenSkeleton](../../Rule30Open/Diagonals/DrivenSkeleton.md), that the eventual words of all such rows, up to a time
shift, are the paths of the pair map of [settled words](settled-words.md) that start from the single cell's pair
$(D_0, D_1)$ and, at each white diagonal $w$ whose predecessor $D_{w-1}$ has even weight per period, take either the
word $D_{w+1}$ or its complement (when the weight is odd the period doubles and the two choices are one class). Every
such path is realized by a row white left of a black cell (`branch_realized`). This entry follows every path.

## Method

`skeleton_tree` reads the single cell's settled words to depth 87,900 from 134,144 steps of the vector of diagonals
(`settled_slope.stream`; every onset is at or before the time base 133,888, a multiple of 64). It then runs the pair
map from $(D_0, D_1) = (1, 1)$ on words as Python integers, checks every word of the single cell's branch against the
evolved one to depth 87,900, takes the single cell's child at its white diagonals, and pushes the other class
whenever it is not a rotation of the first. On each branch it records the white diagonals, the doublings, and for
each stretch between white diagonals (a regime) the largest cyclic white run $g_j$, the largest antiphase alternation
$m_j$ of the pair $(D_{j-1}, D_j)$ (as in `settled_slope.alternations`) and the front walk of
[FrontWalker](../../Rule30Open/Diagonals/FrontWalker.md) on the settled words. The walk starts at $w_1 = 1$ on the
single cell's branch and continues from the parent's walk at each branch point; on the single cell's branch it is
FrontWalker's walk, $w_{200{,}000} = 402{,}228$ and $\max_{j < 200{,}000} (w_{j+1} - 2j) = 2{,}262$, as there. By
`walk_phase_transfer` and `shifted_walk_close`, any other walk along the settled words of a branch, from another phase
or on another row of the branch, advances within one period (16 or 32) of this one over every stretch of depths. The
run takes about 80 seconds and 0.1 GB; the tests check the single cell's branch word by word and its walk against
direct evolution to depth 300, and the flip of `branch_realized` on the evolved rows at $w = 2$ and 7.

## The branches (computed, to depth 250,000)

A branch is named by the white diagonals at which it takes the class its parent does not: S is the single cell's,
S.53207c leaves it at 53,207, and so on. Past the single cell's own branch, which child keeps the parent's name is a
convention: the child whose word is white at the aligned base time (`accumulate` from 0). The largest white run $W$, the largest alternation $A$ and the excess of the
walk include the depths before the split, which are the parent's.

| Branch | Leaves at | Later white diagonals (d: doubling) | Period at 250,000 | $W$ | $A$ | $\max_j (w_{j+1} - 2j)$ | Mean step past the split | Same depths, single cell | $w_{250{,}000}$ |
|---|---:|---|---:|---:|---:|---:|---:|---:|---:|
| S | | 2 d, 7 d, 28 d, 399 d, 53,207, 58,286, 87,866 d | 32 | 23 | 9 | 2,786 | | | 502,760 |
| S.53207c | 53,207 | 72,575 | 16 | 15 | 9 | 2,964 | 2.0099 | 2.0091 | 502,929 |
| S.58286c | 58,286 | 229,337 d | 32 | 19 | 9 | 1,968 | 2.0042 | 2.0100 | 501,673 |
| S.53207c.72575c | 72,575 | 165,748, 174,449, 179,399 | 16 | 15 | 10 | 3,724 | 2.0130 | 2.0101 | 503,688 |
| S.53207c.72575c.165748c | 165,748 | 183,183 d | 32 | 23 | 11 | 2,015 | 1.9948 | 2.0111 | 501,546 |
| S.53207c.72575c.174449c | 174,449 | 243,767 | 16 | 15 | 10 | 3,303 | 2.0112 | 2.0118 | 502,983 |
| S.53207c.72575c.179399c | 179,399 | 196,188 d | 32 | 22 | 11 | 2,666 | 2.0005 | 2.0120 | 502,300 |
| S.53207c.72575c.174449c.243767c | 243,767 | none | 16 | 15 | 10 | 3,487 | 2.0368 | 2.0377 | 503,447 |

"Mean step past the split" is $(w_{250{,}000} - w_k)/(250{,}000 - k)$ with $k$ the first multiple of 1,000 after the
split; the next column is the single cell's over the same depths. The largest $w_j / j$ past depth 1,000 is 2.0270 on
the single cell's branch (FrontWalker's number) and at most 2.0216 on the part of any other branch past its split.

The regimes past each split:

| Branch | Regime | Period | Depths | Largest $g$ | Largest $m$ | First at | Walk mean |
|---|---|---:|---:|---:|---:|---:|---:|
| S | 400 to 53,207 | 16 | 52,807 | 15 | 8 | 7,015 | 2.0173 |
| S | 53,208 to 58,286 | 16 | 5,078 | 15 | 7 | 57,292 | 1.9947 |
| S | 58,287 to 87,866 | 16 | 29,579 | 15 | 8 | 64,578 | 2.0125 |
| S | 87,867 to 250,000 | 32 | 162,133 | 23 | 9 | 88,202 | 2.0094 |
| S.53207c | 53,208 to 72,575 | 16 | 19,367 | 15 | 8 | 70,031 | 2.0216 |
| S.53207c | 72,576 to 250,000 | 16 | 177,424 | 15 | 9 | 189,229 | 2.0091 |
| S.58286c | 58,287 to 229,337 | 16 | 171,050 | 15 | 9 | 59,826 | 2.0043 |
| S.58286c | 229,338 to 250,000 | 32 | 20,662 | 19 | 9 | 236,780 | 2.0033 |
| S.53207c.72575c | 72,576 to 165,748 | 16 | 93,172 | 15 | 10 | 93,032 | 2.0075 |
| S.53207c.72575c | 165,749 to 174,449 | 16 | 8,700 | 15 | 8 | 171,456 | 2.0171 |
| S.53207c.72575c | 174,450 to 179,399 | 16 | 4,949 | 13 | 9 | 178,754 | 2.0200 |
| S.53207c.72575c | 179,400 to 250,000 | 16 | 70,600 | 15 | 9 | 209,728 | 2.0204 |
| S.53207c.72575c.165748c | 165,749 to 183,183 | 16 | 17,434 | 15 | 7 | 168,933 | 1.9932 |
| S.53207c.72575c.165748c | 183,184 to 250,000 | 32 | 66,816 | 23 | 11 | 248,416 | 1.9949 |
| S.53207c.72575c.174449c | 174,450 to 243,767 | 16 | 69,317 | 15 | 8 | 214,135 | 2.0152 |
| S.53207c.72575c.174449c | 243,768 to 250,000 | 16 | 6,232 | 14 | 9 | 249,918 | 1.9649 |
| S.53207c.72575c.179399c | 179,400 to 196,188 | 16 | 16,788 | 15 | 7 | 180,154 | 2.0201 |
| S.53207c.72575c.179399c | 196,189 to 250,000 | 32 | 53,811 | 22 | 11 | 245,156 | 1.9947 |
| S.53207c.72575c.174449c.243767c | 243,768 to 250,000 | 16 | 6,232 | 15 | 8 | 244,795 | 2.0393 |

- **Doublings.** No branch doubles before the single cell's 87,866; the other doublings are at 183,183, 196,188 and
  229,337, and four of the eight branches keep period 16 to depth 250,000. So the largest period over all rows at
  each depth up to 250,000 is the single cell's, and from depth 87,867 on the period of a row's diagonal $j$ is not a
  function of $j$: it is 16 or 32 depending on the branch.
- **White runs.** $W \le 23$ on every branch, attained on the single cell's and on S.53207c.72575c.165748c; the
  branches of period 16 stay at 15.
- **Antiphase alternations.** "First at" is the least depth $j$ whose pair $(D_{j-1}, D_j)$ reaches the regime's
  largest $m$. $A$ is 9 on the single cell's branch, as in [SettledSlope](../../Rule30Open/Diagonals/SettledSlope.md),
  reached at 88,202, and 10 or 11 on four other branches. The largest $m$ over all branches up to depth $J$ is the
  single cell's (8 from depth 7,015) up to 59,825, then 9 from 59,826 (on S.58286c), 10 from 93,032 (on
  S.53207c.72575c) and 11 from 245,156 (on S.53207c.72575c.179399c) to 250,000.
- **Walks.** The excess $\max_j (w_{j+1} - 2j)$ over all branches is 3,724, on S.53207c.72575c, against 2,786 on the
  single cell's; that branch walks slower than the single cell's over the same depths (2.0130 against 2.0101 per
  depth). The regime means range from 1.965 to 2.039, on regimes of 6,232 depths each; with the variance 2 of one plus
  a geometric variable of parameter 1/2 (the heuristic of FrontWalker), the standard error of a mean over $n$ depths
  is $\sqrt{2/n}$, 0.018 at $n = 6{,}232$ and at most 0.011 on the regimes of 19,000 depths or more, whose means
  range from 1.995 to 2.022.

The bounds of [seed window bounds](seed-window-bounds.md) agree with the tree: its abstraction follows both
choices at every white diagonal, and its number of periodic words at a depth, 16 from depth 400, 32 from 53,208, 48
from 58,287 and 64 from 72,576, is 16 rotations times the number of branches alive at that depth here: one, then S
and S.53207c, then S.58286c, then S.53207c.72575c.

## What it means

A statement about every row white left of a black cell, or every driven left half, is from depth 53,208 on a
statement about every branch of the tree, read as a maximum over the branches:

- [Driven run slopes](../../negative-results/diagonals/driven-run-slopes.md) and
  [driven left runs](driven-left-runs.md): $A_j$ and $P_j$ are the single cell's for $j \le 53{,}207$; deeper, the
  largest alternation over all drivers is the maximum over branches, which exceeds the single cell's from depth 59,826
  on (9 against 8) and reaches 11 at depth 245,156, against the single cell's 9; the period over all drivers is at
  most the single cell's to depth 250,000. The computed ranges of driven left runs ($t \le 175$) touch only depths
  below 100 and are unchanged.
- [Seed-uniform onsets](seed-uniform-onsets.md): its exact range ($j \le 76$) and the window abstraction's ($j \le
  1{,}252$) are below 53,207 and unchanged; the conjecture $T_j \le \lceil 3j/2 \rceil + 5$ for every seed is, from
  depth 53,208, a statement over the branches of the tree, and its "Skeleton" bullet, stated below depth 53,207, does not
  extend past it: the row of `branch_realized` is a seed whose diagonal 53,208 is not the single cell's under any time
  shift.
- [Seed window bounds](seed-window-bounds.md): already a maximum over the branches, as above, to depth 87,866.
- [FrontWalker](../../Rule30Open/Diagonals/FrontWalker.md)'s hypotheses over all drivers: on the settled words every
  branch has $w_j / j \le 2.0270 < 41/20$ past depth 1,000 and $w_{j+1} \le 2j + 3{,}724$ to depth 250,000
  ($2j + 2{,}802$ to depth 200,000, FrontWalker's range, against the single cell's $2j + 2{,}262$), and the
  alternation bound is $A = 11$ instead of 9 (10 to depth 200,000).

So the tree changes the numbers of the slope questions in range, but not their kind: on every branch the walk
advances about two times per depth, the white runs stay below the period, and the alternations stay small. Over all
drivers the open inputs are the single cell's, with a maximum over a tree that branches at each white diagonal without
a doubling.

## Reproduce

```bash
python -m computations.skeleton_tree --depth 250000   # about 80 s, 0.1 GB
python -m computations.skeleton_tree --depth 200000   # the numbers to 200,000
python -m pytest tests/test_skeleton_tree.py
```
