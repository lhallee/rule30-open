---
title: The points of K with an ether tail from cell 56 on are 203, all on four periodic orbits, and they are the points of a finite backward tree of 303
category: period-two
problems: [1]
status: computed
formalization: partial
evidence: [computations/k_survivors.py, computations/ether_k_tree.py, computations/held_shift.py]
---

# The points of K with an ether tail from cell 56 on are 203, all on four periodic orbits, and they are the points of a finite backward tree of 303

Let $H(U) = (U \gg 1) \oplus (U \lor (U \ll 1))$ be the held map and $K$ the set of 2-adic $U$ with $H^t(U)$ odd at
every odd $t$ ([the shift model](shift-model.md)). Conjecture (R) says that every rational point of $K$ has an
eventually periodic itinerary. A half whose cells from $p$ on are the ether at an alignment $(a, o)$ (four phases,
seven offsets) is the ether xor a defect $D_0 < 2^p$; take $p$ least, the bit length of $D_0$.
[EtherKTree](../../Rule30Open/PeriodTwo/EtherKTree.md) proves (R) in Lean for every point of $K$ with $p \le 28$, by a
census of the heads that do not break $K$ by step 63. This entry decides, head by head, which of those heads are points
of $K$, for $p \le 56$, and finds their structure: four periodic orbits and a finite tree of preimages above them.

## Result

1. **The true points** (computed; each one a finite certificate). A head of $h$ cells can start a point of $K$ only
   on the tree of $K$, $2^{h/2}$ leaves per alignment ([NoKTails16](../../Rule30Open/PeriodTwo/NoKTails16.md)); past
   the head every cell is the ether, so the condition of $K$ at each odd step $d \ge h$ is a test. `k_survivors` runs
   three exact filters: the odd steps below 64 on numbers of 64 cells, the odd steps below 256 on numbers of 256 cells,
   and an exact run of the defect, with no bound on its top, until an odd step breaks $K$ or the defect repeats at two
   steps that are multiples of 4. A repeat makes the orbit periodic with an even period after every odd step of the
   cycle has been tested, so the half is in $K$: a *true point*. Every point of $K$ with $p \le h$ is a leaf of the tree
   at $h$, so one run at the largest head counts every $p$. The counts, over all 28 alignments:

   | $h$ | leaves | pass step 63 | break $K$ later (latest step) | true points with $p \le h$ |
   |---|---|---|---|---|
   | 12 | 1,792 | 26 | 0 | 26 |
   | 16 | 7,168 | 34 | 0 | 34 |
   | 20 | 28,672 | 34 | 0 | 34 |
   | 24 | 114,688 | 54 | 0 | 54 |
   | 28 | 458,752 | 66 | 0 | 66 |
   | 32 | 1,835,008 | 104 | 18 (67) | 86 |
   | 36 | 7,340,032 | 701 | 562 (77) | 139 |
   | 40 | 29,360,128 | 7,528 | 7,389 (79) | 139 |
   | 44 | 117,440,512 | 112,948 | 112,793 (87) | 155 |
   | 48 | 469,762,048 | 1,848,683 | 1,848,520 (97) | 163 |
   | 52 | 1,879,048,192 | 29,374,858 | 29,374,655 (103) | 203 |
   | 56 | 7,516,192,768 | 470,028,972 | 470,028,769 (117) | 203 |

   Every head that passes the odd steps below 256 is a true point, none is left undecided, and every true point repeats
   by step 28. Up to 28 cells every leaf that passes step 63 is a true point; the 18 at 32 cells that break later are
   the leaves whose defect climbs past cell 32, so they need the bound 39 of
   [EtherKTree32](../../Rule30Open/PeriodTwo/EtherKTree32.md). By exact $p$ the true points number 2 at $p = 0$ (the
   ether itself), then 1, 1, 1, 6, 2, 6, 3, 4, 1, 7, 8, 12, 2, 10, 14, 6, 1, 14, 8, 30, 16, 8 and 40 at
   $p = 2, 3, 4, 5, 6, 7, 8, 10, 14, 15, 22, 24, 25, 26, 29, 31, 33, 34, 35, 36, 43, 45, 50$, and none at any other
   $p \le 56$. They lie at 8 of the 28 alignments: $(a, o) = (0, 0), (0, 5), (0, 6), (1, 5), (2, 0), (2, 5), (2, 6),
   (3, 5)$, with 29, 5, 1, 58, 54, 10, 2 and 44 points.
2. **Four periodic orbits** (computed). Every true point falls onto one of four cycles of the defect, 14 periodic points
   of $K$ at the even steps: the ether at offset 6 (period 4, itinerary period 2, the phases 0 and 2), two cycles of
   period 8 at offset 5 whose defects lie in the cells 0 to 7 (itinerary period 4), and one cycle of period 8 at offset 0
   whose defects reach cell 26 (itinerary period 4). These are the 14 points of spatial period 7 that item 2 of the
   shift model lists for itinerary periods 2 and 4; no other periodic point of $K$ has an ether tail from cell 56 on.
   Of the 203 true points, 102, 83, 15 and 3 fall onto the cycle of offset 5 with the defect 31 at phase 0, the cycle of
   offset 0, the other cycle of offset 5 and the ether.
3. **The backward tree is finite** (computed, exact). A point of $K$ has exactly two preimages in $K$ under $H^2$: the
   preimage $W$ of $V$ under $H$ with cell 0 equal to 1, read off $V$ cell by cell by
   $W(j + 1) = V(j) \oplus (W(j) \lor W(j - 1))$, and the two preimages of $W$. Where $V$ is the ether this recurrence
   is the one the ether obeys one phase earlier, so a preimage has an ether tail exactly when it meets the ether on two
   adjacent cells, which, with 28 values of the pair and the cell modulo 7, happens within 30 cells of the defect or
   never (`preimage`). Taking preimages with an ether tail from the 14 periodic points until none is new stops at
   **303 points**, with $p$ up to 78: the 203 above and 16, 8, 40, 28, 12, 24, 24 and 12 more at
   $p = 43, 45, 50, 57, 66, 70, 71, 78$ (the counts at 43, 45 and 50 are among the 203). Each of them repeats by step 36, each reaches its cycle within
   14 applications of $H^2$, and among them 150 have two preimages with an ether tail, 3 have one and 150 have none.
   The true points with $p \le 56$ are exactly the points of this closure with $p \le 56$.
4. **An independent check to 57 cells** (computed; the search is that of item 7 of the shift model). The same closure
   over every tail of period 7, not only the ether (`tail7_closure`: a preimage is kept when it repeats with period 7
   from some cell on), has 406 points, of which 278 have a preperiod of at most 57. The search of item 7 of the shift
   model, complete for the rational points of $K$ with preperiod $p$ and period $q$ with $p + q \le 64$, found 278
   points with denominator 127, the points with a tail of period 7. The closure's points are in $K$, so the two sets
   are equal, and every point of $K$ with a tail of period 7 and preperiod at most 57 lies in the closure. In
   particular the points of $K$ with an ether tail and $p \le 57$ are the 231 points of the closure with $p \le 57$.
5. **No regular language beyond a finite one** (computed). Within the range, the heads of the points of $K$ with an
   ether tail form a finite set, so they are trivially a regular language; the structure is a finite tree, not an
   automaton that reads defect words glued at many positions. The defects are dense (the longest run of ether cells
   inside a defect of the closure is 11 cells) and points deep in the tree share the top cells of their defect: the
   preimages under $H^2$ differ in the low cells.
6. **The survivors of step 63 follow the rate of independent coins** (computed; the model is a heuristic). Past the
   head a leaf meets $(64 - h)/2$ odd steps below 64, so leaves that pass them would number $28 \cdot 2^{h/2} \cdot
   2^{-(64-h)/2} = 28 \cdot 2^{h - 32}$ if each step were a fair coin: 114,688, 1,835,008, 29,360,128 and
   469,762,048 at $h = 44, 48, 52, 56$, against 112,948, 1,848,683, 29,374,858 and 470,028,972 counted. After step 63
   the late breaks continue at that rate (the latest at step 117 for $h = 56$), and only the points of the closure survive step 256.

## What it means

The census gives a sharp conjecture: **(E) the points of $K$ with an ether tail are exactly the 303 points of the
closure.** (E) implies (R) for every point of $K$ with an ether tail, since a finite set that $H^2$ maps into itself
makes every orbit in it eventually periodic, and it is checked for $p \le 56$ here and for $p \le 57$ through the search
of the shift model. Item 3 gives (E) a form that a counterexample has to meet: the closure holds every preimage in $K$
with an ether tail of each of its points, so the orbit under $H^2$ of a point of $K$ with an ether tail that is not in
the closure never enters it, and since every such point with $p \le 57$ is in it (item 4), **the defect of a point of
$K$ with an ether tail outside the closure has more than 57 cells at every even step.** For heads of 32 cells this agrees with [EtherKTree32](../../Rule30Open/PeriodTwo/EtherKTree32.md), which
proves the bound and (R) in Lean without the list. Only 8 of the 28 alignments of the ether carry a point of $K$ in the
range. A proof of (E) for every head would say that no long head passes every odd step, and item 6 finds the heads
leaving $K$ at about the rate of fair coins (a heuristic model), as on the vacuum, where that statement is the period-two question; the
monotone quantities that would bound the defect directly fail on the closure itself
([no monotone defect on K](../../negative-results/period-two/k-ether-monotone.md)).

## Reproduce

```bash
python -m computations.k_survivors --head 40     # heads of up to 40 cells, about 15 s
python -m computations.k_survivors --head 48     # about 4 minutes
python -m computations.k_survivors --head 52     # about 20 minutes, 0.5 GB
python -m computations.k_survivors --head 56     # about 2 hours, 0.6 GB
python -m computations.ether_k_tree --head 32 --bound 32   # the 18 leaves that climb past cell 32 fail
```

Each run prints the table row of item 1, the counts by $p$ and by alignment, the orbits, the closure of item 3 and the
count of item 4. `tests/test_k_survivors.py` checks the tree filter against the walk and `break_run` of `ether_k_tree`,
the wide filter and the exact run against runs of the held map on whole integers of 600 cells (the break at the same
step, or no break in 500 steps and the half equal after one period), the preimages against a step forward and their
points against 300 steps of the condition of $K$, the counts of 34 and 54 true points and of 14 periodic points on four
orbits, the closure of 303 and its agreement with the true points of up to 24 cells, the closure over tails of period
7 against the 278 points of item 7, and the census section of EtherKTree32 against the module.
