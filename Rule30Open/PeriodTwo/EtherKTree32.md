---
title: Every point of K whose tail from cell 32 on is the ether keeps its defect below cell 39, so (R) holds for it
category: period-two
problems: [1]
status: proved
lean: Rule30Open.PeriodTwo.EtherKTree32
headline: [ether_k_tail_clear32, ether_k_tail_eventually_periodic32, ether_k_tail_itinerary32, ktree32]
kit: new
kit_modules: [Rule30Ether, Rule30ZeroBoundary, Rule30PeriodTwoCoupled]
evidence: [computations/k_survivors.py, computations/ether_k_tree.py]
---

# Every point of K whose tail from cell 32 on is the ether keeps its defect below cell 39, so (R) holds for it

Let $H(U) = (U \gg 1) \oplus (U \lor (U \ll 1))$ be the held map and $K$ the set of 2-adic $U$ with $H^t(U)$ odd at
every odd $t$ ([the shift model](ShiftModel.md); `InK`). [EtherKTree](EtherKTree.md) proves conjecture (R) for every
point of $K$ whose tail from cell 28 on is the ether, by a census of the tree of $K$ in the kernel. This module runs the
same census on heads of 32 cells, four times as many leaves, with the bound 39 on the defect, and cuts each alignment
into eight kernel checks so that the build stays under 4.5 GB.

## Statement

With $e_a(j)$ the ether (`eth a j`) and the defect $D_t(j) = H^t(u)(j) \oplus e_{a+t}(j + o)$ as in
[EtherCensus](EtherCensus.md):

- `ether_k_tail_clear32`: if $u \in K$ and $u(j) = e_a(j + o)$ for every $j \ge p$, with $p \le 32$, then for every
  $t$ and every $j \ge 39$, cell $j$ of $H^t(u)$ is $e_{a+t}(j + o)$.
- `ether_k_tail_eventually_periodic32`: then $H^{t+P}(u) = H^t(u)$ for some $P > 0$ and every $t \ge T$.
- `ether_k_tail_itinerary32`: then the itinerary $\beta_s$ = bit 0 of $H^{2s}(u)$ is eventually periodic. This is (R)
  for every point of $K$ with such a tail.
- `ktree32`: the census, `etherTreeOK 32 32 39 16 a o = true` for each of the 28 alignments $a < 4$, $o < 7$.

## Argument

The census and its soundness are those of [EtherKTree](EtherKTree.md): `treeWith` of [NoKTails16](NoKTails16.md) walks
the heads of 32 cells under the ether, both values at an even cell and the value that keeps bit 0 of $H^d$ odd at an
odd cell $d$, so $2^{16}$ leaves per alignment; at each leaf `etherLeaf` either finds an odd step below 64 at which
bit 0 is 0 (`breakRun 32`, so no point of $K$ has this head) or settles the defect of the head with `runHead`: a
closed strip of 13 cells at a cell below 39 or a repeat of the defect, with no defect cell at 39 or above before.
`clear_of_etherTree` with $H = 32$, $L = 39$, 32 rounds of `breakRun` and 16 rounds of `runHead` turns a passing
census into the defect clear from cell 39 on, and `eventually_periodic_of_clear` and
`itinerary_of_eventually_periodic` of EtherCensus give the other two theorems.

**The cut.** One kernel check of a whole alignment at 32 cells peaked at 5.1 GB of resident memory. So the tree is cut
at cell 6. `treeWith_even_ok` says that the tree at an even cell $d$ passes when the two subtrees at $d + 1$, with cell
$d$ at 0 and at 1, pass; `treeWith_odd_ok` says that it passes at an odd cell $d$ when the subtree with the value
`cond (colRaw d n) n (n ||| 2^d)` passes, the value `treeWith` itself takes. The eight subtrees at cell 6 of each
alignment are checked one by one (`ktree32_a_o_k`, with the root number written out), and `ktree32_a_o` joins them by
these two lemmas, with each root and each value of `colRaw` at the cells 1, 3 and 5 checked by `decide`.

## The census

`python -m computations.ether_k_tree --head 32 --bound 39` runs the same test on the same leaves:

| head | leaves | break $K$ by step 63 | settled by a closed strip | by a repeat | latest settling step | highest defect cell before settling |
|---|---|---|---|---|---|---|
| 32 | 1,835,008 | 1,834,904 | 56 | 48 | 24 | 37 |

With the bound 32, the head itself, 18 leaves fail: they climb past cell 32 before they break $K$, at steps 65 and 67
([the points of K with an ether tail](../../findings/period-two/k-ether-points.md)). The bound 39 is the head plus 7,
the default of the census. `computations/k_survivors.py` writes the census section (`lean_section32`) and the test
checks it against this file.

`lake build Rule30Open.PeriodTwo.EtherKTree32` took 6,171 s of wall time with its imports built, about 27 s per
subtree check, and its Lean process peaked at 2.4 GB of resident memory (sampled every second); one check per alignment
took about 80 s and peaked at 5.1 GB. A measurement on one machine, not a cost model.

## What it means

(R) holds in Lean for every point of $K$ whose tail from cell 32 on is the ether, against 28 in EtherKTree. The
[points of K with an ether tail](../../findings/period-two/k-ether-points.md) finds which points these are: the true
points of $K$ with an ether tail from cell 32 on are 86, all on four periodic orbits, and the census here does not use
that list, only the breaks and the settling of every leaf. Each further 4 cells cost four times the leaves; the kernel
time per leaf of the cut census is about 2.7 times that of one check per alignment (27 s for each of 8
subtrees against 80 s for the whole alignment), the price of the memory bound.

## The kit

The pinned kit's `Rule30PeriodTwoCoupled` shows that the ether's left half is a point of the constrained set
(`etherLeft_eq_Theta`, `ether_free_bits`: the free bits alternate), the empty head of this census, and its main branch's
`Rule30EtherWallWitness` uses the same left half. `Rule30Ether` certifies the wall traps of the ether in the right half
and `Rule30ZeroBoundary` counts the residues of the constrained left half (`count_constrained`). Neither the pinned kit
nor its main branch has a statement about the zero-boundary left half with an ether tail below a nonempty head.
