---
title: Every point of K whose tail from cell 28 on is the ether keeps its defect below cell 28, so (R) holds for it
category: period-two
problems: [1]
status: proved
lean: Rule30Open.PeriodTwo.EtherKTree
headline: [ether_k_tail_clear, ether_k_tail_eventually_periodic, ether_k_tail_itinerary, clear_of_etherTree, etherLeaf_sound]
kit: new
kit_modules: [Rule30Ether, Rule30ZeroBoundary]
evidence: [computations/ether_k_tree.py, computations/no_k_tails16.py, computations/ether_certificate.py]
---

# Every point of K whose tail from cell 28 on is the ether keeps its defect below cell 28, so (R) holds for it

Let $H(U) = (U \gg 1) \oplus (U \lor (U \ll 1))$ be the held map and $K$ the set of 2-adic $U$ with $H^t(U)$ odd at
every odd $t$ ([the shift model](ShiftModel.md); `InK`). Conjecture (R) says that every rational point of $K$ has an
eventually periodic itinerary; on a tail that is the ether, it is the statement that the defect of the point against the
ether stays below a fixed cell (item 5 of the shift model). [EtherCensus16](EtherCensus16.md) proves this for every
half whose tail from cell 16 on is the ether, in $K$ or not, by a census of $2^{16}$ heads at each of the 28 alignments.
This module uses the condition of $K$: only $2^{14}$ heads of 28 cells at each alignment can be the start of a point
of $K$, and each of them either breaks $K$ by step 63 or settles without its defect ever leaving the head. So (R) holds
for every point of $K$ whose tail from cell 28 on is the ether.

## Statement

With $e_a(j)$ the ether (`eth a j`, the cycle of four states on a ring of seven cells) and the defect
$D_t(j) = H^t(u)(j) \oplus e_{a+t}(j + o)$ (`defect u a o t j`) as in [EtherCensus](EtherCensus.md):

- `ether_k_tail_clear`: if $u \in K$ and $u(j) = e_a(j + o)$ for every $j \ge p$, with $p \le 28$, then for every
  $t$ and every $j \ge 28$, cell $j$ of $H^t(u)$ is $e_{a+t}(j + o)$. The defect never reaches cell 28.
- `ether_k_tail_eventually_periodic`: then $H^{t+P}(u) = H^t(u)$ for some $P > 0$ and every $t \ge T$.
- `ether_k_tail_itinerary`: then the itinerary $\beta_s$ = bit 0 of $H^{2s}(u)$ is eventually periodic. This is (R)
  for every point of $K$ with such a tail.
- `clear_of_etherTree`, `etherLeaf_sound`: the census at one alignment and the test at a leaf, for any head size
  $H \le 64$, bound $L$ with $H \le L \le 126$, and rounds $R$ with $2R \le 64$.

## Argument

**The tree of $K$** (`treeWith` and `treeWith_sound` of [NoKTails16](NoKTails16.md)). Bit 0 of $H^d(u)$ is $u_d$ xor a
function of the cells below $d$, so at an odd step $d$ exactly one value of cell $d$ keeps it odd, whatever the cells
above $d$ are. The heads of 28 cells that do not break $K$ at an odd step below 28 form a binary tree that branches at
the even cells and is forced at the odd ones: $2^{14} = 16{,}384$ leaves at each alignment. `treeWith_sound` is stated
for any test at the leaves and any conclusion $Q$: if every point of $K$ that agrees with an accepted leaf on the
cells $0, \dots, 63$ satisfies $Q$, then every point of $K$ with the tail does.

**The test at a leaf** (`etherLeaf`). A leaf is the number $N$ that holds a head in the cells $0, \dots, 27$ and the
ether in the cells $28, \dots, 63$. The test accepts it when one of two checkers of earlier modules succeeds:

1. `breakRun 32 N` of [NoKTails](NoKTails.md) finds an odd step $2s + 1 < 64$ at which bit 0 of $H^{2s+1}(N)$ is 0.
   Bit 0 at that step reads only the cells $0, \dots, 2s + 1$, where $u$ and $N$ agree, so $u \notin K$
   (`not_inK_of_breakRun`), and $Q$ holds vacuously.
2. `runHead` of [EtherCensus](EtherCensus.md) settles the defect of the head, $(N \oplus e_a) \bmod 2^{28}$, which is
   the defect of $u$ at step 0: it lies in a closed strip of 13 cells at a cell below 28 or repeats a snapshot, and no
   step before that puts a defect cell at 28 or above. Then `runHead_sound` gives the defect of $u$ clear from cell 28 on at every step.

**The census** (`etherTreeOK`, `ktree`). For each of the 28 alignments $(a, o)$ with $a < 4$ and $o < 7$, the kernel
runs the tree with this test as one computation. `ether_k_tail_clear` reduces any alignment to $(a \bmod 4, o \bmod 7)$,
which gives the same cells, and applies `clear_of_etherTree` with $H = L = 28$, 32 rounds of `breakRun` and 16
rounds of `runHead`. `eventually_periodic_of_clear` and `itinerary_of_eventually_periodic` of EtherCensus give the
other two theorems.

## The census

`python -m computations.ether_k_tree` runs the same walk and the same test (`leaf_ok`) on the same leaves. For the
heads of 28 cells with the bound 28:

| leaves | break $K$ by step 63 | settled by a closed strip | by a repeat | latest break | latest settling step | highest defect cell before settling |
|---|---|---|---|---|---|---|
| 458,752 | 458,686 | 24 | 42 | step 59 | 16 | 25 |

So every leaf that does not break $K$ by step 63 keeps its defect below cell 28, inside the head. The last column
counts only the steps before a leaf settles: a leaf settled by a closed strip at cell $c$ can raise its defect up to
cell $c$ later, so the bound the census proves is 28, not 26. The bound 28 is the
least the module can use, since `etherLeaf_sound` needs the defect at step 0 clear from the bound on. With heads of 24
cells the least bound that passes is 27, not 24: 12 leaves settle by a closed strip whose cell is 26, which `runHead`
accepts only below the bound (`--head 24 --bound 26` fails on them). The walk takes 22,937,768 steps of $H$ at the odd
cells and the tests at the leaves 14,221,560 more, against $2^{28} \cdot 28 = 7{,}516{,}192{,}768$ heads for a census
without $K$. `lake build Rule30Open.PeriodTwo.EtherKTree` took 520 s of wall time with its imports built, and its Lean
process stayed under 1.6 GB of resident memory (sampled every second), since the module elaborates its 28 kernel checks
one at a time (`Elab.async false`); a measurement on one machine, not a cost model.

With a wider bound the same census runs further (`--head 36 --bound 126 --fuel 400`):

| head | leaves | break $K$ by step 63 | settled by a closed strip | by a repeat | latest break | latest settling step | highest defect cell before settling |
|---|---|---|---|---|---|---|---|
| 12 | 1,792 | 1,766 | 0 | 26 | step 33 | 16 | 9 |
| 16 | 7,168 | 7,134 | 0 | 34 | step 43 | 16 | 14 |
| 20 | 28,672 | 28,638 | 0 | 34 | step 43 | 16 | 14 |
| 24 | 114,688 | 114,634 | 12 | 42 | step 49 | 16 | 23 |
| 28 | 458,752 | 458,686 | 24 | 42 | step 59 | 16 | 25 |
| 32 | 1,835,008 | 1,834,904 | 56 | 48 | step 63 | 24 | 37 |
| 36 | 7,340,032 | 7,339,331 | 617 | 84 | step 63 | 232 | 73 |

Every leaf passes at every head size. With the bound $h + 7$ and 16 rounds of `runHead` (the default of the census), 378
leaves of 36 cells fail, and all of them settle by a closed strip once the bound and the rounds are raised.

The leaves that do not break $K$ by step 63 are the heads that reach a periodic point of $K$ in the tail census, 26 of
12 cells and 34 of 16 cells ([the tail census](../../findings/period-two/tail-census.md), item 4), and the test checks
the counts. So every point of $K$ whose tail from cell 36 on is the ether has an eventually periodic itinerary, by
computation; in Lean the range is 28 cells.

```bash
python -m computations.ether_k_tree --head 28 --bound 28            # the census above, heads of 12 to 28 cells
python -m computations.ether_k_tree --head 36 --bound 126 --fuel 400 # heads of 12 to 36 cells, a few minutes
python -m computations.ether_k_tree --head 36                        # the default bound h + 7: 378 leaves fail
python -m computations.ether_k_tree --lean                          # the census section of the module
lake build Rule30Open.PeriodTwo.EtherKTree
```

`tests/test_ether_k_tree.py` checks the leaves of the tree at heads of 8 cells against a run of every head on whole
halves of 200 cells, the test at sampled leaves of 16 cells against direct runs of the held map (the break at the same
step, or no break within 120 steps and the cells from the bound on equal to the ether at every step), the counts of
leaves that do not break $K$ against the tail census, and the census section against the module.

## What it means

The condition of $K$ cuts the census from $2^h$ heads to $2^{h/2}$ leaves per alignment, and most leaves break $K$
within a few dozen steps; the few that do not settle by a repeat of the defect or in a closed strip, and at 12 and 16
cells they are exactly the heads that reach a periodic point of $K$ in the tail census. So on the ether (R) is now
proved for heads of 28 cells, against 16 for every half in [EtherCensus16](EtherCensus16.md), and computed to 36. The
bound uses $K$ only through the breaks: at a leaf that survives step 63, the defect is bounded by the ether's own
closed strips and repeats, as without $K$. Each pair of cells doubles the leaves, so this is still a census of finitely
many heads, and the leaves that survive past step 63 grow with the head (54, 66, 104 and 701 at 24, 28, 32 and 36
cells, the highest defect cell before settling rising to 73); 18 of the 104 and 562 of the 701 break $K$ after step 63,
and the true points are counted in [the points of $K$ with an ether tail](../../findings/period-two/k-ether-points.md). A proof for every head would need what the ether census asks
for, a bound on the top of every defect, or a proof that the survivors of $K$ settle, and the items 3 and 4 of the
[ether census](../../findings/period-two/ether-defect-census.md) say why the local routes to the first fail.

## The kit

The kit's `Rule30Ether` certifies the wall traps of the ether in the right half and its `Rule30ZeroBoundary` counts the
residues of the constrained left half (`count_constrained`), the tree used here, in its encoding. Neither the pinned
kit nor its main branch (whose `Rule30EtherGrounding` and `Rule30EtherEpisode` treat ether columns behind a black right
edge) has a statement about the zero-boundary left half with an ether tail below a head.
