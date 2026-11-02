---
title: K is a Cantor set of dimension 1/2 in which the stripe-tailed points are dense, and its other rational points with a tail period up to 28 and p + q at most 64 lie in finite backward closures of the 14 ether points
category: period-two
problems: [1]
status: computed
formalization: partial
evidence: [computations/k_structure.py, computations/held_shift_search.c, computations/held_shift.py]
---

# K is a Cantor set of dimension 1/2 in which the stripe-tailed points are dense, and its other rational points with a tail period up to 28 and p + q at most 64 lie in finite backward closures of the 14 ether points

Let $H(U) = (U \gg 1) \oplus (U \lor (U \ll 1))$ be the held map on 2-adic integers (cells $0, 1, 2, \dots$) and $K$ the
set of $U$ with $H^t(U)$ odd at every odd $t$ ([the shift model](shift-model.md)). Conjecture (R) says that every
rational point of $K$ has an eventually periodic itinerary, and conjecture (E) that the points of $K$ with an ether tail
are the 303 points of a finite backward closure ([the points of K with an ether tail](k-ether-points.md)). This entry
measures $K$, lists its rational points family by family of tail periods, and asks whether the form of (E) holds for
every tail period. Write $F_Q$ for the rational points whose cells are periodic with a period dividing $Q$ from some
cell on (denominator dividing $2^Q - 1$). $H$ maps $F_Q$ into itself, and each point of $K$ has exactly two preimages
under $H^2$ in $K$, both rational when it is (item 4 of the shift model) and with a tail period dividing $4Q$, since
past the head of the image the pair of the last two cells of a preimage and the cell modulo $Q$ take at most $4Q$
values (`rat_preimage` holds them exactly).

## Result

1. **The size of $K$** (the count is proved in Lean, [ShiftModel](../../Rule30Open/PeriodTwo/ShiftModel.md) and the
   kit's `Rule30ZeroBoundary.count_constrained`; the rest is an argument). Bit 0 of $H^t(U)$ reads the cells $0, \dots,
   t$ only, and at an odd $t$ it is cell $t$ xor a function of the cells below. So the heads of $h$ cells consistent
   with $K$ at every odd step below $h$ number exactly $N(h) = 2^{\lceil h/2 \rceil}$ (`head_count`, $h \le 24$;
   checked against every integer below $2^h$ for $h \le 12$), and no later step removes one: a later odd step $t$
   constrains cell $t$, which lies above the head, and both values of every even cell keep the tree growing. So the
   tree of $K$ branches at every even cell forever, $K$ is homeomorphic to $\{0, 1\}^{\mathbb N}$ (a Cantor set,
   uncountable, of Haar measure 0), its box dimension in the 2-adic metric is $\lim \log_2 N(h) / h = 1/2$, and the
   uniform measure on itineraries gives every cylinder of $h$ cells mass $2^{-\lceil h/2 \rceil}$, so its Hausdorff
   dimension is $1/2$ as well. The rational points are countable and **dense**: the points of $K$ with a stripe tail that
   reach one of the two stripes within $\lceil h/2 \rceil - 1$ applications of $H^2$ number $2^{\lceil h/2 \rceil}$
   and have pairwise distinct heads of $h$ cells, every head of the tree (`stripe_heads`, all even $h \le 20$). This
   holds for every $h$: their itineraries are every word of $\lceil h/2 \rceil - 1$ readings followed by the constant
   itinerary of either stripe, and the first $\lceil h/2 \rceil$ readings fix the first $h$ cells (item 1 of the shift
   model). So no head is excluded by $K$ alone, every cylinder of $K$ holds rational points on which (R) holds (item 6 of
   the shift model, from the kit's `stripe_absorb`) and uncountably many points with no periodic itinerary, and a census of heads decides
   nothing until a tail is fixed. With a tail fixed the count changes completely: on the ether, the heads of $h$ cells
   that pass the odd steps up to 63 fall at the rate of a fair coin per odd step past the head, and the true points stop at
   203 by $h = 56$ (items 1 and 6 of the ether entry).
2. **Periodic points** (computed; `zoo_points`, every itinerary of period $n \le 16$, the columns run to 1,024 cells,
   which settles every orbit whose points at the $2n$ steps of a period have preperiods of at most $1022 - q$, so
   every point of preperiod at most $1023 - q - 2n$). The periodic points of $H^2$ in $K$ with itinerary period at
   most 16, a tail period of at most 28 and a preperiod of at most 963 are 16: the two stripes (period 2, preperiod 0,
   itinerary period 1) and the 14 of the ether (period 7, preperiods up to 26; 2 of itinerary period 2 and 12 of
   period 4). None has a tail of period 14, 21 or 28 or a tail on another background, in agreement with the table of
   item 2 of the shift model for $n \le 12$.
3. **Purely periodic points** (computed; `purely_periodic`, every word of least period $q \le 16$, run exactly until it
   breaks $K$ or repeats). The numbers whose cells are periodic from cell 0, denominator $2^q - 1$, are in $K$ only for
   $q = 2$ (the two stripes) and $q = 7$ (two of the ether's periodic points); every other word of up to 16 cells breaks
   $K$, none is undecided. Each of the four is itself a periodic point.
4. **The closures** (computed, exact; `closure_levels`). For each $Q$, the closure $C_Q$ is the set of points of $K$ in
   $F_Q$ whose orbit under $H^2$ reaches a periodic point of $K$ of item 2 other than the stripes, found by taking
   preimages in $K$ with a tail period dividing $Q$ until none is new:

   | $Q$ | periodic points | closure $C_Q$ | depth | largest preperiod | longest ring transient into the ether |
   |---|---|---|---|---|---|
   | 1 to 6, 8 to 13, 15, 16 | 0 | empty | | | |
   | 7 | 14 | 406 | 14 | 78 | 2 |
   | 14 | 14 | 487,648 | 24 | 244 | 43 |
   | 21 | 14 | 406 | 14 | 78 | 2 |
   | 28 | 14 | at least 176,564 | at least 34 | at least 185 | not computed |

   The depth is the most applications of $H^2$ a point needs to reach a periodic point. $C_7$ is the closure over every
   tail of period 7 of the ether entry (item 4 there), and its 303 points with a tail on the ether cycle are the closure
   of (E). $C_{14}$ has, level by level, 14, 14, 28, 56, 112, 224, 384, 512, 768, 960, 960, 1,440, 2,496, 3,840, 5,344,
   10,336, 1,280, 2,560, 3,968, 7,936, 14,336, 28,672, 57,344, 114,688 and 229,376 points, of which 406 have a tail of
   period 7. No point of $K$ over $C_7$ has a tail of least period 21, so $C_{21} = C_7$. For $Q = 28$ level $s$ holds
   $14 \cdot 2^{s - 1}$ points for $1 \le s \le 13$ (both preimages of every point of levels 1 to 12 are in $F_{28}$),
   preperiods reach 185 by level 13, and the closure is not computed to its end: its points reached through points of
   preperiod at most 100 are 176,564, down to level 34 (`closure` with `max_pre`).
5. **Every closure is finite** (argument, with item 4 for $Q = 7$). Let $X$ be in $C_Q$ and $X_k = H^{2k}(X)$. The tail
   word of $X_{k+1}$ is the tail word of $X_k$ after two steps of the held map on a ring of $Q$ cells, read at the same
   cells, so if $i$ is the first $k$ at which the tail of $X_k$ is on the ether cycle (whose words have period 7), the
   tail of $X$ is still off the cycle after $2(i - 1)$ ring steps, and $2i - 1 \le \tau_Q$, the longest transient
   into the ether on the ring of $Q$ cells (`ring_transients`). Then $X_i$ is in $F_7$, so in $C_7$, at depth at most
   14. So the depth of $C_Q$ is at most $14 + \lfloor (\tau_Q + 1)/2 \rfloor$, and $C_Q$, a tree of branching at most
   2, is finite. For $Q = 14$ the bound is 36 and the depth is 24. In the levels 15 to 24 of $C_{14}$ every point has a tail of least
   period 14, off the ether cycle, and from level 20 on the count doubles at each level; the bound caps such runs at
   level 36, and this one ends at level 24. The stripes behave differently: their tails are fixed by the ring map, every preimage
   in $K$ of a stripe-tailed point is stripe-tailed (the kit's `Rule30ZeroBoundaryStripe.agrees_pre`), and their
   closure is infinite, $2^s$ points at level $s \ge 1$, and dense by item 1.
6. **The closures against a complete search** (computed; `search_points` on the hits of `held_shift_search.c` run to
   depth 64 with periods up to 28, complete for the rational points of $K$ with least period $q \le 28$ and
   $p + q \le 64$, each hit run exactly). The 8,051 hits give 2,592 points of $K$
   (92 hits break $K$ past the search's horizon, none is undecided), the count of item 7 of the shift model: 896 with a
   stripe tail (least period 2) and 278, 1,312 and 106 of least period 7, 14 and 28. For every $Q \le 16$ and for
   $Q = 21$ and 28, the points of the search in $F_Q$ without a stripe tail are exactly the points of $C_Q$ with
   $p + q \le 64$: none for $Q$ not divisible by 7, 278 for $Q = 7$ and 21, 1,590 for $Q = 14$ and 1,696 for $Q = 28$
   (for $Q = 28$ the points of $C_{28}$ reached through preperiods of at most 100). Since the search is complete in its
   range, **every point of $K$ with a tail period $q \le 28$ and $p + q \le 64$ either has a stripe tail or lies in the
   closure of the 14 ether points**, and its itinerary is eventually periodic.
7. **What the generalization of (E) amounts to** (argument). Say that (E$_Q$) holds when the points of $K$ in $F_Q$
   whose tail does not fall onto a stripe are exactly $C_Q$. If $U$ is such a point, its tail reaches a cycle of the
   ring map after some $\tau$ steps, and for an even $\tau' \ge \tau$ the point $H^{\tau'}(U)$ is in $K$ with a tail
   exactly on a background. If the background is the ether, (E) puts $H^{\tau'}(U)$ among the 303 points and $U$ in
   $C_Q$; if it is another background, the tail census asks that no point of $K$ have it ([NoKTails16](../../Rule30Open/PeriodTwo/NoKTails16.md)
   proves this for heads of up to 16 cells on the 12 backgrounds of tails of up to 12 cells). Conversely (E$_7$)
   contains (E), and (E$_Q$) excludes every other background with $L$ dividing $Q$, since $C_Q$ holds ether tails only.
   So **(E$_Q$) for every $Q$ is equivalent to (E) together with (N): no point of $K$ has a tail on a background other
   than the stripes and the ether**, and with the kit's theorem on the stripes these give (R). The generalization adds
   no new conjecture; the finite closures of item 4 are what (E) and (N) predict, and item 6 tests them on tails of
   period up to 28. Every point found in any range has an eventually periodic itinerary: the closures by construction,
   the search points by an exact repeat.

## What it means

$K$ is as large as a set of its kind can be at its density: a Cantor set of dimension 1/2 whose every cylinder holds
rational points that are preperiodic, so neither the size of $K$ nor the topology of its rational points says anything
about (R). The arithmetic does: a fixed tail cuts $K$ down to finitely many points in every case computed except the
stripes, where the closure is infinite and (R) is already a theorem. On the ether the finite closures for the tail
periods 7, 14 and 21 are consequences of the base closure of 406 points and of the finite transients of the ring, not
separate facts, so the route to (R) through rational points is exactly (E) and (N); both are statements that no long
head on a fixed tail passes every odd step, and the descent of the top at a growing lag reduces (E) to one finite census
per head length without linking the lengths ([the descent at a lag](../../negative-results/period-two/k-descent-lag.md)).

## Reproduce

```bash
python -m computations.k_structure heads --max-h 24                        # item 1, seconds
gcc -O3 -mno-avx -fopenmp computations/held_shift_search.c -o search
./search 64 28 126 10 4 > hits64.txt                                       # about an hour on 4 threads
python -m computations.k_structure families --max-q 16 --max-n 16 --search hits64.txt   # items 2 to 6, about 10 minutes
```

`tests/test_k_structure.py` checks the head count against every integer below $2^h$ for $h \le 12$ and the heads of
the stripe tree, the exact rationals (a step, the preimages, the least form and the denominator) against the held map on
long integers, the exact run against direct runs, the periodic points of period dividing 4 against the table of the
shift model, the closure of period 7 (406 points, 303 on the ether cycle, depth 14, denominator 127) and the first
levels of the closure of period 14, the closure of period 14 against the rational points of $K$ with $p + q \le 18$
found from the tree of $K$, the descent census against runs of whole integers, and the reading of the search's output.
