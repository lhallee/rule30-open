---
title: Every defect of up to 20 cells on the ether settles, so (R) holds for those ether tails; a potential on top windows fails even on the moves real defects make
category: period-two
problems: [1]
status: computed
formalization: wanted
evidence: [computations/defect_potential.py, computations/held_shift.py]
---

# Every defect of up to 20 cells on the ether settles, so (R) holds for those ether tails; a potential on top windows fails even on the moves real defects make

Let $H(U) = (U \gg 1) \oplus (U \lor (U \ll 1))$ be the held map and $K$ the set of 2-adic $U$ with $H^t(U)$ odd at
every odd $t$ ([the shift model](shift-model.md)). Conjecture (R) says that every rational point of $K$ has an
eventually periodic itinerary. For a point whose tail is the ether, the cycle of four states on seven cells, item 5 of
the shift model reduces (R) to a bounded top of the defect $D_t = H^t(U) \oplus B_t$, where $B_t$ is the ether laid
on the cells $j \ge 0$ at one of its 28 alignments (four phases, seven offsets). This entry settles the defect for every
head of up to 20 cells, with or without $K$, and tests three ideas for a bound in general: a potential on the cells at
the top, the top cells as a finite certificate, and the statistics of the climb. None of the three gives a proof, and
the census says where each stops.

## Result

1. **The census** (computed; each head is a finite proof). The pair $(D_t, t \bmod 4)$ is the state of a
   deterministic system, $D_{t+1}(j) = D_t(j+1) \oplus \big((x_t(j) \lor x_t(j-1)) \oplus (B_t(j) \lor B_t(j-1))\big)$
   with $x_t = D_t \oplus B_t$ and $x_t(-1) = 0$, and $D_0$ runs over every word below $2^p$ as the head runs over the
   words of $p$ cells. A head is *settled* when its defect enters a closed strip (item 2), which bounds its top
   forever, or when its state repeats. For every alignment and every head of $p$ cells:

   | $p$ | heads | settled by a closed strip | settled by a repeat (top at most) | highest top | last settling step |
   |---|---|---|---|---|---|
   | 8 | 7,168 | 4,994 | 2,174 (14) | 48 | 257 |
   | 12 | 114,688 | 106,289 | 8,399 (17) | 60 | 298 |
   | 16 | 1,835,008 | 1,816,004 | 19,004 (21) | 78 | 432 |
   | 18 | 7,340,032 | 7,308,760 | 31,272 (21) | 87 | 454 |
   | 20 | 29,360,128 | 29,315,270 | 44,858 (24) | 102 | 538 |

   Every head is settled, none reaches the 120 cells the computation can follow, and the repeats have period 4, 8 or 16.
   So every 2-adic rational whose tail from cell $p \le 20$ on is the ether, in $K$ or not, has an eventually periodic
   orbit, with its top at most 102, and **(R) holds for every point of $K$ with such a tail.** The same holds for a tail
   that reaches the ether on the ring after $\tau$ steps when $p + \tau \le 20$, since $H^\tau(U)$ then has an ether tail
   from cell $p + \tau$ on. The heads settled by a repeat keep their top within 24 cells of the wall, where a closed
   strip of 13 cells does not fit. Nothing here uses $K$; the kit has no statement about the zero-boundary left half
   with an ether tail.
2. **The closed strips** (computed). The greatest set of strips $D(c - w + 1 .. c)$, with $D$ zero above $c$, that one
   step maps into the set for both values of $D(c - w)$ and that never raise the top above $c$ is empty for $w \le 12$
   and has 1,915 strips at $w = 13$, all at one residue of $c + \text{offset}$ modulo 7, by phase 433, 533, 344 and 605.
   Computed directly on $H$, these are the counts of the mirror `background_halves.wall_set` beside the ether up to a
   rotation of the phases ([ether fronts](../../negative-results/period-two/ether-front-windows.md)). A defect inside
   one keeps its top at or below $c$ whatever lies below $c - 12$: the property is closed under one step for both
   inputs, so it holds at every step by induction. In the census, 99.85% of the heads of 20 cells settle this way.
3. **No potential on top windows, not even on the moves real defects make** (computed). Write $\lambda(w)$ for the
   largest mean gain per step over the cycles of the window automaton of `held_shift.front_rate` (the top, the $w - 1$
   cells below it, free cells below, a lost top passing through one node per phase). A potential $\varphi$ on its
   states with $\text{gain} + \varphi(\text{after}) - \varphi(\text{before}) \le 0$ on every move exists exactly when
   $\lambda(w) \le 0$. Karp's algorithm gives exactly $\lambda(5) = 7/25$, $\lambda(6) = 7/24$, $\lambda(7) = 7/32$ and
   $\lambda(8) = 7/32$, each on a cycle that is checked edge by edge. Restricted to the 1,448 of the 12,931 moves at
   $w = 8$ that real defects make (300 random heads of 40 cells at random alignments, 1,500 steps each, moves with the
   top at least 16 cells above the wall), the largest mean gain is still $7/32$, on a cycle of 32 moves. So the positive
   cycles are not made of moves that never occur: every move of a cycle of the largest gain is made by some real
   defect, and a potential on the window states fails even on the moves that occur. Whether one real defect follows a
   whole cycle of positive gain is not tested here; a potential that uses memory of the past moves would have to
   exclude exactly that.
4. **The top cells do not force entry** (computed). The cells at or above $t$ at step $t$ read only the cells at or
   above 0 at step 0, so a word of $n$ cells at the top of a head, with anything at all below it and the wall anywhere,
   is followed exactly in a region that shrinks by one cell per step. If the defect enters a closed strip inside that
   region, every head that ends in that word is settled. Starting from the words of 4 cells whose top cell is a defect
   (a head whose top cells agree with the ether is a shorter head), at all 28 alignments, and extending each unsettled
   word by one cell below, the words not settled number 224, 448, 895, 1,761, 3,461, 6,766, 13,212, 25,938, 50,531,
   98,165, 192,964, 372,901, 730,574, 1,420,148 and 2,788,214 at lengths 4 to 18: 98.2% stay unsettled at length 18,
   and the tree grows by a factor of about 1.96 per cell. The settling time explains it: among the heads of 16 cells,
   the share not yet settled is 0.46 after step 50, 0.21 after 100, 0.10 after 150, 0.037 after 200, 0.0094 after 250,
   0.0037 after 300 and 0.00046 after 400, a factor of about 10 per 100 steps from step 150 on, or $e^{-1/43}$ per step,
   far slower than the factor $1/2$ per cell a finite tree would need, since a word of $n$ cells is followed exactly
   for about $n$ steps plus the rise of its top. That the tree is infinite is a heuristic from these rates, not proved: it would mean a configuration infinite below the top whose
   defect never enters a closed strip.
5. **The climb** (computed; the model is a heuristic). Random heads of 50, 200 and 800 cells, 100 of each at random
   alignments, all enter a closed strip, at median step 43 to 50 and by step 290 at the latest; the top rises at most
   37 cells above the head, with median 8 or 9, whatever the length. Among the heads of 16 cells the share whose top
   rises more than $x$ cells above the head is 0.84, 0.39, 0.12, 0.022, 0.0051, 0.0029 and 0.00075 at
   $x = 0, 10, 20, 30, 40, 50, 60$. The largest rise over all heads of $p$ cells, 40, 48, 62, 69 and 82 at
   $p = 8, 12, 16, 18, 20$, grows by about 4 cells per cell of head. A head of 16 cells with the largest rise, 62,
   settles at step 401, a climb of about 0.15 cells per step, with no visible order in the cells below its top. A climb
   that stops at a rate per step that does not depend on the head gives a rise with an exponential tail, and its maximum over $28 \cdot 2^p$ heads then grows linearly in $p$, as
   observed. Under that model every head settles with probability one and almost every head settles early, which is the
   shape of the heuristic for the Collatz map; it says nothing about a single head.

## What it means

For ether tails, (R) is checked for every head of up to 20 cells, and the mechanism is uniform: the top enters a
closed strip of 13 cells, or stays within 24 cells of the wall. What a proof needs is that every defect enters, the
mirror of the kit's `Absorption` for the ether ([ether fronts](../../negative-results/period-two/ether-front-windows.md)),
and items 3 and 4 show that the two local routes to it, a potential and a finite set of top words, do not reach it. A potential on top windows fails even on the moves real defects
make, and the top cells of a head decide entry for a share of words that does not beat the doubling of their number,
because a chaotic region below the top can keep the top climbing for hundreds of steps before the strip forms. The
stopping is a property of the chaotic region below the top, as in the Collatz problem: random heads stop early and the
largest rise grows only like the logarithm of the number of heads, but no argument here turns that into a bound for one
head. Nothing here uses $K$, and none of it is evidence that $K$ matters for ether tails.

## Reproduce

```bash
python -m computations.defect_potential census --bits 16          # about 20 s
python -m computations.defect_potential census --bits 20          # about 10 minutes
python -m computations.defect_potential closed --width 14
python -m computations.defect_potential karp --window 8
python -m computations.defect_potential realized --window 8 --length 40 --steps 1500 --count 300   # about 30 s
python -m computations.defect_potential tree --bits 4 --length 18  # about a minute
python -m computations.defect_potential random --length 800 --count 100 --steps 3000
```

`tests/test_defect_potential.py` checks the defect, stepped as words and as integers, against
`held_shift.defect_tops`, which steps the whole integer with its tail; the closed strips against the mirror
`background_halves.wall_set` and against direct runs with random cells below; the census, its repeats and its bounds
against direct runs; the soundness of a settled top word under random cells below and the wall at three depths; and
the window automaton against `held_shift.front_rate`, with Karp's value against the longest walks.
