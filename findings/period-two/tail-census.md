---
title: Beyond the stripes and the ether, every periodic tail of up to 12 cells falls onto a background where the tops of most defects run away, and no head of up to 16 cells on one of them is in K
category: period-two
problems: [1]
status: computed
formalization: partial
evidence: [computations/tail_census.py, computations/defect_potential.py, computations/held_shift.py]
---

# Beyond the stripes and the ether, every periodic tail of up to 12 cells falls onto a background where the tops of most defects run away, and no head of up to 16 cells on one of them is in K

Let $H(U) = (U \gg 1) \oplus (U \lor (U \ll 1))$ be the held map and $K$ the set of 2-adic $U$ with $H^t(U)$ odd at
every odd $t$ ([the shift model](shift-model.md)). Conjecture (R) says that every rational point of $K$ has an
eventually periodic itinerary. A rational $U$ has a head of $p$ cells and then a tail that repeats a word of $q$ cells;
far from cell 0 the tail evolves by the ring map of $q$ cells and falls onto a cycle, a *background*: $P$ states on a
ring of least spatial period $L$, laid on the cells $j \ge 0$ at one of $PL$ alignments. As for the ether
([the ether census](ether-defect-census.md)), the defect $D_t = H^t(U) \oplus B_t$ is a deterministic system, and a
bounded top is the same as an eventually periodic orbit (item 5 of the shift model). This entry lists every background
that a tail of up to 12 cells reaches and runs the defect census on each, without and with the condition of $K$.

## Result

1. **The backgrounds** (computed, complete for $q \le 12$; `rings`). The ring map is Rule 30 mirrored, so these are the
   backgrounds of Rule 30 of [periodic backgrounds](../columns/space-time-backgrounds.md) of spatial period at most 12
   (the test checks the two lists against each other). There are 14 up to rotation:

   | $L$ | $P$ | a state, cell 0 first | shift $(k, s)$ | alignments | tails of $q$ cells reaching it ($q$: count) | longest transient |
   |---|---|---|---|---|---|---|
   | 1 | 1 | 0 (the vacuum) | (1, 0) | 1 | every $q$: 2 to 242 | 17 |
   | 2 | 1 | 10 (the stripes) | (1, 0) | 2 | even $q$: 2 | 0 |
   | 4 | 8 | 1000 | (2, 1) | 8 | 4: 12, 8: 28, 12: 12 | 3 |
   | 5 | 5 | 11100 | (1, 2) | 5 | 5: 30, 10: 180 | 20 |
   | 7 | 4 | 1000000 (the ether) | (4, 0) | 28 | 7: 49 | 2 |
   | 7 | 63 | 1010000 | (9, 2) | 63 | 7: 77 | 2 |
   | 8 | 40 | 11100000 | (5, 5) | 40 | 8: 224 | 16 |
   | 9 | 72 | 111000000 | (8, 5) | 72 | 9: 90 | 2 |
   | 9 | 171 | 100100000 | (19, 5) | 171 | 9: 414 | 13 |
   | 10 | 15 | 1110100000 | (3, 2) | 30 | 10: 840 | 46 |
   | 11 | 17 | 10010100000 | (17, 0) | 187 | 11: 495 | 17 |
   | 11 | 154 | 10100000000 | (14, 3) | 154 | 11: 1,551 | 55 |
   | 12 | 3 | 111110010000 | (1, 4) | 12 | 12: 12 | 0 |
   | 12 | 102 | 100100000000 | (34, 8) | 408 | 12: 3,828 | 126 |

   An alignment is counted once per distinct space-time pattern on the cells $j \ge 0$. At $q = 13$ and 14 nine more
   appear: $L = 13$ with $P = 91, 247, 260, 832$ and $L = 14$ with $P = 14, 84, 112, 133, 1428$ (`rings --max-q 14`).

   The shift column is the least $k$ with state $k$ a rotation of state 0 by $s$ cells: all but the vacuum, the
   stripes, the ether and $L = 11, P = 17$ are patterns that travel toward cell 0.
2. **Without $K$, only the stripes and the ether hold the top** (computed; `sets`, `census`, every head of up to 12
   cells at every distinct alignment, 3,000 steps, 256 cells). The generalization of the closed strips of
   `defect_potential` (the greatest set of strips of $w$ cells below a cell $c$, with the defect zero above $c$, closed
   under one step for both values of the cell below and never raising the top above $c$) is nonempty only for the
   stripes ($w = 1$, 3 strips) and the ether ($w = 13$, 1,915 strips) among $w \le 14$. Its opposite, a *growing
   window*, is a set of windows of $w$ cells below the highest top so far, closed under one step for both values of the
   cell below, never losing the top, and with no cycle on which the highest top stays put; a defect whose window enters
   one has a top that grows without bound, whatever lies below, so its orbit is not eventually periodic. The census:

   | $L$ | $P$ | heads | closed strip | repeat | growing window (width) | top past cell 248 | open at step 3,000 |
   |---|---|---|---|---|---|---|---|
   | 1 | 1 | 4,096 | 0 | 1 | 4,095 (2) | 0 | 0 |
   | 2 | 1 | 8,192 | 8,192 | 0 | none | 0 | 0 |
   | 4 | 8 | 32,768 | 0 | 0 | 32,768 (2) | 0 | 0 |
   | 5 | 5 | 20,480 | 0 | 0 | 20,480 (2) | 0 | 0 |
   | 7 | 4 | 114,688 | 106,289 | 8,399 | none | 0 | 0 |
   | 7 | 63 | 258,048 | 0 | 16,387 | 86,140 (16) | 155,521 | 0 |
   | 8 | 40 | 163,840 | 0 | 0 | 163,840 (2) | 0 | 0 |
   | 9 | 72 | 294,912 | 0 | 0 | 294,912 (2) | 0 | 0 |
   | 9 | 171 | 700,416 | 0 | 0 | 699,739 (9) | 677 | 0 |
   | 10 | 15 | 122,880 | 0 | 0 | 122,880 (2) | 0 | 0 |
   | 11 | 17 | 765,952 | 0 | 21,906 | none up to 16 | 732,016 | 12,030 |
   | 11 | 154 | 630,784 | 0 | 0 | 630,662 (6) | 122 | 0 |
   | 12 | 3 | 49,152 | 0 | 16 | 49,136 (2) | 0 | 0 |
   | 12 | 102 | 1,671,168 | 0 | 195,984 | none up to 12 | 1,467,901 | 7,283 |

   The heads are counted over the distinct alignments. The growing window is the least width with one, tried up to
   12 cells (16 for $L = 7, P = 63$ and $L = 11, P = 17$; `--rise-width 16`). The only head of the vacuum that does
   not run away is the zero head, the integer 0. A head counted under "top past cell 248" left the cells followed
   without entering a growing window or repeating: its top is not proved unbounded. A head "open" has neither repeated
   nor left the cells in 3,000 steps.

   So on every background other than the stripes and the ether the tops of most defects run away: on 10 of the
   12 this is proved head by head by a growing window, for every head but 0.1% or fewer on 9 of them and for a third
   of the heads on $L = 7, P = 63$, and on the other two it is observed. A bounded top is proved only by a repeat, on
   the vacuum (the zero head) and on the backgrounds with $(L, P) = (7, 63), (11, 17), (12, 3)$ and $(12, 102)$. Over
   the heads of 12 cells the ether census here matches the one of `defect_potential` exactly (106,289 by a closed
   strip, 8,399 by a repeat, highest top 60).
3. **The fronts** (computed; `fronts`, 20 random heads of up to 12 cells per background, 6,000 steps). On the
   backgrounds with a growing window the top moves at a fixed rational speed: in the second half of every run,
   top$(t + k) - $top$(t)$ is one constant for a $k$ that is a multiple of $P$. The gain is $k$ per $k$ steps on the
   vacuum and on $L = 8, P = 40$ (speed 1), and the speed is 1/2 on $L = 4$, 1/3 on $L = 5$, 5/8 on $L = 9, P = 72$, 5/19 on $L = 9, P = 171$, 2/3 on $L = 10$, 3/14 on $L = 11, P = 154$ and
   2/5 on $L = 12, P = 3$, the same for all 20 heads. On $L = 7, P = 63$ two fronts occur, of speed 11/81 (14 heads)
   and 2/9 (6 heads). On $L = 11, P = 17$ no such $k$ exists in the run and the slope is between 0.138 and 0.162; on
   $L = 12, P = 102$ the heads show fronts of several speeds, some with periods of thousands of steps, between 0 (one
   head, bounded) and 0.235. On the nine backgrounds of $q = 13$ and 14 every run shows a front as well: speeds 1/7,
   8/19, 9/40 or 17/90, 3/5, 5/9, 11/40 or 5/8, and 8/19 where the run shows a period, and slopes 0.11 to 0.15 and
   0.26 to 0.27 on $L = 13, P = 832$ and $L = 14, P = 1428$, where it does not (`fronts --max-q 14`).
4. **With $K$, no head is a point of $K$ beyond the stripes and the ether** (computed; each head is a finite
   certificate, the odd step at which bit 0 of $H^t(U)$ is 0). With the condition of $K$ checked at every odd step,
   every head of up to 16 cells at every alignment of every background other than the stripes and the ether breaks
   $K$ (`census --bits 16 --k-only`, 75,431,936 heads on the 12 backgrounds). The last break is at step 29, 29, 31,
   41, 31, 41, 39, 33, 39, 35, 33 and 45 over the heads of 12 cells and 31, 37, 37, 43, 37, 47, 41, 43, 43, 43, 39 and
   45 over the heads of 16 cells, in the order of the table without the stripes and the ether. On the stripes and the
   ether the heads that do not break $K$ reach a periodic point of $K$ (8 and 26 of the heads of 12 cells, 12 and 34
   of the heads of 16 cells), a domain of the shift model; on no other background does a head of up to 16 cells reach
   one. The share of heads of 14 cells still in $K$ after step $t$ is 1/16 at $t = 8$, about $3.9 \times 10^{-3}$ at
   $t = 16$ and $1.1$ to $4.0 \times 10^{-4}$ at $t = 24$ on the vacuum and every front, and $1.5$ to
   $4.6 \times 10^{-5}$ at $t = 32$ on the nine fronts with at least 12 alignments (`survival --bits 14 --steps 48`):
   close to $2^{-t/2}$, a fair reading at every odd step. That the readings behave as independent coins is a
   heuristic, and on the vacuum it is the period-two question itself.

## What it means

For a rational point of $K$ whose tail falls onto the stripes or the ether, (R) is a statement about a bounded defect,
proved for the stripes in the kit and settled for the ether up to 20 cells ([the ether census](ether-defect-census.md)).
For every other background of spatial period at most 12, the tops of most defects run away at a positive speed:
a growing window proves it head by head for most heads on 9 of the 12 and for a third of them on $L = 7, P = 63$, and
on $L = 11, P = 17$ and $L = 12, P = 102$ it is observed only. So no bound on the top can give (R) on the 10
backgrounds with a growing window. For such a tail (R) says that every point of $K$ with it ends on a periodic point of
$K$ on that background, and none is reached from a head of up to 16 cells, so in that range (R) holds because $K$
misses these tails: every head breaks $K$ within 47 steps. This covers a tail that reaches the background only after
$\tau$ steps of the ring as well: for $U \in K$ and $\tau'$ the even one of $\tau, \tau + 1$, $H^{\tau'}(U)$ is in $K$
and has the background for tail from cell $p + \tau'$ on, so no such point of $K$ exists when $p + \tau' \le 16$. The search of
item 7 of the shift model says the same for every rational point of $K$ with preperiod $p$ and period $q \le 32$ with
$p + q \le 64$. Neither is a proof for longer heads, and the rate at which heads leave $K$ is that of the vacuum, where
the question is the period-two question. So the route of the ether census does not extend past the ether
([growing windows](../../negative-results/period-two/front-backgrounds.md)), and what remains of (R) for these tails is
a statement about $K$ alone, of the same kind as the period-two question.

The census of item 4 is a finite check, each head followed for at most 45 steps on numbers below $2^{64}$, and needs
no closed strip. For the backgrounds with $L = 4, 5, 10$ and $(L, P) = (12, 3)$ it covers 225,280 heads of 12 cells,
a smaller kernel computation than the census of [EtherCensus](../../Rule30Open/PeriodTwo/EtherCensus.md), and would
prove in Lean that no point of $K$ has one of these tails from cell 12 on; [NoKTails](../../Rule30Open/PeriodTwo/NoKTails.md)
does.

## Reproduce

```bash
python -m computations.tail_census rings --max-q 14                # about 2 minutes
python -m computations.tail_census sets --max-q 12                 # about 5 minutes
python -m computations.tail_census census --max-q 12 --bits 12     # about 40 minutes
python -m computations.tail_census census --max-q 7 --bits 12 --only 1010000 --rise-width 16   # about 10 minutes, 1.5 GB
python -m computations.tail_census sets --max-q 11 --only 10010100000 --rise-width 16 --closed-width 16
python -m computations.tail_census census --max-q 12 --bits 16 --k-only   # about 20 minutes
python -m computations.tail_census survival --max-q 12 --bits 14 --steps 48
python -m computations.tail_census fronts --max-q 14 --steps 6000  # about 10 minutes
```

`tests/test_tail_census.py` checks the backgrounds against `held_shift.cycle_class` and against the cycles of the
leftward column map of `space_time_periodic`, the stepping against the held map on whole integers, the closed strips
of the ether and its census against `defect_potential`, the closed strips and the growing windows against direct runs
with random cells below, the repeats against direct runs, and the breaks of $K$ against `in_k_steps`, which steps the
whole integer.
