---
title: A bounded defect top does not give (R) for the periodic tails of up to 12 cells beyond the stripes and the ether, since the tops run away, provably on 10 of the 12 backgrounds
category: period-two
problems: [1]
status: negative
kind: refuted
evidence: [computations/tail_census.py]
---

# A bounded defect top does not give (R) for the periodic tails of up to 12 cells beyond the stripes and the ether, since the tops run away, provably on 10 of the 12 backgrounds

**Idea.** For a rational 2-adic $U$ whose tail falls onto a background $B$ (a cycle of the ring map), item 5 of
[the shift model](../../findings/period-two/shift-model.md) turns (R) into a bounded top of the defect
$D_t = H^t(U) \oplus B_t$. On the stripes the kit bounds it for every head, and on the ether a closed strip of 13 cells
bounds it for every head of up to 20 cells ([the ether census](../../findings/period-two/ether-defect-census.md)). The
idea is to do the same on every other background: find closed strips, run the census, and settle (R) tail by tail
with no use of $K$.

**Where it stops.** On every other background that a tail of up to 12 cells reaches, the tops of most defects
run away ([the tail census](../../findings/period-two/tail-census.md)):

- No set of closed strips of up to 14 cells exists on any of them (`tail_census sets`).
- On 10 of the 12 there is a *growing window*: a set of windows of $w$ cells below the highest top so far ($w = 2$
  on the vacuum and the backgrounds of spatial period 4, 5, 8, 9 with temporal period 72, 10, and 12 with temporal
  period 3; $w = 6$ for $L = 11, P = 154$; $w = 9$ for $L = 9, P = 171$; $w = 16$ for $L = 7, P = 63$), closed under
  one step for both values of the cell below, that never loses the top and has no cycle on which the highest top stays
  put. A defect whose window enters one has a top that grows without bound whatever lies below, so its orbit is not
  eventually periodic. Of the heads of up to 12 cells at every alignment, all enter one on five of these backgrounds,
  all but the zero head on the vacuum, all but 677 of 700,416 on $L = 9, P = 171$, all but 122 of 630,784 on
  $L = 11, P = 154$ (those leave the 256 cells followed first), all but 16 of 49,152 on $L = 12, P = 3$ (those repeat),
  and 86,140 of 258,048 on $L = 7, P = 63$.
- On the other 2 ($L = 11, P = 17$ and $L = 12, P = 102$) no growing window of up to 16 and 12 cells exists, but the
  top of 96% and 88% of the heads passes cell 248 within 3,000 steps, at a mean speed between 0.14 and 0.24 cells per
  step; the rest repeat with a bounded top or stay open.

So the defect census proves only that these heads are not eventually periodic. For such a head (R) says that it is not
in $K$, and only the condition of $K$ can show that: it does for every head of up to 16 cells, each at a definite step,
but no bound on the top is involved. A proof of (R) for these tails is a proof that $K$ misses them, the same kind of
statement as the period-two question for the vacuum.

**Evidence.** `python -m computations.tail_census sets --max-q 12`, `census --max-q 12 --bits 12` (with
`--rise-width 16` for $L = 7, P = 63$) and `fronts --max-q 14 --steps 6000`; `tests/test_tail_census.py` checks the
growing windows against direct runs with random cells below.
