---
title: No forced basin of the double-step game at a fixed width proves that every right half beside an alternating center enters the three closed sets
category: period-two
problems: [1]
status: negative
kind: barrier
evidence: [computations/three_set_game.py, computations/absorption.py]
---

# No forced basin of the double-step game at a fixed width proves that every right half beside an alternating center enters the three closed sets

**Idea.** Period two splits into a statement about the right half, that every finite right half beside an
alternating center enters the gap trap, the kit's ether-and-wall family for $0101$ or the lock of period seven, and
the kit's open `Q01Gap` ([the census](../../findings/period-two/gate-census.md)). A game argument would prove the right
statement at one width $W$: if from every state of the double-step game of $W$ columns every play enters the three
sets, whatever the cells beyond the window, then every right half enters. The forced basin of
[the three-set game](../../findings/period-two/three-set-game.md) is the set of states this argument covers, and it
grows from 35% of the states at 16 cells to 61% at 22.

**Where it stops.** The forced basin never holds every state, at any width, because of the family itself. Take the
kit's finite half `Rule30Ether.config` of depth $k \ge W$: the aligned ether on cells $1, \dots, k$, one of the kit's
wall states on cells $k + 1, \dots, k + 13$, white beyond. It is a member of the family from the start, and by the
kit's `config_pure_ether` its cells $1, \dots, k$ are the aligned ether at every step. So at every white step its
window of $W$ cells is one of the two windows of the aligned ether, with column 1 white (count 1) and black (count 0)
in turn (`three_set_game.ether_cycle`). This play enters none of the targets that a window of $W$ cells can certify:

- not the gap trap, since column 1 of the ether alternates, a gap of 2 between black cells;
- not the family, since a window certifies membership only with a wall state inside it, and the aligned ether has no
  wall state at any depth (`absorption.family_depth` is $-1$ on the periodic ether in both white phases, and the
  strip right of a $B_3$ column is the same at every depth $k = 6, 13, 20, \dots$);
- not the lock, whose column 1 repeats $0101000$ rather than alternating.

So the two states of the ether, and the starting states of these halves, lie outside the forced basin at every width,
although the halves are in the family. A game argument confined to a window misses every member of the family whose
depth is at least the width, and the family has members at every depth $k = 6, 13, 20, \dots$.

**The residue.** Outside the forced basin some move always stays outside, so the plays that avoid the three sets
forever end in strongly connected components of the states outside it that hold a cycle. Those components, from
`python -m computations.three_set_game basin`, at each width (size in consistent states, the gcd of their cycle
lengths, and whether column 1 is a function of the class modulo it):

| $W$ | states outside the basin | components | their states | unlocked components | locked components | the ether lies in |
|---:|---:|---:|---:|---|---|---|
| 16 | 127,172 | 3 | 2,695 | 2,650 (gcd 1) | 35 (gcd 16), 10 (gcd 8) | the 2,650 |
| 17 | 236,383 | 3 | 3,935 | 3,888 (gcd 1) | 36 (gcd 16), 11 (gcd 8) | the 3,888 |
| 18 | 438,368 | 2 | 5,782 | 5,772 (gcd 1) | 10 (gcd 8) | the 5,772 |
| 19 | 803,067 | 2 | 8,406 | 8,393 (gcd 1) | 13 (gcd 8) | the 8,393 |
| 20 | 1,473,713 | 2 | 11,717 | 11,707 (gcd 1) | 10 (gcd 8) | the 11,707 |
| 21 | 2,712,718 | 3 | 10,413 | 5,849 and 4,559 (gcd 1) | 5 (gcd 4) | the 4,559 |
| 22 | 4,965,270 | 2 | 15,322 | 8,975 and 6,347 (gcd 1) | none | the 6,347 |

The residue is about one state in a thousand at 22 cells, but every one of the 39% of the states outside the basin
leads into it under some play. Its unlocked components grow from 2,650 states at 16 cells to 15,322 at 22 and hold
the aligned ether at every width; on them column 1 is not a function of the class, so nothing in the game makes it
periodic there, as masked Jen would need. Of the
spatially periodic halves of [the three-set game](../../findings/period-two/three-set-game.md), 10,032 in each phase,
every one enters the three sets within 10,000 double steps except the aligned ether, so the residue holds no other
real infinite half that was found.

**What it means.** A proof of the right statement cannot be a forced basin at a fixed width with targets certified
inside the window: it has to use that a finite half is finite, as the white cells beyond a deep member's wall are
what make it a member. The test of reach, which the right statement passes to 26 cells, is the necessary side: a
refutation by a closed set that avoids the three sets cut to its window would need more than 26 cells. A target that
held the ether's windows themselves would need a closed set containing them on which column 1 stays periodic or keeps
its gaps at 3 and 5, whatever the cells beyond do; that is not tested here. The same obstacle, the chaotic cells
beyond the window having to deliver entry, stops [the absorption route](absorption-route.md) and the
[ether fronts](ether-front-windows.md).

**Reproduce.**

```bash
python -m computations.three_set_game basin --widths 16 17 18 19 20 21 22   # about 30 s
python -m computations.three_set_game halves --period 12 --random 100 --max-period 32 --double-steps 10000 --widths 16 18 20 22
```
