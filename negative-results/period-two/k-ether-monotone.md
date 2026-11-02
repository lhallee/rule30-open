---
title: The defect of a point of K with an ether tail is not monotone, and proving that K has no long ether head is a question of the period-two kind
category: period-two
problems: [1]
status: negative
kind: dead-end
evidence: [computations/k_survivors.py]
---

# The defect of a point of K with an ether tail is not monotone, and proving that K has no long ether head is a question of the period-two kind

**Question.** Let $H(U) = (U \gg 1) \oplus (U \lor (U \ll 1))$ be the held map and $K$ the set of 2-adic $U$ with
$H^t(U)$ odd at every odd $t$. [The points of K with an ether tail](../../findings/period-two/k-ether-points.md) finds
that, for $p \le 56$, the points of $K$ whose cells from $p$ on are the ether are the points of a finite backward tree
of 303 points over four periodic orbits, and conjectures (E) that these are all of them, which would give conjecture
(R) for every ether tail. A proof for every head needs something that the condition of $K$ imposes on the defect
$D_t$ (the xor of $H^t(U)$ with the ether) and that stops it from climbing. Three candidates were tested.

**What was done.** Each candidate was tested on the 303 points of the closure, which are points of $K$ (each repeats
by step 36 after passing every odd step of its run, `k_survivors.settle`), and stopped at the first counterexample.

1. *The top of the defect of a point of $K$ never rises.* Refuted: 74 of the 303 points raise the top of their defect
   above its top at step 0 before they settle, 50 by one cell, 4 by two, 16 by three, 1 by four and 3 by five.
2. *The length $p$ of the defect does not grow under $H^2$*, a descent that would make the tree of item 3 of the finding
   the whole of $K$ with an ether tail. Refuted: 47 of the 303 points have $p(H^2 U) > p(U)$, 36 by one cell and 11 by
   two. The descent holds only on average: 52 keep $p$ and 204 lower it, by up to 16 cells.
3. *Every climbing cycle of the defect breaks $K$.* The window automaton at the top of the defect has cycles of
   positive gain ([the ether census](../../findings/period-two/ether-defect-census.md), item 3), and a climb that
   always broke $K$ soon after would bound the defect of every point of $K$. But bit 0 at step $t$ reads only the cells
   $0, \dots, t$ of $U$, so a change at the top cell $T$ of the defect reaches bit 0 no sooner than $T$ steps later:
   any such lemma has a lag that grows with the top, and at a bounded lag the condition of $K$ removes no transition of
   a top-window automaton ([ether fronts](ether-front-windows.md), proved in Lean in part). The climbs that do occur on
   points of $K$ (item 1) are short, but no window at the top tells them from the long climbs of halves outside $K$.

**Where it stops.** Without a monotone quantity, a proof of (E) has to show that no head longer than some bound passes
every odd step, the way [NoKTails16](../../Rule30Open/PeriodTwo/NoKTails16.md) shows it on the other backgrounds for
heads of up to 16 cells. The counts say what that takes: past the head a leaf of the tree of $K$ passes the odd steps
below 64 at the rate of a fair coin per step (28 times $2^{h - 32}$ leaves predicted; 112,948, 1,848,683, 29,374,858
and 470,028,972 counted at $h = 44, 48, 52, 56$, item 6 of the finding), so the heads leave $K$ at the rate they leave it on the
vacuum, where the statement that no head passes every odd step is the period-two question itself
([the tail census](../../findings/period-two/tail-census.md), item 4). A finite census proves (E) only up to its head,
as [EtherKTree32](../../Rule30Open/PeriodTwo/EtherKTree32.md) does for (R) at 32 cells.

**What it means.** The condition of $K$ does not act on the defect of an ether tail through any local or monotone
quantity found here: it acts through the odd steps at cell 0, as for the period-two question, and on the ether it is
satisfied by finitely many points as far as computed. The route to (R) on the ether through (E) is therefore a
statement of the same kind as the problem; what it gives is the form of a counterexample (its defect has more than 57
cells at every even step), not a proof.

```bash
python -m computations.k_survivors --head 24     # the closure of 303 points, a second
```
