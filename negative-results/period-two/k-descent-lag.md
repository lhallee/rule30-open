---
title: A descent of the defect's top that uses K at a lag of about twice the top holds head length by head length to 40 cells, but each length is its own census
category: period-two
problems: [1]
status: negative
kind: dead-end
evidence: [computations/k_structure.py, computations/k_survivors.py]
---

# A descent of the defect's top that uses K at a lag of about twice the top holds head length by head length to 40 cells, but each length is its own census

**Question.** Let $H(U) = (U \gg 1) \oplus (U \lor (U \ll 1))$ be the held map and $K$ the set of 2-adic $U$ with
$H^t(U)$ odd at every odd $t$. Conjecture (E) of [the points of K with an ether tail](../../findings/period-two/k-ether-points.md)
says that these points are the 303 of a finite backward closure, and it would give conjecture (R) on the ether. Windows
at the top of the defect cannot bound it, and the condition of $K$ at a fixed lag removes none of their moves
([ether fronts](ether-front-windows.md), [BoundedLag](../../Rule30Open/PeriodTwo/BoundedLag.md)); the top of a point of
$K$ is not monotone either ([no monotone defect on K](k-ether-monotone.md)). The roadmap's next step is a statement that
uses $K$ at a lag growing with the top. The natural one is a descent.

**The statement tried.** For a head length $h$, let $\Lambda_c(h)$ say: every half whose cells from $h$ on are the ether
at some alignment and whose defect $D_0$ has exactly $h$ cells (its top at cell $h - 1$) either has bit 0 of $H^t$
equal to 0 at some odd $t \le c h$ (it is not in $K$), or has the top of its defect $D_t$ below cell $h - 1$ at some
even $t \le c h$. A point $U$ of $K$ with an ether tail and $p = h$ then has, at an even step, an image $H^t(U)$ that is
again in $K$, has an ether tail and has a shorter defect. So $\Lambda_c(h)$ for every $h \ge 33$, by descent on $h$,
brings every point of $K$ with an ether tail to one with $p \le 32$, where
[EtherKTree32](../../Rule30Open/PeriodTwo/EtherKTree32.md) proves (R) in Lean. The reduction is sound, and each
$\Lambda_c(h)$ is a finite check: the heads of $h$ cells that $K$ allows are the $2^{\lceil h/2 \rceil}$ leaves of its
tree per alignment, about half with $p = h$ exactly, and each is run for at most $c h$ steps.

**What was done** (`k_structure descent`, every alignment, every head on the tree of $K$, 21 to 40 cells, each run until
it breaks $K$ or descends, on rows of numpy words wide enough that every cell read is exact):

| $h$ | heads with $p = h$ | break $K$ (latest step) | descend (latest step) | resolved by | running at step $2h$ |
|---|---|---|---|---|---|
| 22 | 28,718 | 19,360 (81) | 9,356 (82) | 2 open at step 82 | 4 |
| 24 | 57,234 | 39,526 (87) | 17,698 (88) | 10 open at step 88 | 14 |
| 25 | 114,688 | 78,038 (49) | 36,650 (48) | $1.96 h$ | 0 |
| 28 | 229,142 | 156,029 (59) | 73,113 (58) | $2.11 h$ | 15 |
| 32 | 917,262 | 620,307 (67) | 296,955 (66) | $2.09 h$ | 18 |
| 35 | 3,670,016 | 2,476,782 (77) | 1,193,234 (76) | $2.20 h$ | 32 |
| 36 | 3,671,934 | 2,474,662 (73) | 1,197,272 (72) | $2.03 h$ | 38 |
| 38 | 7,338,130 | 4,964,114 (77) | 2,374,016 (76) | $2.03 h$ | 4 |
| 40 | 14,679,806 | 9,892,952 (79) | 4,786,854 (78) | $1.98 h$ | 0 |

The other lengths from 25 to 40 resolve by $1.97 h$ to $2.12 h$. Below 25 the heads still open at the end of the run are
points of $K$ in the closure of period 7 whose defect never falls below cell $h - 1$: they reach the periodic orbit
whose four points have preperiods 24, 24, 26 and 26 (2 such points at $h = 22$; 10 at $h = 24$, two of them on the
orbit). So $\Lambda_{2.2}(h)$ holds for $25 \le h \le 40$. The
points of $K$ themselves descend at once: the 314 points of the closure of period 7 with a preperiod of at least 27
have a shorter preperiod within 6 steps (250 at step 2). The heads that resolve late are heads outside $K$ that keep passing odd
steps.

**Where it stops.** Two numbers say why no single argument covers every $h$. About a third of the heads descend, most
within 8 steps, at every $h$; the other two thirds are removed only by breaks of $K$, at steps $h$ to about $2h$. A
head passes the odd steps below $h$ by construction and the next $h/2$ of them at the rate of a fair coin, so under the
model of independent coins (a heuristic), with $\lceil h/2 \rceil$ odd steps from $h$ to $2h$, about
$28 \cdot 2^{\lceil h/2 \rceil - 1} \cdot \tfrac{2}{3} \cdot 2^{-\lceil h/2 \rceil} = 28/3$, about 9, are still
running at step $2h$ for every $h$; the counted 0 to 38 (11 on average for $25 \le h \le 40$) are of that order. The lag must therefore
grow like $2h$ plus a term that does not shrink, every $\Lambda_c(h)$ with $c > 2$ is a census of $2^{h/2}$ heads, and
nothing found links $\Lambda_c(h)$ to $\Lambda_c(h - 1)$: the heads of $h$ cells that survive are not extensions of
those of $h - 1$ cells that survive, since the tree branches below the top and the tests read every cell. Asking that
no head of $h$ cells pass $h/2$ further odd tests, for every $h$, is the statement that $K$ misses the long heads on a
given tail, the same kind of statement as the period-two question on the vacuum
([the tail census](../../findings/period-two/tail-census.md), item 4). The descent gives a clean reduction of (R) on
the ether to an infinite family of finite censuses, checked to 40 cells, and no more.

```bash
python -m computations.k_structure descent --min-h 21 --max-h 40   # about 15 minutes
```
