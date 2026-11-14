---
title: The left step read in the depth direction gives an exact weight identity for three consecutive settled words but no density bound uniform in the period; for every K up to 8, K consecutive words that obey the step can have total weight independent of the period (2 for K = 3), while the single cell's settled words keep at least 9 of 48 cells black on every 3 consecutive diagonals of period 16
category: diagonals
problems: [2]
status: negative
kind: barrier
evidence: [computations/depth_register.py]
---

# The left step read in the depth direction gives an exact weight identity for three consecutive settled words but no density bound uniform in the period; for every K up to 8, K consecutive words that obey the step can have total weight independent of the period (2 for K = 3), while the single cell's settled words keep at least 9 of 48 cells black on every 3 consecutive diagonals of period 16

**Question.** On an eternal orbit of the left-edge frame ([EternalSkeleton](../../Rule30Open/Diagonals/EternalSkeleton.md)),
and in particular on the single cell's shadow, every left diagonal $W_d$ is periodic, and three consecutive ones,
aligned at a common period $P$, satisfy $W_d(t+1) = W_{d-2}(t) \oplus (W_{d-1}(t) \lor W_d(t))$. Read in the depth
direction, this step is a register: the pair $(W_{d-1}, W_d)$ determines the next word when $W_{d-1}$ is not white,
and leaves zero or two choices when it is ([settled words](../../findings/diagonals/settled-words.md)). Does the step
force a positive density of black cells, an inequality $|W_{d}| + \dots + |W_{d+K-1}| \ge cKP$ with $c > 0$ independent
of $P$? Such a bound on the shadow would be the first unconditional density statement on the regular side.

## The exact identity (proved on paper)

Write $|\cdot|$ for the number of black cells in one period. **For every $P$-periodic triple $(A, B, C)$ with
$C(t+1) = A(t) \oplus (B(t) \lor C(t))$,**

$$|A| + |B| = |B \land C| + 2\,|A \land (B \lor C)| .$$

*Proof.* Summing over a period, $\sum_t C(t+1) = |C|$. With $X = B \lor C$, $|A \oplus X| = |A| + |X| - 2|A \land X|$
and $|X| = |B| + |C| - |B \land C|$; so $|C| = |A| + |B| + |C| - |B \land C| - 2|A \land X|$.

Consequences, each exact for every eternal orbit and every depth:

- $|B \land C| \equiv |A| + |B| \pmod 2$, and $|A \land (B \lor C)| \le (|A| + |B|)/2$.
- If $B$ is white, $|A| = 2|A \land C|$ is even. So a white diagonal behind which the next solutions exist with the
  same period has a predecessor of even weight. This is the even case of the period dichotomy of
  [LeftMemory](../../Rule30Open/Diagonals/LeftMemory.md) (`D_period_dichotomy`): at odd weight the period doubles.
- If $C$ is white, $|A| + |B| = 2|A \land B|$, so $A = B$; if $B$ is all black, $|C| = P - |A|$.

`weight_identity` checks the identity on all 65,536 solving triples of period 8, and the test does so for $P \le 6$.

## The barrier: the step allows windows of bounded weight at every period (proved on paper, computed)

Call $K$ words $W_1, \dots, W_K$ of period $P$ a *window* if every three consecutive ones solve the step and no two
consecutive ones are white (two consecutive white diagonals never occur on an eternal orbit with a black frame cell:
read the step backward, `DoublingGaps.no_two_white` for the single cell).

**Localization lemma.** If a window of period $P_0$ has every word white at time $P_0 - 1$, the same integers form a
window at every period $P \ge P_0$. *Proof.* At times $0 \le t \le P_0 - 2$ the step reads the same bits. At times
$P_0 - 1 \le t \le P - 2$ every word is white at $t$ and $t + 1$. At $t = P - 1$ the step asks $C(0) = 0$, which is
the step at $t = P_0 - 1$ of the window of period $P_0$.

`window_min` finds the least total weight of a window by a pruned search over all words; the test checks it against
enumeration of every tuple at $P = 4$.

| $K$ | 3 | 4 | 5 | 6 | 8 |
|---|---:|---:|---:|---:|---:|
| least weight, $P = 6, 8, 10$ ($K = 8$: $P = 6, 8$) | 2 | 4 | 5 | 7 | 13 |
| a minimizer valid at every $P \ge 5$ (bits as binary numbers) | 1, 1, 0 | 11, 10, 10, 0 | | 101, 100, 110, 100, 100, 0 | 1011, 1110, 1010, 1000, 1100, 1000, 1000, 0 |

The minimizers in the last row are white at times $4, 5, \dots$, so by the lemma they are windows at every $P \ge 5$
(the test checks $5 \le P \le 40$). **So for $K = 3, 4, 6, 8$ the step and the rule against two white neighbors admit
$K$ consecutive words with a fixed number of black cells, and their density $m_K / (KP)$ tends to 0 with the period.**
No inequality $\sum |W| \ge cKP$ with $c > 0$ independent of $P$ follows from the step over any fixed number of
diagonals, as far as checked. A density bound for an eternal orbit must use which pairs are reachable from the frame
pair $(1, 1)$ through the pair map and the choices at white diagonals, a global property of the orbit, not the local
register.

## The single cell's settled words are far from these minimizers (computed)

`skeleton_weights` reads the single cell's settled words at period 16 (depths 0 to 53,200, from 82,000 steps; every
onset is at most 71,102). Over depths 400 to 53,200, the stretch of period 16 before the first non-doubling white
diagonal ends:

| $K$ | 1 | 2 | 3 | 4 | 6 | 8 |
|---|---:|---:|---:|---:|---:|---:|
| least weight of $K$ consecutive words | 1 | 5 | 9 | 16 | 26 | 37 |
| as a density | 0.0625 | 0.1562 | 0.1875 | 0.2500 | 0.2708 | 0.2891 |

A single diagonal can carry one black cell per period (as recorded in
[white-run potential](white-run-potential.md)), but three consecutive ones never fall below 9 of 48 here, against 2
for the register alone. The gap is the content a proof would have to capture; it is not explained here.

## The depth dichotomy (proved on paper)

Suppose that from depth $d_0$ on every diagonal of an eternal orbit has period dividing $p$. Fix, at each white
diagonal $w$ whose next word has two solutions $Y$ and $\lnot Y$, the bit saying which one the orbit takes (say, the
value at time 0).

1. **White diagonals recur.** Between two white diagonals the pairs follow the injective pair map from a pair with no
   preimage, so they are distinct ([settled words](../../findings/diagonals/settled-words.md)); there are at most
   $4^p$ aligned pairs, so consecutive white diagonals past $d_0$ are fewer than $4^p$ apart.
2. **Eventually periodic in depth exactly when the choices are.** The pair at depth $d + 1$ is a function of the pair
   at $d$ and, at white diagonals, of the choice bit. If the sequence of choice bits is eventually periodic with
   period $q$, the state (pair, index of the next white diagonal mod $q$) lives in a finite set and evolves
   deterministically, so the words are eventually periodic in depth. Conversely, the choice bit is read from two
   consecutive pairs, so eventually periodic words give eventually periodic choices.

So "the periods are unbounded, or the words are eventually periodic in depth" is not a theorem about eternal orbits:
a bounded-period orbit can take an arbitrary sequence of choices, if one with bounded period exists past its last
doubling (not known). For the single cell the choices are fixed by its transient (`D_shift_of_white`), and its periods
are unbounded (Nersissian 2026 in [the literature](../../literature/rule-30.md); the kit main branch's
`Rule30LeftUnbounded`, not in the pinned kit), so neither alternative bears on it.

In the eventually depth-periodic alternative (period $q$ in depth, $p$ in time), the settled cells form a doubly
periodic array in $(d, t)$, and along a ray $d = \lfloor \beta t \rfloor$ inside the settled region the frequency of
black cells exists for every $\beta$: an average over a finite orbit for rational $\beta$, and the average over one
$q \times p$ block for irrational $\beta$ (Weyl equidistribution of $\beta t$ modulo $q$, jointly with $t$ modulo $p$).

## What this means for the single cell's pattern

No density bound came out of the register, so nothing transfers. Had one held for the shadow, it would apply to the
cells of the single cell's pattern where the orbit equals its shadow: on diagonal $d$ from time $2^d - 1$ on
(`shadow_forward`, proved), a region of depth only about $\log_2 t$ at time $t$. A bound on the region of depth linear
in $t$ would need a linear onset bound, $T_d \le \lceil 3d/2 \rceil + 5$, which
[seed-uniform onsets](../../findings/diagonals/seed-uniform-onsets.md) checks for $d \le 76$ and conjectures for every
$d$.

## Reproduce

```bash
python -m computations.depth_register   # every table, about 20 s
```

`tests/test_depth_register.py` checks `next_words` against enumeration, the identity for $P \le 6$, `window_min`
against every tuple at $P = 4$, the transplanted minimizers for $5 \le P \le 40$, and the single cell's weights against
a direct run of rule 30 to depth 40.
