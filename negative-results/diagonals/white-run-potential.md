---
title: A potential that grows with the white runs does not turn the window bounds into a slope below 2 for every depth, and the step bounds the white runs only by the period; the window bounds grow linearly faster than 3j/2 while W_j is constant, a certificate that knows only the white runs needs slope 7/3, and words with one black cell per period occur at periods 4, 8 and 16
category: diagonals
problems: [2]
status: negative
kind: dead-end
evidence: [computations/settled_words.py, computations/seed_certificate.py]
---

# A potential that grows with the white runs does not turn the window bounds into a slope below 2 for every depth, and the step bounds the white runs only by the period; the window bounds grow linearly faster than 3j/2 while W_j is constant, a certificate that knows only the white runs needs slope 7/3, and words with one black cell per period occur at periods 4, 8 and 16

**Question.** [Seed finite certificate](seed-finite-certificate.md) shows that a certificate for the seed onsets with
a bounded potential needs the white runs of the settled diagonals bounded: one step can cost $c_n = g_n + 1$, with
$g_n$ the longest cyclic white run of the single cell's settled $D_n$. Two ways around it were tried:

1. a certificate whose potential may grow with $W_j = \max_{i \le j} g_i$, giving for every seed and every $j$
   $$T_j \le \gamma j + C + f(W_j), \quad f(W) = O(W);$$
2. a bound on $W_j$ from the step $D_{j+2}(t+1) = D_j(t) \oplus (D_{j+1}(t) \lor D_{j+2}(t))$ on the periodic parts,
   by the period or its logarithm, so that $W_j = O(\log j)$ and (1) gives onsets $\gamma j + O(\log j)$, which with the
   alternation hypothesis of [SettledSlope](../../Rule30Open/Diagonals/SettledSlope.md) gives black center runs of
   slope $3(\gamma - 1)/(5\gamma - 1)$.

Neither closes. The pieces that are proved, computed and conjectured are listed at the end.

## Route 1: the window bounds against $W_j$

The window abstraction of [seed window bounds](../../findings/diagonals/seed-window-bounds.md) gives, for each width
$h$, bounds $U_j \ge R_j$ and $V_j \ge T_j$ over every seed. `settled_words --fit` runs it (period 16, so to depth
87,866) and fits $V_j$ against $\gamma j + C + \kappa W_j$. On these depths $W_j$ is 7 from depth 63 to 406, 10 from
407 to 658 and 15 from 659 on, so a term $\kappa W_j$ can absorb at most $15\kappa$:

| Width $h$ | Slope of $U_j$, depths 63 to 398 (period 8) | 659 to 10,000 | 10,000 to 40,000 | 40,000 to 87,866 |
|---:|---:|---:|---:|---:|
| 0 | 1.9841 | 2.0310 | 2.0231 | 2.0217 |
| 2 | 1.6898 | 1.6839 | 1.7004 | 1.6946 |
| 4 | 1.5363 | 1.5995 | 1.6069 | 1.6026 |
| 6 | 1.5010 | 1.5650 | 1.5565 | 1.5518 |

The least $C$ with $V_j \le \gamma j + C + \kappa W_j$ for every $j \le 87{,}866$, for $\kappa = 0$ and $\kappa = 4$:

| Width $h$ | $\gamma = 3/2$ | $\gamma = 1.6$ | $\gamma = 1.7$ | $\gamma = 2$ | $\gamma = 2.05$ |
|---:|---:|---:|---:|---:|---:|
| 0 | 45,763 and 45,703 | 36,977 and 36,917 | 28,190 and 28,130 | 1,830 and 1,770 | 0 and 0 |
| 2 | 17,044 and 16,984 | 8,266 and 8,206 | 10 and 0 | 0 and 0 | 0 and 0 |
| 4 | 8,903 and 8,843 | 226 and 166 | 0 and 0 | 0 and 0 | 0 and 0 |
| 6 | 4,798 and 4,738 | 1 and 0 | 0 and 0 | 0 and 0 | 0 and 0 |

**The step where it stops.** Inside the regime of period 16 the white runs are constant ($W_j = 15$ from depth 659 to
87,866) while the slope of each bound stays flat over a hundredfold range of depths. So the excess of $V_j$ over
$\gamma j$ grows linearly for every $\gamma$ below the bound's own slope, and no term in $W_j$ absorbs it: what the fit
finds is $V_j \le \gamma_h j + C_h$ within a period regime, with $\gamma_h$ about 2.03, 1.70, 1.61 and 1.56 at $h = 0, 2, 4, 6$. From the regime of
period 8 to that of period 16 the slope rises at $h = 0$, 4 and 6 (by 0.04 to 0.05, 0.06 to 0.07 and 0.05 to 0.06) and not
at $h = 2$; the
period-8 stretch has only 336 depths. A form $\gamma j + C + f(W_j)$ fits the window bounds only with $\gamma$ at least
the largest slope of any regime, and the slope of the regimes of period 32 and beyond is not computed (the program
needs a common period of 16).

**A certificate that knows only the white runs needs slope 7/3.** Suppose a certificate may forget the words but its
transitions cover the step of the window abstraction of width $h \le 3$ from every pair of words of period $P$ whose
white runs are at most $W$, not only from the pairs that occur. The pair graph of period 4 has, for every $h \le 3$,
the cycle of three pair words $(1101, 1100) \to (1001, 0001) \to (0001, 0111)$ with increments 1, 4 and 2
([seed finite certificate](seed-finite-certificate.md)); its words have white runs at most 3, and words of period 4
are words of every period $P$ divisible by 4. So for $W \ge 3$ such a certificate has a cycle of mean $7/3$ and cannot
prove any $\gamma < 7/3$, whatever its potential. (A window of 4 times, a whole period of 4, breaks this cycle and
leaves mean $5/3$ at $P = 4$; at $P = 8$ the mean stays $7/3$ for $h \le 2$, the widths built.) A slope below $7/3$ must use which pairs occur,
and the pairs that occur are the path of the bijection $F$ of [settled words](../../findings/diagonals/settled-words.md),
which meets every word of period 16 up to rotation and never repeats a pair: the information a certificate would have
to carry grows with the depth, the stop of lead 3 in [linear settling leads](linear-settling-leads.md).

## Route 2: a bound on the white runs from the step

[RunTransfer](../../Rule30Open/Diagonals/RunTransfer.md) proves what a run forces on the diagonals before it: a white
run of $r + 1$ in $D_{j+2}$ is a white cell followed by $r$ times at which $D_j = D_{j+1}$, and a black run of $r + 1$ is
a black cell followed by $r$ white cells of $D_j$. So $g_{j+2} \le a_j + 1$ and $b_{j+2} \le g_j + 1$, with $a_j$ the
longest cyclic agreement run of $D_j$ and $D_{j+1}$, and to depth 200,000 equality holds at about a third of the
depths (65,855 and 66,140 of 199,999).

**The step where it stops.** The lemmas move a run to an agreement run or a white run of the same length one or two
diagonals back; nothing shortens it, and the agreement runs reach the whole period (two equal words; the largest
$a_j$ is 32 at period 32). The data rule out every bound below $P - 1$ for small periods: words with one black cell per
period, whose white run is $P - 1$, occur 3 times in the regime of period 4, 9 times in that of period 8 and 17 times
in the regimes of period 16 (`settled_words`, [settled words](../../findings/diagonals/settled-words.md)). So no bound
$g_j \le f(P_j)$ with $f(P) < P - 1$ holds at $P \le 16$, in particular none of order $\log P$. The proved bound is
$g_j \le P_j - 1 < 2^{\lfloor (j+5)/6 \rfloor}$ (the kit's main branch, `Rule30LeftAntiPeriod.D_evPer_pow_div_six`).

What the data show instead is statistical: the white runs follow the longest-run law of fair words of the period, and
$W_j$ stays within the 1% to 99% band of the fair-word model at every record, with $W_j < \log_2 j + 6$ for
$1 \le j \le 200{,}000$. On that model (a heuristic) $W_j$ is about $\min(P_j - 1, \log_2 j + \log_2 P_j)$, so
$W_j = O(\log j)$ would follow from two statements that are open: that the settled words behave like fair words for
their longest runs (a property of the chaotic transient that fixes them), and that $\log P_j = O(\log j)$ (the white
diagonals that double the period are sparse, [left records](../../findings/diagonals/left-records.md)).

## Status of the pieces

| Piece | Status |
|---|---|
| A white run of $D_{j+2}$ is a run of agreement of $D_j, D_{j+1}$; a black run is a white run of $D_j$; $c_{j+2} \le a_j + 2$ | proved in Lean ([RunTransfer](../../Rule30Open/Diagonals/RunTransfer.md)), for every row white left of a cell |
| $g_j \le P_j - 1 < 2^{\lfloor (j+5)/6 \rfloor}$ | proved (period bound of the kit's main branch) |
| The pairs of a regime are a path of a bijection from a source to a sink, distinct up to rotation | paper ([settled words](../../findings/diagonals/settled-words.md)); injectivity in the kit's main branch |
| Every seed has $T_j \le \lceil 8j/5 \rceil$ ($j \le 87{,}866$), $T_j \le \lceil 3j/2 \rceil + 5$ ($j \le 1{,}252$) | computed ([seed window bounds](../../findings/diagonals/seed-window-bounds.md)) |
| $V_j \le 2.05 j$ at $h = 0$, $V_j \le 1.7 j + 10$ at $h = 2$, $V_j \le 1.7 j$ at $h = 4$, $V_j \le 1.6 j + 1$ at $h = 6$, for $j \le 87{,}866$ | computed (table above) |
| $W_j < \log_2 j + 6$, white runs follow the fair-word law | computed to depth 200,000 |
| $W_j = O(\log j)$ | conjecture, with the fair-word heuristic |
| $T_j \le \gamma j + C + f(W_j)$ for every seed and $j$, some $\gamma < 7/3$ | open; not provable from white-run bounds alone (the cycle of mean $7/3$) |
| Seed-uniform onsets $3j/2 + O(\log j)$ and the conditional slope $3/13$ | conjecture; needs both open rows above and the alternation bound |

## Reproduce

```bash
python -m computations.settled_words --depth 200000                 # the words, runs and run lemmas, about 3 min
python -m computations.settled_words --depth 87866 --fit 0,2,4,6    # the window fit, about 13 min on two threads
python -m computations.seed_certificate --graph 4 --widths 0,1,2,3  # the cycle of mean 7/3, about 2 s
```
