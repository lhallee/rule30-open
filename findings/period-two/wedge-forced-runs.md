---
title: The kit's wedge hypotheses BWH and RW are statements about 2^n forced runs; no witness of BWH for 7 <= n <= 31 or of RW for n <= 26
category: period-two
problems: [1]
status: computed
formalization: partial
evidence: [computations/wedge_hypotheses.py, computations/wedge_hypotheses.c, Rule30Open/PeriodTwo/WedgeSmall.lean]
---

# The kit's wedge hypotheses BWH and RW are statements about 2^n forced runs; no witness of BWH for 7 <= n <= 31 or of RW for n <= 26

The kit's main branch reduces period two of the center column to open hypotheses on streams over four symbols
([WedgeSmall](../../Rule30Open/PeriodTwo/WedgeSmall.md) restates them): `BWH` says that for $n \ge 7$ and
$c \in \{2, 3\}$ no binary word $e_0 \dots e_{2n+1}$ (symbols 1 and 2) has wedge $W_n e(t) = c$ for all $t < n + 2$, and
`RW` is its rotated form, with a hard-core guard (no 1 after a 1 from position $n$), lengths $2n + r + 2$, $r \le 2$, and
the fixed symbols $e_{2n+r-1} = 1$, $e_{2n+r} = 2$. `BWH` with `SmallRW` excludes an eventual period two, and
WedgeSmall proves `SmallRW`. This entry is about `BWH` and `RW` for every $n$.

## Results

1. **Forced runs** (proved, `wedge_forced`). $\varphi(a, \cdot)$ is a bijection for each $a$; its rows for
   $a = 0, \dots, 3$ are $0132$, $3210$, $3201$, $3210$. So given $e_0, \dots, e_{k-1}$, $k \ge n$, exactly one of the
   four symbols gives $W_n e(k - n) = c$. The first $n$ symbols are free and every later one is forced: `BWH`$(n, c)$ and
   `RW`$(n, \cdot, c)$ are statements about $2^n$ forced runs, one from each binary prefix, each of which lasts while
   its forced symbols are binary (and, for `RW`, keep the guard). `wedge_hypotheses.c` follows all of them, by a backward
   pass that solves for the forced symbol through the antidiagonals of the cone.
2. **Edges** (the group is computed, the rest is proved on paper; counted). $\varphi(0, \cdot) = (2\,3)$, $\varphi(1, \cdot) = \varphi(3, \cdot) = (0\,3)(1\,2)$
   and $\varphi(2, \cdot) = (0\,3\,1\,2)$ generate the dihedral group of order 8 of the square $0 - 3 - 1 - 2$, and
   $\{1, 2\}$ is an edge of it. The map from $e_k$ to $W_n e(k - n)$ is a product of these permutations and of
   $\partial = (0\,3)(1\,2)$, so the two values on $e_k \in \{1, 2\}$ form an edge $E_k$, and a run survives step $k$ for
   $c$ exactly when $c \in E_k$. Over the 32,724 forced steps of the $2^{14}$ runs at $n = 14$ for $c = 2$ the edges
   $\{0, 3\}$, $\{1, 3\}$, $\{1, 2\}$, $\{0, 2\}$ occur 8156, 8228, 8158 and 8182 times, and over the 32,374 steps for
   $c = 3$ 8022, 7968, 8474 and 7910 times.
3. **Locality** (sampled). $I(t) = C(t, 0)$ depends on $e_j$ exactly for $\lfloor t/2 \rfloor \le j \le t$ (every $t < 8$,
   random words of four symbols), so $W_n e(t)$ never reads $e_j$ for $j < \lfloor t/2 \rfloor$.
4. **BWH** ($7 \le n \le 31$, every free prefix). No witness. The largest constant length $M(n, c)$ (the kit's
   `MaxHorizon`) stays below the horizon $n + 2$:

   | $n$ | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 |
   |---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
   | $M(n, 2)$ | 7 | 6 | 5 | 9 | 9 | 9 | 10 | 11 | 11 | 14 | 13 | 17 | 18 | 16 | 16 | 18 | 19 | 21 | 20 | 21 | 22 | 22 | 27 | 25 | 26 |
   | $M(n, 3)$ | 6 | 7 | 8 | 9 | 8 | 11 | 10 | 11 | 16 | 14 | 13 | 18 | 16 | 17 | 21 | 19 | 17 | 23 | 21 | 21 | 22 | 25 | 24 | 24 | 28 |
   | margin | 2 | 3 | 3 | 3 | 4 | 3 | 5 | 5 | 1 | 4 | 6 | 2 | 3 | 5 | 2 | 5 | 6 | 3 | 6 | 7 | 7 | 5 | 4 | 7 | 5 |

   (margin $= n + 2 - \max_c M(n, c)$). Below 7, `BWH` fails at $n = 5$ ($c = 3$, 2 witnesses, the kit's
   `small_bwh_control`) and $n = 6$ ($c = 2$, 3 witnesses) and holds for $n \le 4$. The survivors halve with each forced
   symbol: at $n = 30$ the ratios of successive counts are 0.500 to within 0.003 for the first 11 forced symbols for both
   values of $c$, as the edges of item 2 predict.
5. **RW** ($n \le 26$, every free prefix, $r \le 2$). No witness. With the guard the survivors shrink by about 0.40 per
   forced symbol (at $n = 26$, $c = 2$: 0.375 for the first, then 0.400 to 0.417 for the next nine), and the longest run past the
   free prefix is 15 and 15 symbols at $n = 26$ ($c = 2, 3$), against the $n + r + 2 \ge 28$ that a witness needs. The
   margin grows with $n$: the longest run is 4 symbols at $n = 7$, 9 and 8 at $n = 15$, and 15 and 15 at $n = 26$.
6. **Clumps and forgetting.** The deepest survivors come in clumps that differ only in their first few symbols: at
   $n = 15$, $c = 3$, the 18 runs that reach length 31 agree from position 5 on, and all die at $k = 31$, where
   $E_{31} = \{0, 2\}$. The head depth (the largest $f$ such that every binary head of length $f$ with a survivor's tail
   survives) of the survivors at the last three lengths a run reaches is at most 2 for $8 \le n \le 14$, at most 3 for
   $15 \le n \le 17$ and at most 5 for $18 \le n \le 24$ (`BWH`; 5 once, at $n = 23$), and for `RW` at most 2 for
   $10 \le n \le 12$ and at most 4 for $13 \le n \le 24$. The forgetting depth $f(n)$, the least $j$
   at which changing $e_j$ changes the wedge on $t < n + 2$ for at least half of 4000 random binary words, is 1, 2, 2,
   3, 3, 4, 5 at $n = 8, 12, 16, 20, 24, 28, 32$; changing $e_0$ changes it for 21.1%, 8.3%, 2.6%, 0.9%, 0.2%, 0.1% and
   0.1% of them.

**Heuristic** (not a proof). If each forced symbol were uniform on the four symbols, a run would survive a step with
probability $1/2$ for `BWH` and, with the guard, with growth rate $\phi/4 \approx 0.405$ ($\phi$ the golden ratio) for
`RW`. Then the expected number of `BWH` witnesses is $2^n \cdot 2^{-(n+2)} = 1/4$ for each $(n, c)$, counted with
multiplicity, and the sum over $n$ diverges; witnesses come in clumps of at least $2^{\text{head depth}}$ runs, so the
chance of a witness at a given $(n, c)$ is smaller than $1/4$ by the clump size, and whether that sum converges depends
on how fast the forgetting depth grows, which the data above (one step of $f$ per 4 to 8 steps of $n$) does not
settle. For `RW` the expected number of survivors at the horizon is about $2^n (\phi/4)^{n}$, which decays like
$0.81^n$, so the margin grows linearly; the longest runs observed (15 or 16 symbols for $23 \le n \le 26$) fall short of the $0.77n$
(17.6 to 19.9) of a clump-free fair coin, as clumps of $2^f$ runs predict. Item 2 is why the data match a fair coin: survival is the
membership of $c$ in an edge, and the edges occur about equally often (each within 5% of a quarter of the steps at
$n = 14$).

## Method

`wedge_hypotheses.py` builds the cone antidiagonal by antidiagonal (`Cone`): adding $e_k$ fills $C(t, k - t)$ for
$t \le k$ and the wedge diagonal $P^m I(k - m)$ for $m \le n$, each new entry $\varphi$ of an old entry and a newer one.
`Cone.forced` runs this backward from $W_n e(k - n) = c$ to the one $e_k$ that gives it. `forced_runs` follows every
free prefix by depth-first search; `wedge_hypotheses.c` does the same in C with OpenMP. The tests check the forced runs
against every binary word for $n \le 5$ by the kit's recursion one cone row at a time (`kit_wedge`), the kit's
`smallControl` by the kit's recursion as written, the C search against the Python one at $n = 8$, the edge census
against the run counts, and the flip profile against the recursion.

```bash
python -m computations.wedge_hypotheses --bwh 7 26          # item 4 to n = 26, about 30 s
python -m computations.wedge_hypotheses --bwh 27 31         # item 4 for n = 27 to 31, about 19 min on two cores
python -m computations.wedge_hypotheses --rw 1 26           # item 5, about 45 s
python -m computations.wedge_hypotheses --clumps 8 24 --rw-clumps 10 24   # item 6, about 30 s
python -m computations.wedge_hypotheses --edges 14          # item 2
python -m computations.wedge_hypotheses --flips 8 12 16 20 24 28 32   # item 6, f(n)
```

Items 1 and `SmallRW` are proved in [WedgeSmall](../../Rule30Open/PeriodTwo/WedgeSmall.md); a mechanism that kills the
survivors was looked for and not found ([no local mechanism](../../negative-results/period-two/wedge-survivor-mechanism.md)).
