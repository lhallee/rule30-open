---
title: The right-edge cycle length L_n of the single cell doubles at 25 of the levels n ≤ 61 and reaches 2^25, about 2^(0.41 n); L_n / n unbounded, equivalently white runs W(2^m) = o(2^m) along a subsequence, is conjectured and would make Rule 30's diagram not 2-automatic
category: complexity
problems: [3]
status: conjecture
formalization: partial
evidence: [computations/two_index.py, tests/test_two_index.py]
---

# The right-edge cycle length L_n of the single cell doubles at 25 of the levels n ≤ 61 and reaches 2^25, about 2^(0.41 n); L_n / n unbounded, equivalently white runs W(2^m) = o(2^m) along a subsequence, is conjectured and would make Rule 30's diagram not 2-automatic

Read row $t$ of the single black cell leftward from its right edge as the binary number $\Phi^t(1)$,
$\Phi(x) = x \oplus (2x \lor 4x)$ (the kit's `TFunction`): bit $j$ is the cell $(t, t - j)$, on the right diagonal
$R_j$. Let $L_n$ be the cycle length of 1 under $\Phi$ modulo $2^n$. Then $L_n$ is the least period of $R_{n-1}$, and
of every $R_i$, $i < n$, together (the kit's `TFunctionCycles.seed_rows_return_iff` with
`Rule30RightPeriods.per_mono_all`); it is a power of two that doubles from level $n$ to $n + 1$ exactly when the input
$R_{n-1} \lor R_{n-2}$ of the next diagonal has an odd number of black cells in one cycle (the kit's
`TFunctionCycles.lift_iff`, `Rule30RightPeriods.e_step`). Let $W(2^m)$ be the number of white cells immediately left
of the right edge at time $2^m$.

## Result

1. **The cycle lengths** (computed, $n \le 61$). $L_n = 2^{a_n}$ with

   | $n$ | 1 | 2 | 4 | 5 | 7 | 8 | 10 | 16 | 17 | 25 | 26 | 28 | 30 | 35 | 37 | 38 | 40 | 42 | 44 | 49 | 50 | 52 | 55 | 56 | 59 | 61 |
   |---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
   | $a_n$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 |

   listing $n = 1$ and the 25 doubling levels; $a_n$ is constant between them. The longest run of levels without a
   doubling has 7 levels ($n = 18, \dots, 24$), $L_{61} = 2^{25}$, $a_{61}/61 = 0.410$, and
   $L_n / n$ is 6.4, 12.8, 136.5, 1,638.4, 20,971.5 and 550,072.7 at $n = 10, 20, 30, 40, 50, 61$. These are the
   right-diagonal periods of OEIS A094605.
2. **The white runs** (the kit's `Rule30RightPeriods.per_iff_gap`: $L_n \le 2^m$ if and only if $W(2^m) \ge n - 1$).
   For $m = 0, \dots, 24$, read off the cycle lengths,
   $$W(2^m) = 0, 2, 3, 5, 6, 8, 14, 15, 23, 24, 26, 28, 33, 35, 36, 38, 40, 42, 47, 48, 50, 53, 54, 57, 59,$$
   and the direct run of the integer rows gives the same values for $m \le 16$. So $W(2^m)/2^m$ falls from 0.75 at
   $m = 2$ to $59/2^{24} \approx 3.5 \cdot 10^{-6}$ at $m = 24$; $W(2^m)$ grows by about 2.5 per step of $m$ on average.
3. **Conjecture.** $L_n / n$ is unbounded. Equivalently, $W(2^m)/2^m$ has $\liminf$ 0: if $L_{j+1} = 2^{k+1} > C(j+1)$
   then $R_j$ does not have period $2^k$, so $W(2^k) < j$ and $W(2^k)/2^k < 2/C$; conversely a black cell on the
   diagonal $j + 1$ at time $2^k$ with $C(j + 1) < 2^k$ makes every period of $R_{j+1}$ at least $2^{k+1}$, more than
   $C(j + 2)$. The computed range supports it ($n \le 61$, $m \le 24$); nothing proves it. The kit bounds $L_n$ between
   a linear function (`Rule30RightPeriods.period_gt`, `per_bound`) and $2^{n/2 + O(\log^* n)}$ (`per_upper_half`), and its
   module docstring records numerically $e_j \approx 0.43 j$; so the conjecture asks for a lower bound past linear.
4. **Consequence** (Lean, [TwoIndex](../../Rule30Open/Complexity/TwoIndex.md)). If the conjecture holds, the array
   $(j, t) \mapsto \mathrm{cell}(t, t - j)$ of Rule 30 is not 2-automatic in two indices, while Rule 90's is; the
   white-run form is `rule30_twoIndex_not_recognizable_of_white_runs`.
5. **Mahler degrees** (computed, $j < 50$; item a on paper). On one least period $P_j = L_{j+1}$, write $R_j(t) =
   \sum_{k < P_j} a_k \binom{t}{k} \bmod 2$ and let $K_j$ be the largest $k$ with $a_k = 1$; then $P_j/2 \le K_j < P_j$ for $j \ge 1$ ($K_0 = 0$),
   since $\binom{t}{k}$ has period $2^{\lceil \log_2 (k + 1) \rceil}$ (Lucas).
   - (a) At every doubling level ($P_j = 2P_{j-1}$, $j \ge 1$), $K_j = P_j/2$ exactly. *Proof.* There $R_j$ is
     complemented by a shift of $P_j/2$ (the kit's `Rule30RightPeriods.leastExp_antiperiod`). By Lucas, a shift of $P/2$
     changes $\binom{t}{k}$ by $\binom{t}{k - P/2}$ for $P/2 \le k < P$ and not at all for $k < P/2$, so
     $\sum_{k \ge P/2} a_k \binom{t}{k - P/2} = 1$, which forces $a_{P/2} = 1$ and $a_k = 0$ for $k > P/2$.
   - (b) A doubling happens at the next level exactly when the coefficient $a_{P-1}$ of the input
     $R_j \lor R_{j-1}$ is 1, since $a_{P-1}$ is the parity of the black cells in one period.
   - (c) At the first level after a doubling that does not double again, $K_j \ge 3P_j/4 + 1$ in all 12 cases with
     $P_j \ge 8$ ($j = 5, 8, 10, 17, 26, 28, 30, 35, 38, 40, 42, 44$), with equality at $j = 5, 8, 17, 26, 38$; at the
     second such level $P_j - K_j \le 2$ in all 4 cases ($j = 11, 18, 31, 45$). After 6 of the 19 doublings at
     $j \le 48$ ($j = 3, 6, 15, 24, 36, 48$) the next level doubles again, so no climb is seen there.

   The climb of $K_j$ from $P_j/2$ toward $P_j$ is therefore an observation on these cases only, not a conjecture: at a
   third of the doublings in range the next doubling comes first, and the cases with a second level number four.

## Method

`computations/two_index.py` builds the diagonals by level lifting: $R_i(t)$ is the prefix XOR of its input
$R_{i-1} \lor R_{i-2}$ over one cycle, tiled twice when the input has odd weight, so each level is one numpy prefix XOR
and $n = 61$ takes about a second. The test checks the cycle lengths against iterating $\Phi$ modulo $2^n$ until 1
returns ($n \le 14$), the diagonals against a direct run of the rule table, and the white runs three ways (integer rows,
cycle lengths, rule table) for $m \le 7$. The Mahler coefficients come from the Möbius transform over the bits of $t$,
checked against a sum with `math.comb`.

## Reproduce

```bash
python -m computations.two_index
```

About nine seconds and 200 MB.
