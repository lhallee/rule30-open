---
title: The right-edge cycle length L_n of the single cell doubles at 36 of the levels n ≤ 84 and reaches 2^36, about 2^(0.43 n), and two exact parities decide whether a stall of the period lasts one diagonal, two, or more; L_n / n unbounded, equivalently white runs W(2^m) = o(2^m) along a subsequence, is conjectured and would make Rule 30's diagram not 2-automatic
category: complexity
problems: [3]
status: conjecture
formalization: partial
evidence: [computations/two_index.py, tests/test_two_index.py, computations/right_edge_runs.py, computations/right_edge_runs.c, tests/test_right_edge_runs.py]
---

# The right-edge cycle length L_n of the single cell doubles at 36 of the levels n ≤ 84 and reaches 2^36, about 2^(0.43 n), and two exact parities decide whether a stall of the period lasts one diagonal, two, or more; L_n / n unbounded, equivalently white runs W(2^m) = o(2^m) along a subsequence, is conjectured and would make Rule 30's diagram not 2-automatic

Read row $t$ of the single black cell leftward from its right edge as the binary number $h(t) = \Phi^t(1)$,
$\Phi(x) = x \oplus (2x \lor 4x)$ (the kit's `TFunction`): bit $j$ is the cell $(t, t - j)$, on the right diagonal $R_j$.
Let $L_n$ be the cycle length of 1 under $\Phi$ modulo $2^n$. Then $L_n$ is the least period of $R_{n-1}$, and of every
$R_i$, $i < n$, together (the kit's `TFunctionCycles.seed_rows_return_iff` with `Rule30RightPeriods.per_mono_all`); it is
a power of two that doubles from level $n$ to $n + 1$ exactly when the input $g_n = R_{n-1} \lor R_{n-2}$ of the next
diagonal has an odd number of black cells in one cycle (the kit's `TFunctionCycles.lift_iff`, `Rule30RightPeriods.e_step`),
where $R_j(t + 1) = R_j(t) \oplus g_j(t)$. Let $W(2^m)$ be the number of white cells immediately left of the right edge at
time $2^m$.

Write $P_j = L_{j+1}$ for the least period of $R_j$, and say that diagonal $j \ge 1$ *doubles* when $P_j = 2P_{j-1}$, that
is when $L$ doubles at level $j + 1$. Write $J_k = W(2^k)$: by the kit's `Rule30RightPeriods.per_iff_gap` it is the last
diagonal whose period divides $2^k$, so $L_n \le 2^k$ if and only if $J_k \ge n - 1$. The diagonals of least period
$2^{k+1}$ are $J_k + 1, \dots, J_{k+1}$; call them the *stall* at period $2^{k+1}$, of length $d_k = J_{k+1} - J_k$. Diagonal
$J_k + 1$ doubles and opens it. $\Phi$ is a bijection of the 2-adic integers, so $h(\tau) = \Phi^\tau(1)$ is defined for
every integer $\tau$; for $\tau < 0$ it is the single cell's past ([the seed's past](../frames/seed-past.md)).

## Result

1. **The cycle lengths** (computed, $n \le 84$). $L_n = 2^{a_n}$ with

   | $n$ | 1 | 2 | 4 | 5 | 7 | 8 | 10 | 16 | 17 | 25 | 26 | 28 | 30 | 35 | 37 | 38 | 40 | 42 | 44 |
   |---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
   | $a_n$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 |

   | $n$ | 49 | 50 | 52 | 55 | 56 | 59 | 61 | 64 | 65 | 67 | 70 | 71 | 73 | 75 | 78 | 80 | 81 | 83 |
   |---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
   | $a_n$ | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 | 32 | 33 | 34 | 35 | 36 |

   listing $n = 1$ and the 36 levels where $L$ doubles; $a_n$ is constant between them. The longest run of levels without
   a doubling has 7 levels ($n = 18, \dots, 24$), $L_{84} = 2^{36}$, $a_{84}/84 = 0.429$, and $L_n / n$ is 6.4, 12.8,
   136.5, 1,638.4, 20,971.5, 550,072.7, 7,669,584.5 and 818,089,008.8 at $n = 10, 20, 30, 40, 50, 61, 70, 84$. These are
   the right-diagonal periods of OEIS A094605.
2. **The white runs** (computed, $m \le 36$; the kit's `Rule30RightPeriods.per_iff_gap`: $L_n \le 2^m$ if and only if
   $W(2^m) \ge n - 1$). For $m = 0, \dots, 36$,
   $$W(2^m) = 0, 2, 3, 5, 6, 8, 14, 15, 23, 24, 26, 28, 33, 35, 36, 38, 40, 42, 47, 48, 50, 53, 54, 57, 59, 62, 63, 65, 68, 69, 71, 73, 76, 78, 79, 81, 83,$$
   by iterating $\Phi$ on 128-bit integers to time $2^{36}$, which is exact since $W(2^m) + 1 \le 84 < 128$; level lifting
   gives the same values for $m \le 26$, and Python integers for $m \le 16$. So $W(2^m)/2^m$ falls from 0.75 at $m = 2$ to
   $83/2^{36} \approx 1.2 \cdot 10^{-9}$ at $m = 36$; $W(2^m)$ grows by about 2.3 per step of $m$ on average. The stall
   lengths are
   $$d_k = 2, 1, 2, 1, 2, 6, 1, 8, 1, 2, 2, 5, 2, 1, 2, 2, 2, 5, 1, 2, 3, 1, 3, 2, 3, 1, 2, 3, 1, 2, 2, 3, 2, 1, 2, 2 \quad (k = 0, \dots, 35).$$
3. **Conjecture.** $L_n / n$ is unbounded. Equivalently, $W(2^m)/2^m$ has $\liminf$ 0: if $L_{j+1} = 2^{k+1} > C(j+1)$
   then $R_j$ does not have period $2^k$, so $W(2^k) < j$ and $W(2^k)/2^k < 2/C$; conversely a black cell on the diagonal
   $j + 1$ at time $2^k$ with $C(j + 1) < 2^k$ makes every period of $R_{j+1}$ at least $2^{k+1}$, more than $C(j + 2)$.
   The computed range supports it ($n \le 84$, $m \le 36$); nothing proves it. The kit bounds $L_n$ between a linear
   function (`Rule30RightPeriods.period_gt`, `per_bound`) and $2^{n/2 + O(\log^* n)}$ (`per_upper_half`), and its module
   docstring records numerically $e_j \approx 0.43 j$; so the conjecture asks for a lower bound past linear. Where each
   route toward one stops is in [the routes to L_n / n unbounded](../../negative-results/complexity/right-edge-cycle-routes.md).
4. **Consequence** (Lean, [TwoIndex](../../Rule30Open/Complexity/TwoIndex.md)). If the conjecture holds, the array
   $(j, t) \mapsto \mathrm{cell}(t, t - j)$ of Rule 30 is not 2-automatic in two indices, while Rule 90's is; the
   white-run form is `rule30_twoIndex_not_recognizable_of_white_runs`.
5. **Mahler degrees** (paper: (a) and (c); computed: the cases listed, $j \le 65$). On one least period $P_j$, write
   $R_j(t) = \sum_{k < P_j} a_k \binom{t}{k} \bmod 2$ and let $K_j$ be the largest $k$ with $a_k = 1$; then
   $P_j/2 \le K_j < P_j$ for $j \ge 1$ ($K_0 = 0$), since $\binom{t}{k}$ has period $2^{\lceil \log_2 (k + 1) \rceil}$
   (Lucas). Write $v_j = P_j - 1 - K_j$; it is the kit's difference order of $R_j$ at its period
   (`Rule30DifferenceOrder.order`).
   - (a) At every doubling diagonal $j \ge 1$, $K_j = P_j/2$ exactly (the pinned kit's
     `Rule30DifferenceOrder.order_of_antiperiod` with `Rule30RightPeriods.antiperiod`), and at every other diagonal
     $j \ge 3$, $K_j > P_j/2$. Diagonal 2 is the exception: $K_2 = 1 = P_2/2$ and it does not double.
   - (b) A doubling happens at the next diagonal exactly when the coefficient $a_{P-1}$ of the input
     $R_j \lor R_{j-1}$ is 1, since $a_{P-1}$ is the parity of the black cells in one period.
   - (c) **The diagonal after a doubling** (Theorem A; the kit's main branch). If diagonal $i \ge 3$ doubles, diagonal
     $i + 1$ doubles if and only if $R_{i-1}$ has an odd number of black cells in one period, that is $v_{i-1} = 0$; if
     it does not, $K_{i+1} = P_i/2 + K_{i-1} + 1$, that is $v_{i+1} = v_{i-1} - 1$. With (a): at the first diagonal $j$
     after a doubling that does not double again, $K_j \ge 3P_j/4 + 1$ whenever $P_j \ge 8$, with equality if and only
     if diagonal $j - 2$ doubles as well. In the computed range these are the 18 diagonals
     $j = 5, 8, 10, 17, 26, 28, 30, 35, 38, 40, 42, 44, 50, 52, 56, 59, 61, 65$, with equality at
     $j = 5, 8, 17, 26, 38, 50, 56, 65$. After 8 of the 27 doublings at $j \le 64$ ($j = 3, 6, 15, 24, 36, 48, 54, 63$)
     the next diagonal doubles again.
   - (d) At the second diagonal after a doubling, when neither it nor the first doubles, $P_j - K_j$ is 1, 2, 1, 2, 1,
     4, 1 at $j = 11, 18, 31, 45, 53, 57, 62$, the seven cases with $j \le 65$: the bound $P_j - K_j \le 2$ of the four
     cases $j \le 45$ fails at $j = 57$. Theorem B below gives $K_j$ there exactly. At the non-doubling diagonals
     $j \le 65$ that are not first after a doubling, $0 \le v_j \le 4$; at the first ones $v_j$ counts down by one per
     doubling along alternating runs, as Theorem A says (8190, 8189, 8188, 8187 at $j = 38, 40, 42, 44$).
6. **The anatomy of a stall** (paper; checked for $k \le 25$, every diagonal $j \le 65$). For every $k \ge 1$, with
   $i = J_k + 1$ the doubling diagonal that opens the stall, $H = 2^k$ and $D_{i+1}(t) = R_{i+1}(t + H) \oplus R_{i+1}(t)$:
   - $d_k = 1$ if and only if $R_{J_k}$ has an odd number of black cells in one period $2^k$ (Theorem A);
   - $d_k = 2$ if and only if that number is even and
     $\sum_{t < H} R_{i+1}(t) + \sum_{t < H} R_i(t)\, D_{i+1}(t)$ is odd (Theorem B);
   - otherwise $d_k \ge 3$, and whether each diagonal $J_k + 3, \dots, J_{k+1} + 1$ doubles is the parity of the black
     cells of $\Gamma = g(\cdot + H) \oplus g$ in $H$ for its input $g$ (Lemma 2): a hovering run.

   ($d_0 = 2$ is the exception: the stall at period 2 opens at diagonal 1, before Theorem A applies.) On
   $1 \le k \le 35$: $d_k = 1$ at 10 periods ($k = 1, 3, 6, 8, 13, 18, 21, 25, 28, 33$), $d_k = 2$ at 16, and $d_k \ge 3$
   at 9 ($k = 5, 7, 11, 17, 20, 22, 24, 27, 31$, with $d_k = 6, 8, 5, 5, 3, 3, 3, 3, 3$); $d_k \le 3$ for every
   $k \ge 18$. The two parities give $d_k$ at every $k \le 25$, and in the hovering runs with $j \le 65$ every order $v_j$
   lies between 0 and 4.
7. **The agreement identity** (paper, Theorem C). For integers $a \ne b$, the rows $h(a)$ and $h(b)$ agree on exactly the
   diagonals $0, \dots, J_{v_2(a - b)}$:
   $$v_2\big(h(a) - h(b)\big) = J_{v_2(a - b)} + 1, \qquad \text{in particular} \qquad J_{k+1} + 1 = v_2\big(h(2^k) - h(-2^k)\big).$$
   The rows at times $2^k$ and $-2^k$ both end in $1\,0^{J_k}\,1$ read from the right edge and agree on exactly
   $J_{k+1} + 1$ cells, so $d_k - 1$ is the length of their agreement beyond that common end. Checked for $k \le 34$ on the
   run to $2^{36}$, and for every pair $a, b \in [-24, 24]$ by inverting $\Phi$ bit by bit.
8. **A relative sufficient lemma** (paper, Proposition D). If $J_{k+1} \le \lambda J_k + C$ for some $\lambda < 2$, some
   $C$ and every large $k$, then $L_n \ge c\, n^{1/\log_2 \lambda}$ for some $c > 0$ and every $n$ (and $L_n$ grows
   exponentially if $\lambda = 1$), so $L_n / n$ is unbounded. On the computed range $J_{k+1} \le 1.75\, J_k$ for
   $1 \le k \le 35$ (equality at $k = 5$, $J_6 / J_5 = 14/8$), and $d_k \le 0.06\, J_k$ for $18 \le k \le 35$ (equality at
   $k = 20$). The constant 2 cannot be reached: $J_{k+1} \le 2J_k$ allows $J_k$ of order $2^k$, that is $L_n$ of order $n$.
   With item 7 the hypothesis reads $v_2(h(2^k) - h(-2^k)) \le \lambda\, v_2(h(2^k) - 1) + C'$.

## Proofs

**Facts used.** For $f$ of period $P = 2^e$ write $f(t) = \sum_{k < P} a_k(f) \binom{t}{k} \bmod 2$ and $K(f)$ for the
largest $k$ with $a_k(f) = 1$. By Lucas $\binom{t}{k}$ is odd if and only if every binary digit of $k$ is a digit of $t$,
so $a_k(f)$ is the sum of $f(s)$ over the $s$ whose digits are digits of $k$, and:

- (F1) $f$ has period $2^b$, $b \le e$, if and only if $K(f) < 2^b$;
- (F2) $a_{P-1}(f)$ is the parity of $\sum_{t < P} f(t)$;
- (F3) if $g$ has period $P$ and an even number of black cells in a period, then $Sg(t) = \sum_{s < t} g(s) \bmod 2$ has
  period $P$ and $a_{k+1}(Sg) = a_k(g)$, so $K(Sg) = K(g) + 1$ for $g \ne 0$ (since
  $\sum_{s < t} \binom{s}{k} = \binom{t}{k+1}$).

From the pinned kit: $R_j(t + 1) = R_j(t) \oplus g_j(t)$ (`Rule30Diagonals.R_step`), and in `Rule30RightPeriods`, a
doubling diagonal $j$ has $R_j(t + P_{j-1}) = \lnot R_j(t)$ (`antiperiod`); for $j \ge 3$ every period of $g_j$ is a
multiple of $P_{j-1}$ (`inp_least_period`), and diagonal $j$ doubles if and only if $g_j$ has an odd number of black
cells in $P_{j-1}$ (`S_rule`); $P_j$ is $P_{j-1}$ or $2P_{j-1}$ (`e_step`); $R_j(t) = 0$ for $2t < j$ and
$R_j(\lceil j/2 \rceil) = 1$ for $j \ge 1$ (`R_lt`, `R_half`). The doubling diagonals are $1, 3, 4, 6, 7, \dots$:
diagonal 2 does not double, so a doubling diagonal $i \ge 2$ has $i \ge 3$.

**Lemma 1 (top-bit decomposition).** Let $f$ have period $P = 2H \ge 2$ and put $Df(t) = f(t + H) \oplus f(t)$, of
period $H$. Then $a_{H + k}(f) = a_k(Df)$ for $0 \le k < H$, the right side taken on $\mathbb{Z}/H$. So $f$ has period
$H$ if and only if $Df = 0$; otherwise $K(f) = H + K(Df)$; and $K(f) = H$ if and only if $f(t + H) = \lnot f(t)$ for
every $t$.

*Proof.* For $0 \le t < H$ and $k < H$, Lucas gives $\binom{t + H}{k} \equiv \binom{t}{k}$ ($k$ has no digit $H$),
$\binom{t}{H + k} \equiv 0$ and $\binom{t + H}{H + k} \equiv \binom{t}{k}$. Subtracting the expansions at $t + H$ and $t$
gives $Df(t) = \sum_{k < H} a_{H+k}(f) \binom{t}{k}$ for $0 \le t < H$, which is the expansion of $Df$ on $\mathbb{Z}/H$.
Then $Df = 0$ if and only if $a_k(f) = 0$ for every $k \ge H$, that is (F1) period $H$; and $K(Df) = 0$ with $Df \ne 0$
means $Df \equiv 1$. $\square$ The kit's `Rule30DifferenceOrder.difs_two_pow` and `difs_add` state the same in difference
form: the $H$-th difference of $f$ is $Df$.

**Item 5(a).** Let $j \ge 1$. $R_j$ does not have period $P_j/2$, so $K_j \ge P_j/2$ by (F1). If $j$ doubles,
`antiperiod` and Lemma 1 give $K_j = P_j/2$. If $j \ge 3$ does not double and $K_j = H = P_j/2$, Lemma 1 gives
$R_j(t + H) = \lnot R_j(t)$ for every $t$, so $g_j(t) = R_j(t + 1) \oplus R_j(t)$ has the period $H = P_{j-1}/2$, against
`inp_least_period`. $\square$

**Theorem A (the diagonal after a doubling).** Let diagonal $i \ge 3$ double, $H = P_{i-1}$, $P = P_i = 2H$.

- (i) Diagonal $i + 1$ doubles if and only if $\sum_{t < H} R_{i-1}(t)$ is odd, if and only if $K_{i-1} = H - 1$, that is
  $v_{i-1} = 0$.
- (ii) If it does not, then $D_{i+1}(t) = R_{i+1}(t + H) \oplus R_{i+1}(t)$ is $R_{i+1}(H) \oplus S(\lnot R_{i-1})$, and
  $K_{i+1} = H + K_{i-1} + 1$, that is $v_{i+1} = v_{i-1} - 1$.

*Proof.* `antiperiod` gives $R_i(t + H) = \lnot R_i(t)$, and $R_{i-1}$ has period $H$. For bits,
$(\lnot a \lor b) \oplus (a \lor b) = \lnot b$, so $g_{i+1}(t + H) \oplus g_{i+1}(t) = \lnot R_{i-1}(t)$. Hence the number
of black cells of $g_{i+1}$ in $P$ has the parity of $\sum_{t < H} \lnot R_{i-1}(t) = H - \sum_{t < H} R_{i-1}(t)$, and
$H \ge 2$ is even; with `S_rule` at $i + 1 \ge 4$ this is the first equivalence of (i), and (F2) with (F1) gives the
others. For (ii), $D_{i+1}(t + 1) \oplus D_{i+1}(t) = \lnot R_{i-1}(t)$ gives $D_{i+1} = R_{i+1}(H) \oplus S(\lnot R_{i-1})$.
Now $\lnot R_{i-1}$ has an even number of black cells in $H$, and it is not constant ($i - 1 \ge 2$, `R_lt`, `R_half`), so
$K(\lnot R_{i-1}) = K_{i-1} \ge 1$ and, by (F3), $K(D_{i+1}) = K_{i-1} + 1$. $R_{i+1}$ has least period $P$ (`e_step`),
so Lemma 1 gives $K_{i+1} = H + K_{i-1} + 1$. $\square$

In the kit's main branch at commit
[368d1c7](https://github.com/WolframInstitute/Rule30PrizeKit/blob/368d1c7ff515f940cf4efa82f4dd893985833d9a/lean/Ruliology/CellularAutomata/Rule30ClosingLaw.lean),
(ii) is `Rule30ClosingLaw.order_countdown_exact_or` and the converse half of (i) is
`not_period_two_mul_of_order_zero_or` (with `order_pos_of_period`), on the gate laws of
[`Rule30GateClocks`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/368d1c7ff515f940cf4efa82f4dd893985833d9a/lean/Ruliology/CellularAutomata/Rule30GateClocks.lean)
(`dif_shift_sum_gate`); the pinned kit has the forward half of (i), `Rule30DifferenceOrder.order_reset_before`, and the
inequality $v_{i-1} \le v_{i+1} + 1$, `order_countdown`.

**Item 5(c), the bound.** Let $i \ge 3$ double and $i + 1$ not. Diagonal 4 doubles, so $i \ge 4$ and $i - 1 \ge 3$, and
by (a) $K_{i-1} \ge P_{i-1}/2$ with equality if and only if $i - 1$ doubles. Theorem A(ii) gives
$K_{i+1} = H + K_{i-1} + 1 \ge 3H/2 + 1 = 3P_{i+1}/4 + 1$ with $H = P_{i-1}$, and equality if and only if $i - 1$ doubles.
The only first diagonal after a doubling with $P_j < 8$ is $j = 2$, after diagonal 1. $\square$

**Lemma 2 (half-period differences in a stall).** Let diagonal $m \ge 3$ double, $P = P_m = 2H$, and let $i \ge m + 1$
with $P_{i-1} = P$. For every diagonal $l$ whose period divides $P$ put $D_l(t) = R_l(t + H) \oplus R_l(t)$ (so $D_l = 0$
when $P_l$ divides $H$, and $D_m \equiv 1$), and put $\Gamma_i(t) = g_i(t + H) \oplus g_i(t)$. Then

- (a) $\Gamma_i = D_{i-1}(1 \oplus R_{i-2}) \oplus D_{i-2}(1 \oplus R_{i-1}) \oplus D_{i-1} D_{i-2}$;
- (b) $\Gamma_i$ has period $H$, and diagonal $i$ doubles if and only if $\sum_{t < H} \Gamma_i(t)$ is odd;
- (c) if diagonal $i$ does not double, then $D_i = R_i(H) \oplus S\Gamma_i$, $\Gamma_i \ne 0$, and
  $K_i = H + 1 + K(\Gamma_i)$, $K(\Gamma_i)$ taken on $\mathbb{Z}/H$.

*Proof.* (a) For bits, $((a \oplus x) \lor (b \oplus y)) \oplus (a \lor b) = x(1 \oplus b) \oplus y(1 \oplus a) \oplus xy$
(expand $p \lor q = p \oplus q \oplus pq$ on both sides); apply it with $a = R_{i-1}(t)$, $b = R_{i-2}(t)$,
$x = D_{i-1}(t)$, $y = D_{i-2}(t)$, since $R_l(t + H) = R_l(t) \oplus D_l(t)$. (b) $g_i$ has period $P$, so
$\Gamma_i(t + H) = \Gamma_i(t)$, and the number of black cells of $g_i$ in $P$ has the parity of $\sum_{t < H}(g_i(t) +
g_i(t + H))$, that is of $\sum_{t < H} \Gamma_i(t)$; apply `S_rule`. (c) $D_i(t + 1) \oplus D_i(t) = \Gamma_i(t)$ and
$D_i(0) = R_i(H)$, so $D_i = R_i(H) \oplus S\Gamma_i$. If $\Gamma_i = 0$, $g_i$ has period $H < P_{i-1}$, against
`inp_least_period`. By (b) $\Gamma_i$ has an even number of black cells in $H$, so $K(D_i) = K(\Gamma_i) + 1 \ge 1$ by
(F3), and $R_i$ has least period $P$, so $K_i = H + K(D_i)$ by Lemma 1. $\square$

At $i = m + 1$, where $D_{i-1} = D_m \equiv 1$ and $D_{i-2} = 0$, this is Theorem A.

**Theorem B (the second diagonal after a doubling).** Let diagonal $i \ge 3$ double and $i + 1$ not, $P = P_i = 2H$.
Then diagonal $i + 2$ doubles if and only if $\sum_{t < H} R_{i+1}(t) + \sum_{t < H} R_i(t) D_{i+1}(t)$ is odd; if it does
not, $K_{i+2} = H + 1 + K(\Gamma)$ with $\Gamma = \lnot R_{i+1} \oplus R_i D_{i+1}$ on $\mathbb{Z}/H$.

*Proof.* Lemma 2(a) at $i + 2$, with $D_i \equiv 1$, gives
$\Gamma_{i+2} = D_{i+1}(1 \oplus R_i) \oplus (1 \oplus R_{i+1}) \oplus D_{i+1} = \lnot R_{i+1} \oplus R_i D_{i+1}$. Its
number of black cells in $H$ has the parity of $H + \sum R_{i+1} + \sum R_i D_{i+1}$, and $H$ is even; apply Lemma 2(b)
and (c). $\square$

With $D_{i+1} = R_{i+1}(H) \oplus S(\lnot R_{i-1})$ (Theorem A) and $R_{i+1} = S g_{i+1}$, the parity of Theorem B is a
function of $R_i$ on $[0, H)$ and of $R_{i-1}$ alone; all four combinations of its two sums occur for $j \le 65$.

**Item 6.** Let $k \ge 1$; then $i = J_k + 1 \ge 3$ doubles and $P_i = 2^{k+1}$, $P_{i-1} = 2^k = H$. The stall has
$d_k = 1$ if and only if $i + 1$ doubles, which is Theorem A(i) with $R_{i-1} = R_{J_k}$. Otherwise $d_k = 2$ if and only
if $i + 2$ doubles, which is Theorem B. Otherwise the diagonals $i + 1$ and $i + 2$ do not double, and Lemma 2(b)
decides each later diagonal of period $P_i$ and the one that ends the stall. $\square$

**Item 7 (Theorem C).** $\Phi$ is a bijective isometry of the 2-adic integers: bit $j$ of $\Phi(y)$ is $y_j$ plus a
function of lower bits (the kit's `Rule30Equivalents.Odometer`, `G_bijective` and `agree_G_iff`). So
$v_2(\Phi(x) - \Phi(y)) = v_2(x - y)$, and the same holds for every power $\Phi^b$, $b \in \mathbb{Z}$. Hence
$v_2(h(a) - h(b)) = v_2\big(\Phi^b(h(a - b)) - \Phi^b(h(0))\big) = v_2(h(a - b) - 1)$, and by symmetry we may take
$\tau = a - b > 0$, $\tau = 2^k u$ with $u$ odd. The kit's `Rule30RightPeriods.rows_at_powers_of_two` says that row
$2^k u$ reads $1\,0^J\,1$ leftward from its right edge, where $J$ is the last diagonal of period $2^k$, that is $J_k$
(`per_iff_gap`). So $v_2(h(\tau) - 1) = J_k + 1$. The case $a = 2^k$, $b = -2^k$ has $v_2(a - b) = k + 1$. $\square$

**Item 8 (Proposition D).** For $\lambda > 1$, $J_k + C/(\lambda - 1)$ grows at most by the factor $\lambda$ per step
for $k \ge k_0$, so $J_k \le A \lambda^k$ for some $A$ and every $k$. $L_n = 2^{k(n)}$ with $k(n)$ the least $k$ with
$J_k \ge n - 1$ (`per_iff_gap`), so $n - 1 \le A \lambda^{k(n)}$ and $L_n \ge ((n - 1)/A)^{1/\log_2 \lambda}$, and
$1/\log_2 \lambda > 1$. For $\lambda = 1$, $J_k \le A + Ck$ and $L_n \ge 2^{(n - 1 - A)/C}$. $\square$

## In the kit

The pinned kit (commit 932cf8d) has item 5(a) at the doubling diagonals (`Rule30DifferenceOrder.order_of_antiperiod`
with `Rule30RightPeriods.antiperiod`), the forward half of Theorem A(i) (`order_reset_before`) and the inequality of
Theorem A(ii) (`order_countdown`), Lemma 1 in difference form (`difs_two_pow`, `difs_add`), and the facts the proofs
use. Its main branch at commit 368d1c7 has Theorem A in full (`Rule30ClosingLaw.order_countdown_exact_or`,
`not_period_two_mul_of_order_zero_or`), the count of the orders along alternating runs of doublings (`closing_run`,
`closing_law_or`; the countdown 8190, 8189, 8188, 8187 of item 5(d)) and `no_1101011`. Neither has the strict
inequality of item 5(a) at non-doubling diagonals (two lines from Lemma 1 and `inp_least_period`), Lemma 2 past the
first diagonal of a stall, Theorem B, the anatomy of item 6, the agreement identity, Proposition D, or the data past
$n = 61$.

## Method

`computations/two_index.py` builds the diagonals by level lifting: $R_i(t)$ is the prefix XOR of its input
$R_{i-1} \lor R_{i-2}$ over one cycle, tiled twice when the input has an odd number of black cells, so each level is one
numpy prefix XOR and $n = 61$ takes about a second. The test checks the cycle lengths against iterating $\Phi$ modulo $2^n$ until 1
returns ($n \le 14$), the diagonals against a direct run of the rule table, and the white runs three ways (integer rows,
cycle lengths, rule table) for $m \le 7$. The Mahler coefficients come from the Möbius transform over the bits of $t$,
checked against a sum with `math.comb`.

`computations/right_edge_runs.c` iterates $\Phi$ on 128-bit integers from 1 to time $2^{36}$ and prints $W(2^k)$ and
the row at each time $2^k$, and the row at each time $2^{36} - 2^k$, which is $h(-2^k)$ modulo $2^{84}$ because
$L_{84} = 2^{36}$; `computations/right_edge_runs.py` drives it and reads off the cycle lengths, the stalls and the
agreement identity. Its `stall_laws` lifts the diagonals to period $2^{27}$ ($j \le 65$), computes each $K_j$ by
Lemma 1 (halving the period while a difference survives) and checks every law above at every diagonal where it applies:
item 5(a) at 64 diagonals, Theorem A(i) at 26 and (ii) at 18, Lemma 2(a) and (b) at 62 and (c) at 37, Theorem B at 17
(and its formula for $K$ at 7), with no failure; it also prints the cases of items 5(c) and 5(d), the orders and the
stalls. `tests/test_right_edge_runs.py` checks the C program against Python integers stepped one at a time and against
the white runs and cycle lengths of `two_index` ($k \le 16$), its backward rows against $\Phi$ inverted bit by bit,
the agreement identity for every pair of times in $[-24, 24]$, the degrees of Lemma 1 against the full Möbius transform,
and the laws at every diagonal $j \le 46$.

## Reproduce

```bash
python -m computations.two_index                             # L_n to n = 61, degrees j < 50: about 9 s, 200 MB
python -m computations.right_edge_runs runs --k-max 36       # items 1, 2, 6 to 8: about 2 min
python -m computations.right_edge_runs laws --diagonals 66      # items 5 and 6 to j = 65: about 5 s, 1.5 GB
```
