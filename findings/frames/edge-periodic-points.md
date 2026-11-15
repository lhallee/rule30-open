---
title: The right-edge map has no periodic 2-adic points of period dividing 64 other than 0 and the shifts of the rain pair ±1/3, so a row with a white right half that comes back after L steps moved L cells right, 128 not dividing L, is white or a rain row; an odd seed agreeing with ±1/3 to exactly m bits leaves every cycle of length dividing 2^k by level m + T_k + 2, sharp for every m ≥ 2, with T_k = 0, 1, 3, 4, 14, 103 for k = 1, ..., 6
category: frames
problems: [3]
status: computed
formalization: partial
evidence: [computations/edge_periodic_points.py, tests/test_edge_periodic_points.py]
---

# The right-edge map has no periodic 2-adic points of period dividing 64 other than 0 and the shifts of the rain pair ±1/3, so a row with a white right half that comes back after L steps moved L cells right, 128 not dividing L, is white or a rain row; an odd seed agreeing with ±1/3 to exactly m bits leaves every cycle of length dividing 2^k by level m + T_k + 2, sharp for every m ≥ 2, with T_k = 0, 1, 3, 4, 14, 103 for k = 1, ..., 6

In the frame of its right edge Rule 30 is the invertible T-function $\Phi(y) = y \oplus (2y \lor 4y)$ on the 2-adic
integers $\mathbb{Z}_2$: bit $e$ of $\Phi(y)$ is $y_e \oplus (y_{e-1} \lor y_{e-2})$, with $y_{-1} = y_{-2} = 0$ (the
kit's `TFunction`, `Odometer.G`, `Rule30FrozenRuler.T`). The kit has the cycle theory of Klimov and Shamir and of
Anashin for such maps, proved for every natural seed $x$ of any such T-function and applied elsewhere to the orbit of 1
(`TFunctionCycles`: `lift_iff`, `per_eq_two_pow`, `iterate_mod_iff_dvd`, `per_unbounded`), the odometer structure of the orbit closure of every nonzero finite seed
(`Rule30Equivalents.Odometer`), and the one periodic orbit it names: $\Phi$ swaps $-1/3 = \dots 10101$ and $1/3 = \dots
101011$, and these are the only odd $y$ with $\Phi^2(y) = y$ (`Rule30EdgeStaircases.period_two_iff`, `no_fixed_point`).
This entry asks for all the periodic points of $\Phi$ on $\mathbb{Z}_2$, not only those of finite seeds, and measures
how fast a seed near them leaves a short cycle.

A 2-adic integer $y$ is a row white to the right of one cell and read leftward from it; $\Phi^L(y) = y$ says that the row
comes back after $L$ steps moved $L$ cells to the right. These are the rows of $\Sigma_L$ of [the light-like
rows](../../Rule30Open/RandomRows/LightLikeEntropy.md) that have a white right half: $\Sigma_{12}$, $\Sigma_{15}$ and
$\Sigma_{17}$ are uncountable, and the question is what a right edge leaves of them.

## Result

1. **The column graph** (paper). For $L \ge 1$ let $G_L$ be the graph on pairs $(u, v)$ of words $\mathbb{Z}/L \to \{0,
   1\}$ with an edge $(u, v) \to (v, w)$ whenever $w(t + 1) \oplus w(t) = u(t) \lor v(t)$ for all $t \in \mathbb{Z}/L$.
   Then the odd $y$ with $\Phi^L(y) = y$ correspond one to one to the infinite walks in $G_L$ from $(0, 1)$ (the white
   word, the black word), by $y \mapsto (b_{e-1}, b_e)_{e \ge 0}$ with $b_e(t) = $ bit $e$ of $\Phi^t(y)$.
   Moreover, for odd $y$, $\Phi^L(y) \equiv y \pmod{2^n}$ exactly when the columns $b_0, \dots, b_{n-1}$ are
   $L$-periodic, that is when $(b_{e-1}, b_e)_{0 \le e < n}$ is a walk of $n - 1$ edges in $G_L$ from $(0, 1)$.
2. **The periodic points** (exact computation of a finite graph, $L = 2^k$, $k \le 6$; for $L = 64$ the computation
   rests on the one implementation in `computations/`, see Reproduce). In $G_{2^k}$, $1 \le k \le 6$,
   the part reachable from $(0, 1)$ has 7, 11, 35, 67, 2,115 and 171,779 states, of which exactly 5 have an infinite
   forward walk: the start and four states that the walks of $\pm 1/3$ pass through, two at level 1 and two that
   alternate at every level from 2 on. The start has two live successors and each of the other four live states has
   exactly one. So for every $L$ with $128 \nmid L$:
   $$\Phi^L(y) = y \iff y = 0 \ \text{ or } \ y = \pm 2^m/3 \text{ for some } m \ge 0 \text{ and } L \text{ even}.$$
   Equivalently: a row of Rule 30 that is white to the right of some cell and comes back after $L$ steps moved $L$
   cells to the right, $128 \nmid L$, is all white or a translate of the rain row $\dots 0101011$ or $\dots 010101$ (in
   which case $L$ is even). In particular every row of $\Sigma_{15}$ and $\Sigma_{17}$ other than the white one, and every
   row of $\Sigma_{12}$ other than the white and rain rows, has infinitely many black cells to the right of each cell.
3. **Leaving a short cycle** (exact computation, sharp). Let $T_k$ be the largest number of edges of a walk in $G_{2^k}$
   that starts at a successor of a live state and has no live state. Then $T_k = 0, 1, 3, 4, 14, 103$ for $k = 1, \dots,
   6$, and: if $y$ is odd, $y \ne \pm 1/3$, and $m = \max(v_2(y - 1/3), v_2(y + 1/3))$ (so $m \ge 2$), then
   $$\Phi^{2^k}(y) \not\equiv y \pmod{2^n} \quad \text{for every } n \ge m + T_k + 2,$$
   and for each $k \le 6$ and every $m \ge 2$ some odd $y$ with that $m$ has $\Phi^{2^k}(y) \equiv y \pmod{2^{m + T_k +
   1}}$. In cycle language: the cycle
   of $y$ modulo $2^n$ is longer than $2^k$ from level $m + T_k + 2$ on, for every odd seed except the rain pair.
4. **The single cell** (corollary of 3). The seed 1 has $m = v_2(1 + 1/3) = 2$, so $L_n > 2^k$ for $n \ge T_k + 4$,
   that is $J_k \le T_k + 2$ with $J_k = W(2^k)$ the white run of [right-edge
   cycles](../complexity/right-edge-cycles.md). With $J_k = 2, 3, 5, 6, 8, 14$ for $k = 1, \dots, 6$, equality holds for
   $k \le 4$ (the single cell stays in its short cycles as long as any seed can) and fails from $k = 5$ on: $8 < 16$ and
   $14 < 105$.
5. **Conjecture.** For every $k$ the live part of $G_{2^k}$ is the start and the four rain states, so the periodic
   points of $\Phi$ on $\mathbb{Z}_2$ are exactly 0 and $\pm 2^m/3$, and a row with a white right half is light-like
   periodic only if it is white or rain. Checked for $k \le 6$ (item 2); nothing proves it beyond.

## Proofs

**Item 1.** Bit $e$ of $\Phi(z)$ is $z_e \oplus (z_{e-1} \lor z_{e-2})$, so the columns of the orbit of any $y$ obey
$b_e(t + 1) = b_e(t) \oplus (b_{e-1}(t) \lor b_{e-2}(t))$ for all $t$, with $b_{-1} = b_{-2} = 0$; for odd $y$, $b_0
= 1$. If $\Phi^L(y) = y$ every column is $L$-periodic, so $(b_{e-1}, b_e)_{e \ge 0}$ is a walk in $G_L$ from $(0, 1)$.
Conversely, a walk $(b_{e-1}, b_e)_{e \ge 0}$ from $(0, 1)$ defines $y = \sum_e b_e(0) 2^e$, and induction on $t$ (the
recurrence is $\Phi$ bit by bit) gives bit $e$ of $\Phi^t(y)$ equal to $b_e(t \bmod L)$, so $\Phi^L(y) = y$; distinct
walks give distinct $y$, since the word $b_e$ is fixed by $b_{e-1}, b_{e-2}$ and $b_e(0)$. For the finite form,
$\Phi^L(y) \equiv y \pmod{2^n}$ means bits $0, \dots, n - 1$ of $\Phi^{t + L}(y) = \Phi^t(\Phi^L(y))$ and $\Phi^t(y)$
agree for every $t$ ($\Phi^t$ is a T-function), that is $b_0, \dots, b_{n-1}$ are $L$-periodic. Given $u, v$, the
equation $\Delta w = u \lor v$ on $\mathbb{Z}/L$ has a solution exactly when $u \lor v$ has an even number of ones, and
then exactly two, $w$ and its complement; this is the doubling criterion of `TFunctionCycles.lift_iff` read as a graph.

**Item 2.** $G_L$ is finite, so a state has an infinite forward walk exactly when it has walks of every length (König),
and these *live* states are found by deleting, until none is left, the states with no remaining successor.
`computations/edge_periodic_points.py` builds the reachable part of $G_{2^k}$ and does this. With five live states, the
start's two live successors and one live successor at every other live state, there are exactly two infinite walks, so
by item 1 exactly two odd $y$ with $\Phi^{2^k}(y) = y$; $\pm 1/3$ are two such (`period_two_iff`), so they are all.
Three reductions finish the statement for every $L$ with $128 \nmid L$. (i) $\Phi(2z) = 2\Phi(z)$, since bit $e$ of
$\Phi(z)$ reads bits $e - 2, \dots, e$ only and $2z$ has bit 0 white, so for $y = 2^m z$, $z$ odd, $\Phi^L(y) = y$ if and
only if $\Phi^L(z) = z$. (ii) If $\Phi^L(z) = z$, the cycle length of $z$ modulo every $2^n$ divides $L$
and is a power of two: these are `iterate_mod_iff_dvd` and `per_eq_two_pow` applied to the natural number $z \bmod 2^n$,
since $\Phi^t(z) \equiv \Phi^t(z \bmod 2^n) \pmod{2^n}$ ($\Phi$ is a T-function). Directly: the cycle modulo $2^{n+1}$
projects onto the cycle modulo $2^n$ with fibers of size at most 2, so its length is the same or doubled, and modulo 2 the
length is 1 for odd $z$. So the cycle length so it divides $2^{v_2(L)}$, and $\Phi^{2^{v_2(L)}}(z)
\equiv z$ modulo every $2^n$, that is $\Phi^{2^{v_2(L)}}(z) = z$; with $v_2(L) \le 6$ the computation applies. For odd $L$
this gives $\Phi(z) = z$, which no odd $z$ satisfies (bit 1 of $\Phi(z)$ is $z_1 \oplus 1$). (iii) The translation to
rows: put the cell right of which the row is white at 0 and read $y_e = x(-e)$. Cell $(t, t - e)$ of the evolution depends
only on the cells $-e, \dots, 2t - e$ at time 0; those right of 0 are white, and those at or left of 0 are the cells $-e,
\dots, 0$, which are bits $0, \dots, e$ of $y$, so it equals the same cell for the finite row $y \bmod 2^{e+1}$, which is bit $e$ of $\Phi^t(y)$ by the kit's `TFunction.testBit_orbit`. So $F^L x =
\sigma^{-L} x$ for such a row exactly when $\Phi^L(y) = y$.

**Item 2 for period 4, by hand and in Lean.** The graph argument is short enough to follow on paper for $L = 4$, and
[EdgePeriodFour](../../Rule30Open/Frames/EdgePeriodFour.md) proves it in Lean (`period_four_iff`). Write words on
$\mathbb{Z}/4$ as $b(0)b(1)b(2)b(3)$. For odd $y$, $b_0 = 1111$, and $\Delta b_1 = 1111$ makes $b_1$ alternating
($0101$ or $1010$). Let $(u, v)$ be a state with $u$ and $v$ alternating. If $v = \bar u$, then $u \lor v = 1111$ has
four ones and the two successors are $(v, u)$ and $(v, v)$. If $v = u$, then $u \lor v = u$ has two ones, so the
successor word $w$ satisfies $w(t + 1) = w(t) \oplus u(t)$: with $u(t_0) = u(t_0 + 2) = 1$, it gives $w(t_0 + 3) =
w(t_0 + 1) \oplus u(t_0 + 1) \oplus u(t_0 + 2) = \overline{w(t_0 + 1)}$, so $w \lor u$ has the two ones of $u$ and
exactly one of $w(t_0 + 1), w(t_0 + 3)$: three ones, and $(u, w)$ has no successor. The state $(1111, b_1)$ has the
successors $(b_1, b_1)$ and $(b_1, \bar b_1)$, since $b_1 \lor 1111 = 1111$. So an infinite walk never enters a state $(u,
u)$, and $b_{e+1} = \bar b_e$ for every $e \ge 1$: $y_0 = 1$, $y_1$ is free and $y_{e+1} = \bar y_e$ from there, which is
$-1/3 = \dots 10101$ or $1/3 = \dots 101011$. The dead branch $(u, u)$ lasts one edge, which is $T_2 = 1$.

**Item 3.** Let $y$ be odd, $y \ne \pm 1/3$, with $y \equiv r \pmod{2^m}$, $y \not\equiv r \pmod{2^{m+1}}$, $r \in \{\pm
1/3\}$, $m$ largest. The columns $b_e$ of $y$ and of $r$ agree for $e < m$ (bit $e$ of $\Phi^t(y)$ reads $y \bmod
2^{e+1}$), and if $b_m$ of $y$ is $2^k$-periodic it solves the same equation as $r$'s and differs from it at $t = 0$, so
it is its complement. So up to level $m - 1$ the walk of $y$ is the walk of $r$, through live states, and its state at
level $m$ is the successor of a live non-start state other than its unique live successor: not live. If $\Phi^{2^k}(y)
\equiv y \pmod{2^n}$, the walk has $n - 1$ edges in $G_{2^k}$ (item 1), the last $n - 1 - m$ of them from that non-live
successor through non-live states (a successor of a non-live state is not live), so $n - 1 - m \le T_k$. Sharpness for every $m \ge 2$: the computation
(`escape_depth_by_level`) finds the two live states of level 1 and finds that the other two live states both occur at
level 2; since the walks of $\pm 1/3$ alternate between those two from level 2 on, both occur at every level $j \ge 2$.
For $k \le 6$ the longest walk through non-live states from a non-live successor has $T_k$ edges both from the level-1
live states and from the two others. Prefixing the walk of the rain point through that live state at level $j = m - 1$
gives a walk from the start of $n - 1$ edges with $n - 1 - m = T_k$, the walk of an odd residue modulo $2^n$ that agrees
with that rain point to exactly $m$ bits. The computation of $T_k$ is a longest path in the
non-live part, which is acyclic (a cycle is live).

**Item 4.** $1 + 1/3 = 4/3$ and $1 - 1/3 = 2/3$, so $m = 2$ for the seed 1, and item 3 gives $L_n > 2^k$ for $n \ge T_k
+ 4$; by the kit's `per_iff_gap`, $L_n \le 2^k$ exactly when $n \le J_k + 1$, so $J_k + 1 \le T_k + 3$. The values of
$J_k$ are recomputed by `white_run` and agree with right-edge cycles.

## What this gives toward L_n / n, and what it does not

The cycle tree of Klimov, Shamir and Anashin, taken over all seeds, bounds the single cell by $J_k \le T_k + 2$, with
the rain pair as the only seeds removed. That inequality would give $L_n / n$ unbounded if $T_k = o(2^k)$, and it is
exact for $k \le 4$. It is far from exact after: $T_k / 2^k = 0, 0.25, 0.375, 0.25, 0.44, 1.61$ for $k = 1, \dots, 6$,
and $T_6 = 103$ exceeds the period 64 ($T_6 + 2 = 105$ still beats the kit's $J_6 \le 2^7 - 2 = 126$ of
`rows_at_powers_of_two`). By the sharpness in item 3 with $m = 2$ some finite row (a residue modulo $2^{106}$)
keeps its first 106 right diagonals at a period dividing 64, while the single cell keeps 15. So the seed-uniform escape depth does not see the single cell's light cone, which
is where [the routes to L_n / n unbounded](../../negative-results/complexity/right-edge-cycle-routes.md) say a proof
must look; the route is recorded in [the seed-uniform escape
depth](../../negative-results/complexity/seed-uniform-escape-depth.md). What the global view does give is item 2: the
seeds $\pm 1/3$ that bar every seed-free argument (section 7 of the routes) are, for periods up to 64, the only
obstruction of their kind: every other seed, finite or not, has a cycle longer than 64 modulo $2^n$ for all large $n$
(and, for finite seeds, unbounded cycle lengths by the kit's `Odometer`).

For finite seeds part of item 3 is in kit work after the pinned commit, as recorded in [the kit pull
requests](../../literature/kit-pull-requests.md) (#51, #54, #55): kit main's `Rule30UniversalStart.universal_start`
gives the least periods 4, 8, 8, 16, 32, 32 of the diagonals $D_{m+1}, \dots, D_{m+6}$ for every finite seed with $m \ge
2$ in the sense of that pull request, which bounds the depths $T_1, \dots, T_4$ for those seeds, and the open PR #55
claims that the whole-prefix clock reaches 64 by diagonal $m + 15$, sharp for the seed 47649: that is $T_5 = 14$ with a
sharp witness (47649 has $m = 2$ here, and its cycle has length 32 modulo $2^{17}$ and 64 modulo $2^{18}$). New here are
$T_6 = 103$, the column graph for all 2-adic seeds, and the classification of the periodic points in item 2.

The kit's frozen ruler (`Rule30FrozenRuler.frozen_ruler`) measures a finite row's depth against the single cell's orbit;
item 3 is the same isometry argument measured against the periodic orbit, and it holds for infinite rows.

## Reproduce

```
python -m computations.edge_periodic_points --k-max 6    # items 2 to 4, L = 2, ..., 64: about 5 s
python -m pytest tests/test_edge_periodic_points.py      # the graph against direct iteration of Phi: under a second
```

The test checks, against iteration of $\Phi$ modulo $2^n$ on all odd residues: the residues fixed by $\Phi^L$ modulo
$2^n$ against the walks of $G_L$ ($L \le 16$, $n < 12$); that only $\pm 1/3$ survive to level $8 + T_k + 2$ ($L \le
16$); the bound of item 3 and its sharpness ($L \le 8$, residues modulo $2^{14}$); and $J_k$, $k \le 6$, against right-edge
cycles. For $L = 32$ a separate test uses no graph: over all odd residues modulo $2^{19}$ other than $\pm 1/3$, the
largest value of (the largest $n$ with $\Phi^{32}(y) \equiv y \pmod{2^n}$) $- m$ is $T_5 + 1 = 15$. For $L = 64$ (item
2 at $k = 6$ and $T_6 = 103$) the repository has only the graph computation of `computations/edge_periodic_points.py`.
