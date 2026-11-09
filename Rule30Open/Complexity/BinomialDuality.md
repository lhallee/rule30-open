---
title: The binomial transform over GF(2) is an involution that exchanges a period 2^a from 2^m with a period 2^m from 2^a at the same least witness, so the first rung of Problem 3, and Problem 1, hold for the center column exactly when they hold for its transform
category: complexity
problems: [3, 1]
status: proved
lean: Rule30Open.Complexity.BinomialDuality
headline: [binomial_eq_difs, bsub_eq_land, binomial_involutive, binomial_tail_difs, binomial_firstOne_iff, binomial_tail_iff, binomial_period_window_iff, binomial_period_iff, binomial_firstMismatch_iff, binomial_support_iff, binomial_periodic_iff, binomial_twoPow_iff, binomial_eventuallyPeriodic_iff, center_binomial_period_iff, center_binomial_rung_iff, center_binomial_firstMismatch_iff, problem1_iff_gamma, gamma_not_period_from_one, gamma_period_ge_262125, center_rung_le_seventeen, gamma_rung_le_seventeen]
kit: refines
kit_modules: [Rule30DifferenceOrder, Rule30Jen, Rule30Prize, Rule30Equivalents.TwoAdicPeriods, Rule30Equivalents.DiophantineGraph, Rule30Equivalents.AlgebraicDegree]
evidence: [computations/binomial_duality.py, tests/test_binomial_duality.py]
---

# The binomial transform over GF(2) is an involution that exchanges a period 2^a from 2^m with a period 2^m from 2^a at the same least witness, so the first rung of Problem 3, and Problem 1, hold for the center column exactly when they hold for its transform

For $f : \mathbb{N} \to \{0, 1\}$ write $t \subseteq n$ when every binary digit of $t$ is a digit of $n$, that is
$t \mathbin{\&} n = t$, and let
$$\zeta f(n) = \sum_{t \subseteq n} f(t) \bmod 2 .$$
By Lucas's theorem $\binom{n}{t}$ is odd exactly when $t \subseteq n$, so $\zeta f(n) = \sum_t \binom{n}{t} f(t) \bmod 2$:
$\zeta$ is the binomial transform over GF(2). Read as a function of the digits of $n$, $\zeta f$ is the algebraic normal
form of $f$ (the Moebius transform over the subset order of the digits). For the center column $c$ write
$\gamma = \zeta c$, the function whose spectrum [the index spectrum](../../negative-results/complexity/index-function-spectrum.md)
measures. In Lean these are `BinomialDuality.zeta` and `BinomialDuality.gamma`, and `difs r f` is the kit's $r$-th
difference $\Delta^r f$ over GF(2), $\Delta f(t) = f(t + 1) \oplus f(t)$ (`Rule30DifferenceOrder`).

The first rung of the ladder in [restricted models](../../negative-results/complexity/restricted-models.md) asks, for
each $k$, for a time $m \ge 2^{k-1}$ with $c(m) \ne c(m + 2^k)$; for all $k$ together it says that $c$ has no eventual
period $2^a$, which that entry shows equivalent to unbounded one-tape time. This entry shows that the transform turns
each such statement into the same statement for $\gamma$ with period and transient exchanged, with the same least
witness, and that it turns Problem 1 into Problem 1 for $\gamma$.

## Statement

All items are in Lean, for every $f$ unless the center column is named.

1. **The transform is the iterated difference** (`binomial_eq_difs`): $\zeta f(n) = \Delta^n f(0)$, the $n$-th Mahler
   coefficient of $f$ over GF(2). The subset relation is the repository's `TwoIndex.bsub`, which satisfies Pascal's
   rule (`bsub_eq_land`).
2. **Involution, and shifts against differences.** $\zeta(\zeta f) = f$ (`binomial_involutive`). With $E$ the shift,
   $\zeta(E^k f) = \Delta^k \zeta f$ and $\zeta(\Delta^k f) = E^k \zeta f$ (`binomial_shift`, `binomial_difs`), so the
   transform of $j \mapsto \Delta^r f(j + s)$ is $i \mapsto \Delta^s \zeta f(i + r)$ (`binomial_tail_difs`).
3. **The first 1 stays in place** (`binomial_prefix_iff`, `binomial_firstOne_iff`): $f$ vanishes on $[0, N)$ if and
   only if $\zeta f$ does, so $f$ and $\zeta f$ have their first 1 at the same index.
4. **The duality.** For all $r, s, N$: $\Delta^r f$ vanishes on $[s, s + N)$ if and only if $\Delta^s \zeta f$ vanishes
   on $[r, r + N)$ (`binomial_window_iff`), and so $\Delta^r f$ vanishes on $[s, \infty)$ if and only if
   $\Delta^s \zeta f$ vanishes on $[r, \infty)$ (`binomial_tail_iff`).
5. **Powers of two.** Over GF(2), $\Delta^{2^a} f(t) = f(t + 2^a) \oplus f(t)$ (the kit's `difs_two_pow`), so for all
   $a, m \ge 0$:
   - $f$ has period $2^a$ on $[2^m, \infty)$ if and only if $\zeta f$ has period $2^m$ on $[2^a, \infty)$
     (`binomial_period_iff`), and the same on windows: $f(2^m + j + 2^a) = f(2^m + j)$ for all $j < N$ if and only if
     $\zeta f(2^a + j + 2^m) = \zeta f(2^a + j)$ for all $j < N$ (`binomial_period_window_iff`);
   - **the least witnesses agree**: the least $j$ with $f(2^m + j + 2^a) \ne f(2^m + j)$ is the least $j$ with
     $\zeta f(2^a + j + 2^m) \ne \zeta f(2^a + j)$, and one exists if and only if the other does
     (`binomial_firstMismatch_iff`);
   - the two extreme cases: $f$ vanishes on $[2^m, \infty)$ if and only if $\zeta f$ has period $2^m$
     (`binomial_support_iff`), and $f$ has period $2^a$ if and only if $\zeta f$ vanishes on $[2^a, \infty)$
     (`binomial_periodic_iff`);
   - $f$ has an eventual period that is a power of two if and only if $\zeta f$ has one (`binomial_twoPow_iff`).
6. **Any period** (`binomial_eventuallyPeriodic_iff`): $\zeta f$ is eventually periodic if and only if $f$ is.
7. **The center column.**
   - $c$ has period $2^a$ on $[2^m, \infty)$ if and only if $\gamma$ has period $2^m$ on $[2^a, \infty)$
     (`center_binomial_period_iff`). At the rung $k + 1$: $c$ is not $2^{k+1}$-periodic from $2^k$ if and only if
     $\gamma$ is not $2^k$-periodic from $2^{k+1}$ (`center_binomial_rung_iff`), with the same least witness offset
     (`center_binomial_firstMismatch_iff`); $c$ has an eventual period $2^a$ if and only if $\gamma$ has one
     (`center_binomial_twoPow_iff`).
   - **Problem 1 holds if and only if $\gamma$ is not eventually periodic** (`problem1_iff_gamma`).
   - Unconditionally: for no $m$ does $\gamma$ have period $2^m$ on $[1, \infty)$ (`gamma_not_period_from_one`, from
     the kit's `center_not_eventually_period_one`); if $\gamma$ has period $2^m$ on $[2^a, \infty)$, then
     $2^a + 2^m \ge 262{,}125$ (`gamma_period_ge_262125`, from [WideWindow](../Columns/WideWindow.md)); and the rung
     holds at every level $k + 1 \le 17$ on both sides: $c$ is not $2^{k+1}$-periodic from $2^k$
     (`center_rung_le_seventeen`) and $\gamma$ is not $2^k$-periodic from $2^{k+1}$ (`gamma_rung_le_seventeen`), for
     $k \le 16$.

## Proof

**Item 1.** Both sides split the same way on the lowest digit of $n$. On the left, $2s + a \subseteq 2n + b$ exactly
when $a \le b$ and $s \subseteq n$ (`sub_digit`), and a sum over $t < 2k$ splits into even and odd $t$
(`xorSum_two_mul`), so
$$\zeta f(2n) = \zeta f_0(n), \qquad \zeta f(2n + 1) = \zeta f_0(n) \oplus \zeta f_1(n), \qquad f_0(s) = f(2s),\ f_1(s) = f(2s + 1)$$
(`zeta_two_mul`, `zeta_two_mul_add_one`). On the right, $\Delta^2 g(t) = g(t + 2) \oplus g(t)$ over GF(2), so
$\Delta^{2n} f(2s) = \Delta^n f_0(s)$ by induction on $n$ (`difs_two_mul`), and
$\Delta^{2n+1} f(0) = \Delta^{2n}(\Delta f)(0) = \Delta^n f_0(0) \oplus \Delta^n f_1(0)$ (`difs_two_mul_add_one`).
With $\zeta f(0) = f(0)$, strong induction on $n$ gives item 1. This is Lucas's theorem modulo 2 in the form of the
transform; with the kit's `fwdDiff_iter_zero` (`TwoAdicPeriods`), $\Delta^n f(0) = \sum_{j \le n} \binom{n}{j} f(j)$.
`bsub_eq_land` is the same digit recursion for `TwoIndex.bsub`.

**Item 2.** From item 1, $\zeta(\Delta f)(n) = \Delta^{n+1} f(0) = \zeta f(n + 1)$, and
$\zeta(E f)(n) = \Delta^n f(1) = \Delta^n f(0) \oplus \Delta^{n+1} f(0) = \Delta \zeta f(n)$, since $\Delta^n$ commutes
with the shift (the kit's `difs_shift`). Then $\zeta\zeta f(0) = f(0)$ and
$$\zeta\zeta f(t + 1) = \zeta(\Delta \zeta f)(t) = \zeta(\zeta (E f))(t) = E f(t) = f(t + 1)$$
by induction on $t$ for all $f$ at once (`binomial_involutive_apply`). Iterating the two identities gives
$\zeta E^k = \Delta^k \zeta$ and $\zeta \Delta^k = E^k \zeta$, and
$\zeta(E^s \Delta^r f) = \Delta^s E^r \zeta f$, which is `binomial_tail_difs`. Over GF(2) the transform conjugates the
shift $E$ into $\Delta = 1 + E$ and back.

**Item 3.** $\Delta^i g(0)$ reads only $g(0), \dots, g(i)$ (`difs_eq_false_of_prefix`), so if $g$ vanishes below $N$
then so does $\zeta g$; the converse is the same statement for $\zeta g$, by item 2. The first 1 of $g$ is at $j$ when
$g$ vanishes below $j$ and not below $j + 1$.

**Item 4.** Apply item 3 to $g(j) = \Delta^r f(j + s)$, whose transform is $\Delta^s \zeta f(i + r)$ by item 2. The
form on $[s, \infty)$ takes $N$ large.

**Item 5.** Substitute $r = 2^a$ and $s = 2^m$ in item 4 and item 3: $\Delta^{2^a} f(t) = 0$ says
$f(t + 2^a) = f(t)$. For the extreme cases take $r = 0$ or $s = 0$. If $f$ has period $2^a$ from $T$, it has it from
$2^m$ for any $2^m \ge T$, for example $m = T$, so $\zeta f$ has period $2^m$ from $2^a$; the converse is the same
statement for $\zeta f$.

**Item 6.** Let $f$ have period $P > 0$ from $T$. Every difference $\Delta^k f$ has period $P$ from $T$
(`difs_period`), so it is fixed by its window on $[0, T + P)$ (`eq_of_agree_window`). Among the $2^{T+P} + 1$ windows
of $\Delta^0 f, \dots, \Delta^{2^{T+P}} f$ two agree (the kit's `Rule30Jen.pigeonhole`), say those of
$\Delta^m f$ and $\Delta^n f$ with $m < n$, so $\Delta^m f = \Delta^n f$, and then
$\zeta f(t + n - m) = \Delta^{t - m}\Delta^n f(0) = \Delta^{t - m}\Delta^m f(0) = \zeta f(t)$ for $t \ge m$. The
converse is the same statement for $\zeta f$, by item 2.

**Item 7.** Items 5 and 6 for $f = c$. Problem 1 is the statement that $c$ is not eventually periodic. For the
unconditional parts: a period $2^m$ of $\gamma$ on $[1, \infty) = [2^0, \infty)$ would be a period $1$ of $c$ on
$[2^m, \infty)$, which the kit excludes; a period $2^m$ of $\gamma$ on $[2^a, \infty)$ is a period $2^a$ of $c$ on
$[2^m, \infty)$, so $2^m + 2^a \ge 262{,}125$ by `transient_add_period_ge_262125`; and for $k \le 16$,
$2^k + 2^{k+1} \le 3 \cdot 2^{16} = 196{,}608 < 262{,}125$, so $c$ is not $2^{k+1}$-periodic from $2^k$.

**Generating functions** (paper, not used in the Lean proofs). With $C(x) = \sum_t c(t) x^t$ and
$\Gamma(x) = \sum_n \gamma(n) x^n$ in $\mathbb{F}_2[[x]]$, $\sum_n \binom{n}{t} x^n = x^t / (1 + x)^{t+1}$ gives
$$\Gamma(x) = \frac{1}{1 + x}\, C\!\left(\frac{x}{1 + x}\right),$$
Euler's transformation of series over GF(2), and $x \mapsto x/(1 + x)$ is an involution of $\mathbb{F}_2(x)$. It fixes
the point 0 and exchanges the points 1 and $\infty$. Since $1 + x^{2^a} = (1 + x)^{2^a}$, a period $2^a$ is a pole at 1,
and a transient is a polynomial part, a pole at $\infty$; item 5 is the exact form of their exchange. A rational $C$
stays rational, which is item 6. The other poles move to other points of the same degree over GF(2) but can change
their multiplicative order, so an odd period need not survive: for the multiples of 5, $C = 1/(1 + x^5)$ and
$\Gamma = (1 + x)^4 / (1 + x + x^4)$, of period 15.

## Computations

`computations/binomial_duality.py` computes $\gamma$ by the subset-sum butterfly and checks it.

- **Ones of $\gamma$.** On $[0, 2^L)$, $\gamma$ has 131, 500, 2,057, 8,190, 32,657, 130,780 and 524,041 ones for
  $L = 8, 10, \dots, 20$, against $2^{L-1}$ = 128, 512, 2,048, 8,192, 32,768, 131,072, 524,288.
  [The index spectrum](../../negative-results/complexity/index-function-spectrum.md) sets $c(0) = 0$, which complements
  $\gamma$ (every $n$ has $0 \subseteq n$), so its monomial counts are $2^L$ minus these: 125, 524, 2,039, 8,194,
  32,879, 131,364, 524,535, as its table has.
- **The rung on both sides.** For $k = 1, \dots, 20$ the least witness offsets of "$c$ is not $2^k$-periodic from
  $2^{k-1}$" and of "$\gamma$ is not $2^{k-1}$-periodic from $2^k$" are both
  1, 1, 0, 1, 5, 0, 4, 0, 0, 3, 2, 4, 1, 0, 0, 0, 1, 0, 0, 1, the offsets of
  [restricted models](../../negative-results/complexity/restricted-models.md), as item 5 requires (the first
  $3 \cdot 2^{19} + 64$ cells).
- **Multiples of $q$.** The transform of the indicator of the multiples of $q$ (period $q$ from 0), on $2^{14}$
  values, has least eventual period and transient:

| $q$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 15 | 17 | 21 | 31 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| period | 1 | 1 | 3 | 1 | 15 | 6 | 7 | 1 | 63 | 30 | 341 | 12 | 819 | 15 | 255 | 63 | 31 |
| transient | 1 | 2 | 1 | 4 | 1 | 2 | 1 | 8 | 1 | 2 | 1 | 4 | 1 | 1 | 1 | 1 | 1 |

  For $q = 2^e$ the transform vanishes from $2^e$ on (item 5); the odd periods $2^j - 1$ stay, the others grow
  ($5 \to 15$, $9 \to 63$, $11 \to 341$, $13 \to 819$, $17 \to 255$).

`tests/test_binomial_duality.py` checks the transform against the direct subset sums, the binomial sums and the
iterated differences at every $n < 300$ of a random sequence; the involution; the operator identity of item 2 for
$r, s \le 6$; the least witnesses of item 5 on random sequences and on sequences with a planted break, for
$a, m \le 4$; the generating function above for $q \le 12$; and the numbers of the center column against
`restricted_models.dyadic_witnesses` and `index_spectrum.monomial_profile`.

## What it means

The transform moves the first rung of Problem 3 and Problem 1 to $\gamma$ without changing them. The witnesses that
the first rung needs for $c$, a time $m \ge 2^{k-1}$ with $c(m) \ne c(m + 2^k)$, are exactly the witnesses for
$\gamma$ with period and transient exchanged, at the same offset, so any proof of the rung for every $k$ is a proof of
the dual statement for $\gamma$, and conversely; and $c$ is eventually periodic exactly when $\gamma$ is. In models that
read the digits of $n$ the first rung is the same for both functions: for every function, one-tape time that is
eventually at most $k$ makes it $2^k$-periodic from $2^{k-1}$ (the kit's
`Rule30Problem3Bounds.period_of_eventually_time_le`, main branch), and an eventual period $2^a$ gives bounded time
(the lemma of [restricted models](../../negative-results/complexity/restricted-models.md)), so by
`center_binomial_twoPow_iff` every machine computing $c$ has unbounded time if and only if every machine computing
$\gamma$ does (on paper, from those two). Nothing is gained toward a proof: $\gamma$ is the normal form that
[the index spectrum](../../negative-results/complexity/index-function-spectrum.md) finds indistinguishable from a random
function, about half its values are 1, and the duality gives no reason why either side should be easier.

What the transform does show is which periods are special. Only powers of two are exchanged with transients, because the
binomial transform conjugates the shift into the difference operator and $\Delta^{2^a}$ is the difference at distance
$2^a$; an odd period is carried to another period, often a different one. So the first rung, and the open periods 2 and
4 of [the roadmap](../../ROADMAP.md), have an exact dual form, and odd periods are only carried along. The window bound
of [WideWindow](../Columns/WideWindow.md) gives the rung in Lean for every $k \le 17$ (`center_rung_le_seventeen`), past
the $k \le 13$ of the kit's main branch (`time_unbounded_le_thirteen`, from its window of 16,359); with that branch's
`period_of_eventually_time_le` it makes every one-tape machine computing $c$ take more than $k$ steps infinitely often
for $k \le 17$, a consequence joined on paper because that theorem is not at this repository's pinned commit.

## The kit, the repository and the literature

The kit has the pure-period case in an existential form, for every prime $p$: `TwoAdicPeriods.exists_fwdDiff_eq_zero_iff`
says that $u : \mathbb{N} \to \mathbb{F}_p$ has some period $p^k$ if and only if its Mahler coefficients
$\Delta^n u(0)$ vanish for all large $n$, and `noTwoPowPeriod_iff_fwdDiff` restates the absence of an eventual period
$2^k$ through the Mahler coefficients of every tail of $c$; `fwdDiff_iter_zero` writes them with binomial
coefficients over GF(2). Its `Rule30DifferenceOrder` has the iterated differences and `difs_two_pow`; its
`DiophantineGraph.sub_iff_odd_choose` is Lucas's theorem modulo 2; its `AlgebraicDegree` uses the Moebius transform for
functions of the cells of a row, not of the digits of the index. Neither the pinned kit nor its main branch (at
4f4fb5a) has the involution, the exchange of a period $2^a$ from $2^m$ with a period $2^m$ from $2^a$, the equality of
least witnesses, or the invariance of eventual periodicity, so this entry refines `TwoAdicPeriods` with exact
thresholds and both parameters. Its main branch's `Rule30Problem3Bounds` has the first rung for $k \le 13$, for the
center column only.

In the repository, [the index spectrum](../../negative-results/complexity/index-function-spectrum.md) measures $\gamma$
(complemented) as a function of the digits; [TwoIndex](TwoIndex.md) defines `bsub` with Pascal's rule; and
[right-edge cycles](../../findings/complexity/right-edge-cycles.md) expands each right diagonal $R_j$, of period
$P_j = 2^{e_j}$, on one period as $\sum_{k < P_j} a_k \binom{t}{k}$: that is item 5 with $m = 0$, $a_k = \zeta R_j(k)$
and $\zeta R_j = 0$ from $P_j$ on. Its $K_j$, the last $k$ with $a_k = 1$, is the last 1 of $\zeta R_j$, and by item 4
with $s = 0$ ($\Delta^r f = 0$ if and only if $\zeta f$ vanishes from $r$ on) $K_j + 1$ is the least $r$ with
$\Delta^r R_j = 0$, the linear complexity of $R_j$, and $P_j - 1 - K_j$ is the kit's difference order
(`Rule30DifferenceOrder.order`), as that entry says.

That the binomial transform is its own inverse over GF(2), Lucas's theorem, and the generating function $\Gamma(x) =
C(x/(1+x))/(1+x)$ are classical. Computing the linear complexity of a sequence of period $2^a$, one more than the last 1
of $\zeta f$ by the case $s = 0$, is what the algorithm of Games and Chan does; its record was seen here only through
search results. The title of Nersissian (2026, in [the literature](../../literature/rule-30.md)) names Newton supports
of Rule 30's diagonals, which are expansions of this kind; its text was not read here. A search found no statement of
the two-parameter exchange, of the equality of least witnesses, or of its reading for the first rung; the argument is
elementary, and the result may well be folklore.

## Reproduce

```bash
lake build Rule30Open.Complexity.BinomialDuality
python -m computations.binomial_duality                              # seconds
python -m computations.binomial_duality --bits 20 --max-k 20 --cells 1572928   # about 5 minutes
python -m pytest tests/test_binomial_duality.py
```
