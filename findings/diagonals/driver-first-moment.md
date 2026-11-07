---
title: From a random left half every admissible driver has black density at most 0.7729, and the driver-density conjecture S_B is a large-deviation bound for the center column with column 1 random; from the white start the admissible words with b black cells number at most 1.35 times their mean count over random left halves for n from 20 to 150, and at most 0.69 times it when b ≥ 0.68 (n - 1)
category: diagonals
problems: [2]
status: computed
formalization: wanted
evidence: [computations/driver_counts.py]
---

# From a random left half every admissible driver has black density at most 0.7729, and the driver-density conjecture S_B is a large-deviation bound for the center column with column 1 random; from the white start the admissible words with b black cells number at most 1.35 times their mean count over random left halves for n from 20 to 150, and at most 0.69 times it when b ≥ 0.68 (n - 1)

**Setting.** As in [driver density](driver-density.md): a driver $c(0) = 1, c(1), c(2), \ldots$ is *admissible* from a
left half $x$ when, with $x$ driven by $c$, $c(t + 1) = \lnot x_{-1}(t)$ whenever $c(t) = 1$. Since
$c(t + 1) = x_{-1}(t) \oplus (c(t) \lor x_1(t))$, the center column of every row is admissible from the row's own left
half, whatever its right half. $\Lambda_L$ is the set of drivers admissible from the white half, $M(T)$ the most black
cells among $c(0), \ldots, c(T)$ over $\Lambda_L$, and Conjecture $S_B$ says $M(T) \le \rho T + C$ for some $\rho < 1$.

For a word $w = w(0) \cdots w(n - 1)$ let $b(w)$ be the number of black letters among $w(0), \ldots, w(n - 2)$, the
letters that fix the next one. $N_n(b)$ is the number of words of length $n$ with $w(0) = 1$ and $b(w) = b$ that are
admissible from the white half, and $N_n(b; x)$ the same from a half $x$; so $M(T) = \max\{b : N_{T + 2}(b) > 0\}$. The
*mean count* is
$$E_n(b) = 2 \binom{n - 2}{b - 1} 2^{-b}, \qquad \sum_b E_n(b) = (3/2)^{n - 2}.$$
$h$ is the binary entropy, $d^* = 0.7729078$ the root of $h(d) = d$ in $(1/2, 1)$, and
$\kappa = 1 + \log_2\bigl(d^* / (1 - d^*)\bigr) = 2.7670$.

Lemma 1, Theorem 2 and Propositions 3 and 4 are proved on paper below, Lemma 1 from lemmas of the kit. Conjecture Q
is open; the counts that support it and the maxima from random halves are computed by
[driver_counts](../../computations/driver_counts.py), with the ranges stated.

## Lemma 1: a word is admissible from $2^{(n - 1) - b(w)}$ of the fillings (proved on paper)

**Lemma 1.** Let $n \ge 2$, let $w$ be a word of length $n$, and fix the cells of the left half beyond $-(n - 1)$. Of
the $2^{n - 1}$ fillings of the cells $-1, \ldots, -(n - 1)$, exactly $2^{(n - 1) - b(w)}$ admit $w$, that is, satisfy
$w(t + 1) = \lnot x_{-1}(t)$ at every $t \le n - 2$ with $w(t) = 1$, the half driven by $w$.

*Proof.* Drive the half by $w$. The cell $x_{-1}(j)$ depends only on the cells $-1, \ldots, -(j + 1)$ at time 0, and
changing cell $-(j + 1)$ alone flips it: these are the kit's `Rule30DrivenLeft.light_cone` and
`Rule30DrivenLeft.permutive`, which hold for every driver and every start. So the map from a filling to the column
$\bigl(x_{-1}(0), \ldots, x_{-1}(n - 2)\bigr)$ is triangular with a flip on the diagonal, a bijection of
$\{0, 1\}^{n - 1}$ (the kit's `barrier_exists` and `barrier_unique` state it for the starts whose leftmost black cell
is at $-n$). Admissibility prescribes the $b(w)$ entries at the times $t$ with $w(t) = 1$ and leaves the other
$(n - 1) - b(w)$ free. $\square$

So from a uniformly random left half a fixed word is admissible with probability $2^{-b(w)}$, and since
$2\binom{n - 2}{b - 1}$ words have $w(0) = 1$ and $b(w) = b$ (the letters $w(1), \ldots, w(n - 2)$ hold $b - 1$ black
ones and $w(n - 1)$ is free), the mean of $N_n(b; x)$ over the halves is $E_n(b)$. This is the driven-half form of the
counts that [LeftWindow](../../Rule30Open/RandomRows/LeftWindow.md) proves in Lean for whole rows (`cone_left_xor`,
`count_adapted`).

## Theorem 2: from a random left half (proved on paper)

**Theorem 2.** Let the cells $-1, -2, \ldots$ of the left half at time 0 be independent fair coins, and let $B_n(x)$ be
the largest $b(w)$ over the words $w$ of length $n$ with $w(0) = 1$ that are admissible from $x$. For every $n \ge 2$
and $a \ge 0$,
$$P\bigl(B_n \ge d^* (n - 2) + 1 + a\bigr) \le \frac{2^{-\kappa a}}{1 - 2^{-\kappa}}.$$
Hence, almost surely, for all large $T$ every driver admissible from $x$ has at most
$d^* T + 0.73 \log_2 T + 2$ black cells among $c(0), \ldots, c(T)$, and its black cells have upper density at most
$d^* = 0.7729$. Since the center column of every row is admissible from the row's left half, this holds at once for
every right half beside $x$. (The words with $w(0) = 0$ obey the estimate with the bound doubled and without the 1, so
the conclusion holds with a white center cell at time 0 as well.)

*Proof.* Write $m = n - 2$ and $j = b - 1$, so that $E_n(b) = \binom{m}{j} 2^{-j} \le 2^{m g(j/m)}$ with
$g(d) = h(d) - d$, from $\binom{m}{j} \le 2^{m h(j/m)}$. The function $g$ is concave, $g(d^*) = 0$ and
$g'(d^*) = \log_2\bigl((1 - d^*)/d^*\bigr) - 1 = -\kappa$, so $g(d) \le -\kappa (d - d^*)$ for every $d$ and
$$E_n(b) \le 2^{-\kappa (j - d^* m)}.$$
By Lemma 1 the expected number of admissible words with $b(w) = b$ is $E_n(b)$, so by the union bound
$$P\bigl(B_n \ge d^* m + 1 + a\bigr) \le \sum_{j \ge d^* m + a} 2^{-\kappa (j - d^* m)}
\le \frac{2^{-\kappa a}}{1 - 2^{-\kappa}}.$$
With $a = (2/\kappa) \log_2 n$ the bound is $n^{-2} / (1 - 2^{-\kappa})$, which is summable, so by Borel-Cantelli
$B_n < d^* (n - 2) + 1 + (2/\kappa) \log_2 n$ for all large $n$, almost surely. The black cells of a driver among
$c(0), \ldots, c(T)$ are $b$ of its prefix of length $T + 2$, so they number at most
$B_{T + 2} \le d^* T + 1 + 0.723 \log_2 (T + 2) \le d^* T + 0.73 \log_2 T + 2$ for $T \ge 2$. $\square$

The threshold is the first-moment one: $E_n(\lceil \beta n \rceil)$ tends to 0 exponentially exactly when $\beta > d^*$.
In the dual form, $\sum_b E_n(b) 2^{s b} = 2^s (1 + 2^{s - 1})^{n - 2}$ and $\min_{s > 0} \log_2(1 + 2^{s - 1}) / s =
d^*$, attained at $s = \kappa$.

## Proposition 3: $S_B$ as a large-deviation bound (proved on paper)

Run Rule 30 from the single cell's left half, white at time 0, with $c(0) = 1$, and replace column 1 by independent fair
coins $y(0), y(1), \ldots$:
$$c(t + 1) = x_{-1}(t) \oplus \bigl(c(t) \lor y(t)\bigr),$$
the left half driven by $c$. Call this the *coin process*.

**Proposition 3.**

(a) The coin process follows only admissible words, and $P\bigl(c(0..n-1) = w\bigr) = 2^{-((n - 1) - b(w))}$ for every
admissible word $w$ of length $n$. Hence $P\bigl(b(c(0..n-1)) = b\bigr) = N_n(b)\, 2^{b - (n - 1)}$ and
$$\frac{N_n(b)}{E_n(b)} = \frac{P\bigl(b(c(0..n-1)) = b\bigr)}{P\bigl(1 + \mathrm{Bin}(n - 2, 1/2) = b\bigr)}.$$

(b) From a uniformly random left half in place of the white one, $c(1), c(2), \ldots$ are independent fair coins.

(c) $S_B$ holds if and only if there is $\delta > 0$ with
$P\bigl(\text{at least } (1 - \delta) n \text{ black cells among } c(0), \ldots, c(n - 1)\bigr) < 2^{-\delta n}$ for all
large $n$.

(d) $S_B$ holds if and only if $Z_n(y) = \sum_b N_n(b)\, y^{(n - 1) - b} \le 2^{-\varepsilon n}$ for some
$y \in (0, 1/2)$, some $\varepsilon > 0$ and all large $n$. By (a), $Z_n(1/2) = 1$ for every $n$.

(e) $S_B$ holds if and only if, for some $\rho' < 1$ and $C'$, no driver in $\Lambda_L$ has more than $\rho' T + C'$
times $t < T - 1$ with $c(t) = c(t + 1) = 1$. At each such time cell $-1$ is white under a black center.

*Proof.* (a) After a black center, $c(t + 1) = \lnot x_{-1}(t)$ is the forced value; after a white one,
$c(t + 1) = x_{-1}(t) \oplus y(t)$ is a fair coin independent of the past. So each white letter among
$w(0), \ldots, w(n - 2)$ costs a factor $1/2$ and each black one costs nothing; summing over the admissible words with
$b(w) = b$ gives the distribution, and $E_n(b)\, 2^{b - (n - 1)} = \binom{n - 2}{b - 1} 2^{-(n - 2)}$. (b) Given the
past, $c(0), \ldots, c(t)$ and $y(0), \ldots, y(t - 1)$, the cell $x_{-1}(t)$ is a fair coin: the past depends on the
cells $-1, \ldots, -t$ and the coins only, and cell $-(t + 1)$, independent of them, flips $x_{-1}(t)$ (Lemma 1). So
both rules give a fair coin. (c) If $M(T) \le \rho T + C$, no admissible word of length $n$ has $(1 - \delta) n$ black
cells once $1 - \delta > \rho$ and $n$ is large, and the probability is 0. Conversely an admissible word with at least
$(1 - \delta) n$ black letters has at most $\delta n$ white ones, hence probability at least $2^{-\delta n}$ by (a); so
the bound forbids such words for large $n$, which is $S_B$ with $\rho = 1 - \delta$.
(d) If $M(T) \le \rho T + C$, every admissible word of length $n$ has at least $(1 - \rho)(n - 1) - C$ white letters
among its first $n - 1$, and there are at most $2^{n - 1}$ words, so $Z_n(y) \le 2^{n - 1} y^{(1 - \rho)(n - 1) - C}$,
which decays exponentially once $2 y^{1 - \rho} < 1$. Conversely $Z_n(y) \le 2^{-\varepsilon n}$ gives
$y^{(n - 1) - b(w)} \le 2^{-\varepsilon n}$ for each admissible $w$, at least $\varepsilon n / \log_2(1/y)$ white
letters, which is $S_B$ with $\rho = 1 - \varepsilon / \log_2(1/y)$. (e) Over $c(0), \ldots, c(T - 1)$ let $B$ count the
black cells and $D$ the times $t$ with $c(t) = c(t + 1) = 1$. A black run of length $L$ gives $L - 1$ such times and
the runs are separated by white cells, so $D \le B \le (D + T + 1)/2$; and $c(t + 1) = \lnot x_{-1}(t) = 1$ makes cell
$-1$ white at $t$. $\square$

For independent fair coins $c(1), \ldots, c(n - 1)$, which is the coin process from a random half by (b), the
probability in (c) is $2^{-(1 - h(\delta)) n + o(n)}$ (the kit's `LargeDeviations.tendsto_log_measureReal_trace`
proves this rate for the center column of a random configuration, whose cells are independent fair coins), and
$1 - h(\delta) > \delta$ exactly when $\delta < 1 - d^* = 0.2271$. So $S_B$ asks of the coin process from the white
half an upper large-deviation bound with rate $\delta$ at density $1 - \delta$, where fair coins have rate
$1 - h(\delta)$, far larger for small $\delta$.

## Conjecture Q and the counts

**Conjecture Q.** There is $C$ such that $N_n(b) \le C\, E_n(b)$ for every $n \ge 2$ and every $b$. By Proposition
3(a): under the coin process from the white half, the number of black cells among $c(0), \ldots, c(n - 2)$ takes each
value $b$ with at most $C$ times the probability that $1 + \mathrm{Bin}(n - 2, 1/2)$ does.

**Proposition 4 (proved on paper).** (a) Q implies $M(T) \le d^* T + 1 + \log_2(C) / \kappa$ for every $T$: $S_B$ with
$\rho = d^* = 0.7729$. (b) If for some $\rho \in (d^*, 1)$ and some $\theta < \rho - h(\rho)$ the bound
$N_n(b) \le 2^{\theta n} E_n(b)$ holds for all large $n$ and every $b \ge \rho (n - 1)$, then $S_B$ holds with that
$\rho$. Conversely $S_B$ with some $\rho' < \rho$ gives the bound with $\theta = 0$, so (b) is equivalent to $S_B$. The
loss $\rho - h(\rho)$ that (b) allows is 0.0781 at $\rho = 0.8$, 0.2402 at 0.85, 0.4310 at 0.9 and 0.6636 at 0.95.

*Proof.* (a) By the proof of Theorem 2, $C E_n(b) \le C\, 2^{-\kappa (b - 1 - d^* (n - 2))} < 1$ once
$b > 1 + d^* (n - 2) + \log_2(C) / \kappa$; $N_n(b)$ is an integer, so it is 0 there, and
$M(T) = \max\{b : N_{T + 2}(b) > 0\}$. (b) For $b \ge \rho (n - 1)$ the ratio $j/m$ of that proof is at least
$\rho_n = (\rho (n - 1) - 1)/(n - 2) \to \rho$, and $g$ decreases on $(1/3, 1)$, so
$E_n(b) \le 2^{m g(\rho_n)} = 2^{-(\rho - h(\rho)) n + o(n)}$ and
$N_n(b) \le 2^{(\theta - \rho + h(\rho)) n + o(n)} < 1$ for large $n$. $\square$

**The counts (computed).** `count_layers` computes $N_n(b)$ exactly for every $n \le 150$ in one pass, by dynamic
programming over the states (left half at time $t$, $c(t)$), each with its count vector packed into one Python
integer; it clears the cells that no word of the range can still read and merges the states that then agree. It agrees
with the listing of every admissible word for $n \le 14$, from the white half and from a random half; with the
independent count of admissible words of `constrained_runs` for $n \le 22$; with the maxima of `driver_density` (the
densest word at every $n \le 70$); and, summed over all $2^{n - 1}$ fillings, with $2^{n - 1} E_n(b)$ for $n \le 8$
(tests). The total at $n = 40$ is the 3,774,663 of
[driven left runs](driven-left-runs.md#long-runs-against-fair-bits-a-heuristic).

| $n$ | admissible words | $\log_2(\text{words})/n$ | largest $N_n(b)/E_n(b)$ (at $b/(n-1)$) | largest for $b \ge 0.68(n-1)$ | densest $b$ (at $b/(n-1)$) | largest $b$ with $E_n(b) \ge 1$ |
|---:|---:|---:|---:|---:|---:|---:|
| 20 | 1,159 | 0.5089 | 1.3058 (0.526) | 0.6619 | 13 (0.684) | 14 |
| 40 | 3,774,663 | 0.5462 | 1.1400 (0.513) | 0.2231 | 27 (0.692) | 29 |
| 60 | 13,356,789,054 | 0.5606 | 1.0376 (0.508) | 0.3421 | 42 (0.712) | 44 |
| 80 | $4.279 \times 10^{13}$ | 0.5660 | 1.0401 (0.519) | 0.2685 | 57 (0.722) | 60 |
| 100 | $1.456 \times 10^{17}$ | 0.5701 | 1.0347 (0.515) | 0.1885 | 72 (0.727) | 75 |
| 120 | $4.719 \times 10^{20}$ | 0.5723 | 1.0336 (0.513) | 0.1669 | 86 (0.723) | 90 |
| 140 | $1.555 \times 10^{24}$ | 0.5740 | 1.0292 (0.504) | 0.1694 | 101 (0.727) | 106 |
| 150 | $8.842 \times 10^{25}$ | 0.5746 | 1.0285 (0.503) | 0.1463 | 108 (0.725) | 114 |

The mean count of all words grows by $\log_2(3/2) = 0.5850$ per letter. For every $n$ from 20 to 150 and every $b$,
$N_n(b) \le 1.3471\, E_n(b)$ (the largest ratio is 1.34708, at $n = 23$ and $b = 12$), and
$N_n(b) \le 0.6839\, E_n(b)$ when $b \ge 0.68 (n - 1)$ (0.68389, at $n = 52$ and $b = 35$). Below $n = 20$ the largest
ratio is 3.2, at $n = 7$ and $b = 5$: the single cell's own column 1101110 is the only admissible word of length 7 with
five black cells among its first six letters, against a mean count $E_7(5) = 0.3125$. So Q holds with $C = 3.2$ for
$n \le 150$. From $n = 60$ to 150 the largest ratio is at most 1.0508 ($n = 70$) and sits at $b/(n - 1)$ between 0.500
and 0.525, and the largest ratio for $b \ge 0.68 (n - 1)$ lies between 0.095 and 0.456. At $n = 100$ the ratio falls
from 0.8489 at $b = 60$ to 0.0023 at $b = 72$ (one word, against a mean count of 431), and the mean count stays at
least 1 up to $b = 75$.

Under the coin process from the white half, the number of black cells among $c(0), \ldots, c(n - 2)$ has mean 0.03 to
0.10 below the fair $n/2$ at $n = 20, 30, \ldots, 150$, and variance $0.155 (n - 2)$, $0.218 (n - 2)$,
$0.231 (n - 2)$ and $0.235 (n - 2)$ at $n = 20$, 50, 100 and 150, against $(n - 2)/4$ for fair coins. On this range it
is a little more concentrated than fair coins, which is how the ratio exceeds 1 near $b = n/2$ and falls below it in
the tails.

**Random halves as a control (computed).** From 8 uniformly random left halves (`halves`, seed 2026), at $n = 100$ the
ratio $N_{100}(b; x)/E_{100}(b)$ at $b = 67$ (density 0.68) lies between 0.014 and 0.923, against 0.274 from the white
half, and at $b = 50$ between 0.963 and 1.067, against 1.034. The largest ratio over $20 \le n \le 100$ lies between
1.329 and 5.354, against 1.347 from the white half, which is below that of 7 of the 8 random halves. So at $n = 100$
the white half's ratios lie inside the spread of the random halves, and over $20 \le n \le 100$ its constant in Q is
smaller than that of all of them but one.

## From random halves the rate is near 3/4 too (computed)

Write $M_x(T)$ for the most black cells among $c(0), \ldots, c(T)$ over the drivers admissible from $x$. Theorem 2
gives $\limsup_T M_x(T)/T \le 0.7729$ for almost every $x$. From three uniformly random halves (`random`, seed 12345)
the exact values at $T = 60$ are 46, 44 and 44, against $M(60) = 44$ from the white half, and a beam that keeps 20,000
states (a lower bound attained by a driver) gives $M_x(1{,}000) \ge 753$, 750 and 749, ratios to $T + 1$ of 0.7522,
0.7493 and 0.7483, against 749 (0.7483) from the white half, the count of [driver density](driver-density.md).

## What it means

- **The first moment is nearly the truth.** From random halves the measured ratios at $T = 1{,}000$, 0.748 to 0.752
  (lower bounds on $M_x(1{,}000)/1{,}001$), sit just below the proved limit 0.7729, and the white half measures the same
  (0.7511 at $T = 3{,}000$ in [driver density](driver-density.md)). Read heuristically, the dependence between the
  forced values along the tree of drivers lowers the rate below the first-moment threshold by about 0.02, from random
  halves and from the white half alike.
- **$S_B$ is a comparison with fair coins, with room to spare.** By Propositions 3 and 4, $S_B$ says that the white
  half's dense admissible words are not much more numerous than fair coins make them: a proof may lose a factor
  $2^{\theta n}$ against the mean count, with $\theta < \rho - h(\rho)$ for the target $\rho$ (0.078 for
  $\rho = 0.8$, 0.43 for $\rho = 0.9$), while the counts meet Q, a bound with no exponential loss, on the whole range
  and stay below the mean count in the dense tail. Q and the forms (c) and (d) are sums over drivers rather than a
  maximum, so a proof of them may average over drivers, for instance through a weighted transfer operator on the
  states. A potential must bound every edge instead, and over a basis of 27 row features it certifies only $12/13$
  ([driver-density potentials](../../negative-results/diagonals/driver-density-potential.md)).
- **Where it stops.** Theorem 2 is about almost every left half, and the white half is one half, of measure zero: the
  barrier of [almost every row](../../negative-results/random-rows/almost-every-row.md) applies. Q, and $S_B$ itself,
  are statements about the one tree of drivers from the white half, and the control above says that tree looks like a
  random one without saying why. What the entry adds is a benchmark that is a theorem for random halves and a target
  that may lose an exponential factor against it.
- **The kit.** The pinned kit has the bijection behind Lemma 1 (`Rule30DrivenLeft.light_cone`, `permutive`,
  `barrier_exists`, `barrier_unique`), the fair center column of a random configuration
  (`RandomConfigurations.measurePreserving_trace`), its normality beside a fixed right half
  (`ae_isNormal_trace_glue`, with an exceptional set that depends on the right half) and Cramér's theorem for it
  (`LargeDeviations.tendsto_log_measureReal_trace`). It bounds no density over all the drivers a left half allows,
  from a random half or from the white one, and Theorem 2's bound for every right half at once is not in it. Lemma 1
  is a finite count over `Rule30DrivenLeft` and Propositions 3 and 4 follow from it by elementary estimates; Theorem 2
  also needs Borel-Cantelli, which the kit's `RandomConfigurations` already uses in Lean
  (`ae_eventually_abs_count_trace_lt`).

## Reproduce

```bash
python -m computations.driver_counts sweep --nmax 150        # the table and the ranges, about 1 min, 2 GB
python -m computations.driver_counts sweep                   # the same to n = 120, about 5 s
python -m computations.driver_counts tail --n 100 --start 60 # N_100(b) against E_100(b), about 1 s
python -m computations.driver_counts halves                  # the control from 8 random halves, about 4 s
python -m computations.driver_counts random                  # 3 random halves and the white one, about 1 min
```

The defaults are `sweep --nmax 120 --nmin 20 --late 60 --every 10`, `tail --n 100` (from $b = 0.68 (n - 1)$),
`halves --n 100 --halves 8 --seed 2026` and `random --steps 1000 --beam 20000 --exact 60 --halves 3 --seed 12345`.
`sweep` prints $d^*$, $\kappa$, the losses $\rho - h(\rho)$, a row every 10 values of $n$ (with the total probability,
mean and variance of the coin process) and the largest ratios over the range.
