---
title: The kit's source-energy hypothesis gives density 1/2 on every progression mod 2^k p, hence Problem 1 too
category: structure
problems: [1, 2]
status: paper
formalization: wanted
evidence: [computations/source_energy.py, tests/test_source_energy.py]
---

# The kit's source-energy hypothesis gives density 1/2 on every progression mod 2^k p, hence Problem 1 too

The kit's main branch (module `Rule30SourceEnergy`, not in the pinned commit) derives Problem 2 from one estimate,
`SourceEnergySmallO`: $E_{\mathrm{src}}(n) = o(2^n n^2)$, where for $N = 2^n$, the $n$ shifts
$S_n = \{0, 1, 2, 4, \dots, 2^{n-2}\}$ and $z(t) = (-1)^{c(t)}$ extended by $0$ outside $[0, N)$,

$$Z(u) = \sum_{s \in S_n} z(u + s), \qquad E_{\mathrm{src}}(n) = \sum_{0 \le u < N} Z(u)^2 .$$

Its inequality is the frequency-zero case of a Fourier inequality, and the lacunary shift set makes the inequality
strong at every frequency $a / (2^k p)$ with $p = 1$ or $p$ an odd prime. So the hypothesis says much more than Problem 2:

1. **Fourier inequality.** For every real $\theta$, every $n \ge 2$ and every $2^{n-1} < M \le 2^n$,
   $$|P_n(\theta)| \cdot |\hat z_M(\theta)| \le \sqrt{M \, E_{\mathrm{src}}(n)} + 2^n, \qquad
   P_n(\theta) = \sum_{s \in S_n} e(s\theta), \quad \hat z_M(\theta) = \sum_{t < M} z(t)\, e(-t\theta),$$
   with $e(x) = e^{2\pi i x}$. At $\theta = 0$, $P_n = n$ and this is the kit's bound
   $n |D(M)| \le \sqrt{M E_{\mathrm{src}}(n)} + 2^n$.
2. **The frequencies it controls.** For $\theta = a/(2^k p)$ in lowest terms with $p = 1$ or $p$ an odd prime,
   $P_n(\theta)/n$ tends to a nonzero limit. Hence `SourceEnergySmallO` implies $\hat z_M(\theta) = o(M)$ at every such
   $\theta$.
3. **Progressions.** `SourceEnergySmallO` implies that for every modulus $q = 2^k$ or $q = 2^k p$ ($k \ge 0$, $p$ an odd prime)
   and every residue $r$, the black cells among the $t < M$ with $t \equiv r \pmod q$ are a fraction $1/2 + o(1)$ of
   them. For $q = 2^k$ there is an integer bound with no Fourier analysis: for every $f$ of period $2^k$ with
   $|f| \le 1$ and $k < n$, $(n - k)\,|\sum_{t<M} z(t) f(t)| \le \sqrt{M E_{\mathrm{src}}(n)} + kM + 2^n$.
4. **Problem 1.** `SourceEnergySmallO` implies Problem 1: the center column is not eventually periodic. So the kit's
   hypothesis is a joint sufficient condition for Problems 1 and 2, and a proof of it must exclude every eventual period.
5. **Strictly stronger than density 1/2.** As a property of 0/1 sequences the hypothesis is strictly stronger than density
   1/2: $c(t) = t \bmod 2$ has density 1/2 and $E_{\mathrm{src}}(n) \ge \frac34 \, 2^n (n-2)^2$.
6. **Not every progression.** The moduli of item 3 cannot include 9 on the hypothesis alone: for $0 < \delta \le 1$,
   independent cells black at $t$ with probability $(1 - \delta\cos(2\pi t/9))/2$ satisfy `SourceEnergySmallO` almost
   surely and have black fraction $(1 - \delta)/2$ on $t \equiv 0 \pmod 9$ (and $1/2$ overall and on every class mod 3).
   So the hypothesis does not give density 1/2 along every arithmetic progression, which the pinned kit's
   `problem1_of_density_on_progressions` assumes; item 4 goes through the dyadic classes instead.

On the center column, to $N = 2^{18}$, $E_{\mathrm{src}}(n)$ is within 4.3 percent of its mean over independent fair
signs for every $9 \le n \le 18$ (within 0.3 percent at $n = 18$), so $E_{\mathrm{src}}(n) / (N n^2)$ falls like $1/n$
(0.054 at $n = 18$; 0.745 for $t \bmod 2$). The Fourier coefficients at $1/2, 1/4, 1/8, 1/3, 1/5, 1/6, 1/7, 1/9$ and the
class biases mod $2^k$, $k \le 6$, are of the size that independent signs give: in this one run at $N = 2^{18}$,
$|\hat z_N(\theta)| / \sqrt{N}$ and the class bias times the square root of the class size lie between 0.6 and 2.6. These numbers are
consistent with the hypothesis and say nothing about its truth: the bounds of items 1 and 3 at $n = 18$ are 0.29 to 2.6,
against observed values below 0.04.

## Proofs

**Item 1.** Fix $\theta$ and $2^{n-1} < M \le 2^n$. Exchange the sums and put $t = u + s$:

$$\sum_{0 \le u < M} Z(u)\, e(-u\theta) = \sum_{s \in S_n} e(s\theta) \sum_{t \in [s, s+M) \cap [0, N)} z(t)\, e(-t\theta).$$

The inner range differs from $[0, M)$ by at most $s$ terms removed ($[0, s)$) and at most $s$ terms added
($[M, \min(M + s, N))$), each of modulus at most 1, so the right side is $P_n(\theta) \hat z_M(\theta)$ up to an error of
modulus at most $2\sum_{s \in S_n} s = 2(2^{n-1} - 1) < 2^n$. By Cauchy-Schwarz the left side has modulus at most
$\sqrt{M \sum_{u < M} Z(u)^2} \le \sqrt{M E_{\mathrm{src}}(n)}$, since $M \le N$ and the terms are nonnegative. $\square$

Dividing by $M |P_n(\theta)|$ and using $2^n < 2M$, $N < 2M$:

$$\frac{|\hat z_M(\theta)|}{M} \le \frac{n}{|P_n(\theta)|}\left(\sqrt{\frac{2 E_{\mathrm{src}}(n)}{N n^2}} + \frac{2}{n}\right),$$

which tends to $0$ under `SourceEnergySmallO` whenever $\liminf_n |P_n(\theta)|/n > 0$ (with $n$ the dyadic scale of
$M$, $n = \lceil \log_2 M \rceil$).

**Item 2.** $P_n(\theta) = 1 + \sum_{j=0}^{n-2} e(2^j \theta)$, a Birkhoff sum of $e(x)$ along the orbit of $\theta$
under the doubling map $x \mapsto 2x \bmod 1$. For rational $\theta$ the orbit is eventually periodic, so
$P_n(\theta)/n$ tends to the mean of $e$ over the cycle it enters. For $\theta = a / 2^k$ the orbit reaches $0$ after
$k$ steps and the limit is $1$; concretely $|P_n(a/2^k)| \ge (n - k) - k = n - 2k$. For $\theta = a / (2^k p)$ with $p$
an odd prime and $p \nmid a$, after $k$ steps the orbit is $b\,2^j / p$ with $b = a \bmod p \ne 0$, of period
$d = \mathrm{ord}_p(2)$, and the cycle mean is $\eta_b / d$ with the Gauss period
$\eta_b = \sum_{h \in H} \zeta^{bh}$, $H = \langle 2 \rangle \le (\mathbb{Z}/p)^\times$, $\zeta = e(1/p)$. It is not zero:
the automorphism $\zeta \mapsto \zeta^g$ of $\mathbb{Q}(\zeta)$ sends $\eta_b$ to $\eta_{bg}$, so every $\eta_{b'}$ with
$p \nmid b'$ is a Galois conjugate of $\eta_b$; if $\eta_b = 0$ all of them vanish, but
$\sum_{b' \in (\mathbb{Z}/p)^\times} \eta_{b'} = d \sum_{x \in (\mathbb{Z}/p)^\times} \zeta^{x} = -d \ne 0$. $\square$

The limits are $-1/2$ at $1/3$, $-1/4$ at $1/5$ and $(-1 + i\sqrt7)/6$ at $1/7$ (`cycle_average`, tested against these
closed forms and nonzero for every $a / (2^k p)$ with $k \le 2$ and $p \le 47$ or $p = 73$).

**Item 3.** For $q = 2^k$ or $2^k p$, every fraction $b / q$ reduces to a denominator $2^{k'}$ or $2^{k'} p$, so item 2
gives $\hat z_M(b/q) = o(M)$ for each of the $q$ values of $b$ (for $b = 0$ this is Problem 2). By finite Fourier
inversion $\sum_{t < M,\ t \equiv r} z(t) = q^{-1} \sum_{b=0}^{q-1} e(br/q)\, \hat z_M(b/q) = o(M)$, and the class has
$M/q + O(1)$ elements, so its black fraction tends to $1/2$.

The integer bound for $q = 2^k$: put $f$ in place of $e(-u\theta)$ in the computation of item 1. For $s = 0$ and
$s = 2^j$ with $j \ge k$ (there are $n - k$ of them), $f(t - s) = f(t)$, so each contributes
$\sum_{t<M} z(t) f(t)$ up to $2s$; the $k$ shifts $2^j$ with $j < k$ contribute at most $M$ each; Cauchy-Schwarz with
$|f| \le 1$ bounds the left side by $\sqrt{M E_{\mathrm{src}}(n)}$. $\square$

**Item 4.** Suppose $c(t + L) = c(t)$ for all $t \ge T$, with $L = 2^a q$ and $q$ odd. On the class $t \equiv r \pmod{2^a}$
the sequence $k \mapsto c(r + 2^a k)$ has period $q$ from some point on, so among its first $K$ terms the black ones
number $wK/q + O(q + T)$, with $w$ the black cells in one period. As $q$ is odd, $w/q \ne 1/2$, against item 3 at
modulus $2^a$; for $a = 0$ this is the density 1/2 of Problem 2. $\square$ The kit's main branch has the same last step as
`Rule30P2Bridge.problem1_of_dyadic_subseq_densityHalf` (density 1/2 on one class mod $2^a$ for every $a \ge 1$ gives
Problem 1); the step from `SourceEnergySmallO` to those classes is items 1 and 3.

**Item 5.** For $z(t) = (-1)^t$ and $u < N - 2^{n-2}$ every shift is in range, $z(u + 1) = -z(u)$ and $z(u + 2^j) = z(u)$
for $j \ge 1$, so $Z(u) = (n - 2) z(u)$ and $E_{\mathrm{src}}(n) \ge \frac34 N (n-2)^2$. More generally, by items 1 and 2, if
$|\hat z_M(\theta)| \ge \varepsilon M$ for infinitely many $M$ at some $\theta = a/(2^k p)$, then
$E_{\mathrm{src}}(n) \ge c N n^2$ for infinitely many $n$ (some $c > 0$), so `SourceEnergySmallO` fails, whatever the
density. $\square$

**Item 6.** Write $m(t) = \delta \cos(2\pi t/9) = \mathbb{E} z(t)$. The doubling orbit of $1/9$ is periodic of length 6
from $j = 0$ and its six values $e(2^j/9)$ are the primitive ninth roots of unity, with sum $\mu(9) = 0$; so every sum
of $e(s/9)$ over a prefix of $S_n$ (in increasing order) has modulus at most 6. For each $u$ the shifts in range form
such a prefix, so $|\mathbb{E} Z(u)| = |\mathrm{Re}\, \delta\, e(u/9) \sum_{s} e(s/9)| \le 6\delta$, and
$\mathrm{Var}\, Z(u) \le n$; hence $\mathbb{E} E_{\mathrm{src}}(n) \le N(n + 36)$. Changing one cell changes $Z(u)$ by 2
for at most $n$ values of $u$, and each $Z(u)^2$ by at most $4n$, so by McDiarmid's inequality
$\Pr[E_{\mathrm{src}}(n) \ge \mathbb{E} E_{\mathrm{src}}(n) + N n^{3/2}] \le \exp(-2 N^2 n^3 / (16 N n^4)) =
\exp(-2^n/(8n))$, which is summable. By Borel-Cantelli, almost surely $E_{\mathrm{src}}(n) \le N(n + 36 + n^{3/2})$ for
all large $n$, which is $o(N n^2)$. The class fractions follow from the strong law of large numbers, since
$\sum_{r=0}^{8} \cos(2\pi r/9) = 0$ and $\sum_{m=0}^{2} \cos(2\pi (r_0 + 3m)/9) = 0$. $\square$ For $\delta = 1/2$ and
$t < 2^{18}$ one sample has $E_{\mathrm{src}} / (N n^2) = 0.049$ and black fraction 0.251 on $t \equiv 0 \pmod 9$
(`planted_nine`); the largest $|P_n(1/9)|$ for $n \le 200$ is 2.53.

## What the inequality does not see

- **Frequency $1/9$.** The doubling orbit of $1/9$ is all of $(\mathbb{Z}/9)^\times / 9$, whose sum of $e$ is the
  Ramanujan sum $c_9(1) = \mu(9) = 0$, so $P_n(1/9)$ stays bounded and item 1 says nothing there; item 6 shows that
  the hypothesis indeed allows a bias on the classes mod 9. More generally, at every $\theta$ with $P_n(\theta)/n \to 0$ (for example
  every $\theta$ whose binary digits are normal, so almost every $\theta$; this condition already forces
  $2\theta \notin \mathbb{Z}$) the
  hypothesis allows $|\hat z_M(\theta)| / M \to \delta/2$: run the proof of item 6 with $\cos(2\pi t\theta)$ in place of
  $\cos(2\pi t/9)$. The prefix sums are $P_m(\theta)$, $m \le n$, so $\max_{m \le n}|P_m(\theta)| = o(n)$ gives
  $\mathbb{E} E_{\mathrm{src}}(n) \le N(n + o(n^2))$, the concentration step is unchanged, and by the strong law
  $\hat z_M(\theta)/M$ has the limit of $M^{-1}\sum_{t<M} \delta \cos(2\pi t\theta) e(-t\theta) \to \delta/2$. So the
  hypothesis forces $\hat z_M(\theta) = o(M)$ when $\liminf_n |P_n(\theta)|/n > 0$ and does not when
  $P_n(\theta)/n \to 0$; the frequencies with $\liminf$ zero and $\limsup$ positive are not settled here.
- **Source signs as dyadic differences of the binomial transform.** Over GF(2), $(1 + E)^{2^j} = 1 + E^{2^j}$ by Lucas's theorem, so
  the source sign $z(u) z(u + 2^j) = (-1)^{c(u) + c(u + 2^j)}$ is $(-1)$ to the $2^j$-th iterated finite difference of
  $c$ at $u$, and with $\gamma$ the binomial transform of [BinomialDuality](../../Rule30Open/Complexity/BinomialDuality.md),
  $c(u) + c(u + 2^j) = \sum_{i \subseteq u} \gamma(i + 2^j) \pmod 2$ (tested to $u < 192$, $j \le 5$). So
  $|Z(u)| = |n_u - 2 w(u)|$, where $n_u$ counts the shifts in range and $w(u)$ the $j$ with $c(u + 2^j) \ne c(u)$: the
  hypothesis says that for most $u$ about half of the cells $c(u + 2^j)$ differ from $c(u)$, in mean square. Remark, not a
  proved statement: the identity relabels the hypothesis and gives no weaker one, since the duality exchanges statements linear over GF(2) (periods), while $E_{\mathrm{src}}$ is
  a quadratic form over the integers in the signs, which the binomial transform does not preserve.
- **Which lag sets give Problem 2 alone.** Item 1 holds for any finite shift set $S$ with $\sum_{s \in S} s$ in place of
  $2^{n-1} - 1$. A small energy forces $\hat z_M(\theta) = o(M)$ wherever $|P_S(\theta)| \gg |S|$; a lacunary $S$ has
  that at every $a/(2^k p)$, an interval $S = [0, H)$ only near $\theta = 0$. The kit's equivalent forms of Problem 2
  are block energies, the interval case (`Rule30P2Bridge`).

## What remains

The open statement is unchanged: no bound on $E_{\mathrm{src}}$ for the center column is known. Items 3 and 4 show what
any proof of it must deliver along the way: density 1/2 on every progression mod $2^k$ and mod $2^k p$, and no eventual
period. So the source-energy route is not a route to Problem 2 that avoids Problem 1; it contains it.

## Kit

`SourceEnergySmallO`, `Esrc`, `problem2_of_source_energy` and the frequency-zero inequality are in
`Rule30SourceEnergy` on the kit's main branch (commit 268488d); `problem1_of_dyadic_subseq_densityHalf` is in its
`Rule30P2Bridge`. Neither module is in the pinned kit, and neither branch has the Fourier inequality for
$\theta \ne 0$, the progressions of item 3 or the implication of item 4 from `SourceEnergySmallO`. The pinned kit's
`Rule30Equivalents.ProblemTwo.problem1_of_density_on_progressions` gives Problem 1 from density 1/2 on every
progression, which item 3 supplies only for moduli $2^k$ and $2^k p$; item 4 needs only the moduli $2^k$.

## Reproduce

```bash
python -m computations.source_energy               # n = 8 .. 18: energies, class biases, Fourier coefficients (10 s)
python -m pytest tests/test_source_energy.py
```
