---
title: No linear or learned projection tells the chaotic region of the single cell from the invariant measure
category: statistics
problems: [2]
status: negative
kind: no-signal
evidence: [computations/projections.py]
---

# No linear or learned projection tells the chaotic region of the single cell from the invariant measure

**Question.** Rule 30 is onto, so the uniform Bernoulli measure on rows is invariant, and under it a space-time patch
of $h$ rows and $w$ cells is the image of a uniform row of $w + 2(h - 1)$ cells. Do the patches of the single black
cell's diagram, read at position $x$ and time $t$, follow that law? A local deviation anywhere in the chaotic region,
seen by a covariance (PCA) spectrum, a trained classifier, an autoencoder or a neighbor graph, would be structure that
the tests of the center column alone ([randomness tests](randomness-tests.md), [compression](compression.md)) cannot
see; a deviation near $x = 0$ would bear on Problem 2. The same question is asked of two matrix forms of the center
column that those tests did not use.

**Setup.** Times $t$ from $2^{14}$ to $2^{17}$, every 256 steps (16 for the edge), left ends $x$ on a lattice with a
random offset whose stride makes the base rows of patches in one row disjoint, so that under the invariant measure
those patches are independent. Each statistic is computed three ways: for the single cell, binned by $x / t$ or by the
distance $d = t - x$ to the right edge; for a **control diagram** run from a uniform random row with the same
geometry, whose patches have exactly the invariant law and the same dependence between samples; and for a
**planted** sample, invariant patches of which 10% are taken over rows of density 0.6.

- **Exact test.** For patches of $4 \times 8$ (5,120 patterns, by enumerating all $2^{14}$ base rows) and $6 \times 6$
  (7,936 patterns), Pearson's statistic of the counts in each bin against the exact law, standardized by its exact
  mean $K - 1$ and variance under independent sampling, and $\hat D = (X^2 - (K - 1)) / n$, an unbiased estimate of
  the chi-square divergence $\chi^2(q \| p)$. Since $\mathrm{TV}(q, p) \le \tfrac12 \sqrt{\chi^2(q \| p)}$, a bound on
  $\hat D$ bounds the held-out accuracy $\tfrac12 + \tfrac12 \mathrm{TV}$ of every classifier of patches of that size.
- **Projections**, on patches of $8 \times 16$ (base rows of 30 cells, too many to enumerate), 20,000 per set:
  the distance of the second-moment matrix from that of 400,000 invariant patches and its top eigenvalue; held-out
  accuracy of gradient boosting and of an MLP (128, 64) trained to tell the set from fresh invariant patches (a quarter
  held out, standard error 0.005); the reconstruction error of an MLP autoencoder $128 \to 64 \to 16 \to 64 \to 128$
  trained on 50,000 invariant patches, as a Welch standard score against held-out invariant patches; and Schilling's
  nearest-neighbor two-sample test ($k = 10$, standard score against 200 relabelings) on 5,000 + 5,000 patches in the
  raw space and on 1,000 + 1,000 in a two-dimensional t-SNE embedding.

**Outcome: the profile across $x / t$.** Two phases and a sharp front, with no local deviation in the chaotic phase.

| Region, patches of $4 \times 8$ | Bins of width 0.05 | Patches per bin | $z$ | $\hat D$ (sd 0.00086) |
|---|---:|---:|---|---|
| $-1 \le x/t < -0.25$, regular | 15 | 118,000 | 74.6 to 1,194 | 0.064 to 1.03 |
| $-0.25 \le x/t < 0.95$, chaotic | 24 | 118,000 | $-0.93$ to 2.24 | at most 0.0019 |
| $0.95 \le x/t < 1$, edge layer inside | 1 | 118,000 | 195 | 0.17 |
| Control diagram, every bin | 40 | 118,000 | $-2.48$ to 2.41 | at most 0.0021 |

Pooled over $-0.2 \le x/t < 0.9$ (2,601,028 patches) the single cell gives $z = -0.24$, $\hat D = -0.000009 \pm 0.000039$,
and the control $z = -0.12$. Patches of $6 \times 6$ agree: chaotic bins $z$ from $-0.99$ to 1.89 on 103,000 patches
each, pooled $\hat D = -0.000056 \pm 0.000055$ on 2,275,877 (control: every bin within $-3.16$ to 2.31, pooled
$-0.000097 \pm 0.000055$). The planted contamination has $\chi^2 = 0.0062$ on $4 \times 8$ patches (exact, by
weighting the enumeration), which this test would see at about $z = 7$ in a single bin. So in every bin of width 0.05
between $x/t = -0.25$ and $0.95$, $\chi^2 \lesssim 0.0036$ and no classifier of $4 \times 8$ patches beats about
0.515 held-out accuracy; pooled over the chaotic region, about 0.502 (a heuristic bound: two standard deviations of
$\hat D$ under independent sampling, which the control diagram supports).

- **The front is at $x / t \approx -1/4$, not $-1/3$.** At resolution 0.01 and $t$ from $2^{16}$ to $2^{17}$ (18,000
  patches per bin), $\hat D$ stays between 0.076 and 0.145 from $x/t = -0.5$ to $-0.25$ and drops to noise ($|z| \le
  2.1$) in the next bin; the band from $2^{15}$ to $2^{16}$ (4,500 patches per bin) puts the drop in the same bin,
  and the band from $2^{14}$ to $2^{15}$ (1,140 per bin) is too small to resolve it. A direct computation of the diagonals
  locates it: with $\mathrm{onset}(j)$ the least $s$ with $D_j(t + 16) = D_j(t)$ for $s \le t \le 2^{17} - 16$, the
  first diagonal not yet repeating at $t = 2^{14}, 2^{15}, 2^{16}$ sits at $x/t = -0.2502, -0.2534, -0.2520$; the
  median of $\mathrm{onset}(j)/j$ is 1.3302 to 1.3407 on each dyadic range of depths from 4,096 to 79,999, and its
  largest value there is 1.3455 (depth 28,584). So the left diagonals start repeating at about $4j/3$, and the regular
  phase is the cone $x < -t/4$. No diagonal $8 \le j < 80{,}000$ has $\mathrm{onset}(j) > \lceil 3j/2 \rceil$ (every
  onset is at most 126,976, confirmed by at least 4,096 later steps), which extends the direct check of
  [the settled-runs hypothesis](../../findings/diagonals/settled-runs.md) from depth 7,999 to depth 79,999, on times up
  to $2^{17}$.
- **The right edge has a boundary layer about 38 cells wide, a width in cells, not in $x / t$.** Patches of $3 \times 4$ (128 patterns,
  about 900 per distance $d$) fail the exact test at every $d \le 34$ ($z$ from 4.96 to 7,217) and pass from $d = 35$
  on, apart from $z = 2.27$ and 3.22 at $d = 37, 38$; each wider bin from 40 to 4,096 has $|z| \le 1.73$ with up to
  1.8 million patches. The layer is made of the right diagonals $R_k(t) = \mathrm{cell}(t, t - k)$, which are
  periodic from the start with period $2^k$ (the kit's `Rule30Diagonals.R_periodic`), so their law does not change
  with $t$; over the times 32,768 to
  65,535 their least periods are 4,096 at $k = 29$ to 33, 8,192 at $k = 34$ and 35, and above 8,192 from $k = 36$.
  A patch at distance $d$ covers the diagonals $d - 3$ to $d + 2$, so the test stops seeing the layer about where the
  periods pass 8,192.

**Outcome: the projections** ($8 \times 16$ patches; invariant reference eigenvalues from 2.89 down to 0.255, so the
null PCA spectrum is far from flat; covariance distance of 20,000 invariant patches $0.927 \pm 0.021$).

| Set | Cov. distance | GB | MLP | Autoencoder $z$ | kNN $z$ | t-SNE kNN $z$ |
|---|---:|---:|---:|---:|---:|---:|
| $x/t \in [-0.85, -0.75)$, regular | 1.184 | 0.597 | 0.621 | $-0.03$ | 3.12 | 3.08 |
| $[-0.40, -0.35)$, regular | 1.050 | 0.521 | 0.543 | 1.22 | $-0.39$ | $-0.31$ |
| $[-0.35, -0.30)$, regular | 1.035 | 0.517 | 0.548 | 0.63 | 0.87 | 0.07 |
| $[-0.30, -0.25)$, regular | 1.011 | 0.515 | 0.544 | $-0.21$ | 1.17 | 0.88 |
| $[-0.20, -0.10)$ | 0.920 | 0.514 | 0.503 | $-0.44$ | $-1.24$ | 0.74 |
| $[-0.05, 0.05)$ | 0.921 | 0.496 | 0.498 | $-0.77$ | $-0.80$ | 0.36 |
| $[0.40, 0.50)$ | 0.919 | 0.493 | 0.500 | 0.09 | $-0.44$ | 0.42 |
| $[0.90, 0.95)$ | 0.932 | 0.505 | 0.493 | $-1.87$ | $-0.06$ | $-0.42$ |
| Control diagram, $[-0.05, 0.05)$ | 0.909 | 0.499 | 0.508 | $-1.00$ | 1.41 | $-1.01$ |
| Planted, 10% at density 0.6 | 0.967 | 0.501 | 0.499 | 0.14 | $-0.35$ | 0.93 |

Refit three times on 40,000 patches per set with half held out (standard error 0.0025), gradient boosting scores
0.4978 to 0.5009 on the bins $[-0.20, -0.10)$ and $[-0.05, 0.05)$, and 0.4969 to 0.4998 on the control: the 0.514 in
the table is a fluctuation of one fit.

The projections are much weaker instruments than the exact test: they see the regular phase (covariance distance 4 to
12 standard deviations, the MLP at 0.54 to 0.62), but the autoencoder misses it entirely, the neighbor tests see only
the far left, and none clearly sees the planted contamination (the covariance distance at 1.9 standard deviations is
the most) that the exact test would find at $z \approx 7$.
With 25% and 50% of the patches planted (exact $\chi^2$ on $4 \times 8$ patches 0.039 and 0.155), the covariance
distance is 1.119 and 1.511, gradient boosting 0.526 and 0.573, and the raw kNN test $z = 2.75$ and 5.54: the
projections need a contamination several times larger than one the exact test resolves in a single bin.

**Outcome: the center column as a matrix.** First $2^{20}$ cells in $\pm 1$ encoding, against 100 sequences of fair
coins each (two-sided rank $p$-values).

| Matrix | Largest eigenvalue | Smallest eigenvalue | KS distance to the reference law |
|---|---|---|---|
| Delay matrix, $L = 64$ | 1.0215 (coins $1.0166 \pm 0.0036$, $p = 0.18$) | 0.9769 ($0.9835 \pm 0.0028$, $p = 0.040$) | 0.102 ($0.082 \pm 0.017$, $p = 0.28$) |
| Delay matrix, $L = 256$ | 1.0482 ($1.0390 \pm 0.0053$, $p = 0.16$) | 0.9601 ($0.9616 \pm 0.0051$, $p = 0.65$) | 0.032 ($0.041 \pm 0.009$, $p = 0.30$) |
| Rows of $r = 1{,}024$ | 3.9234 ($3.9586 \pm 0.0319$, $p = 0.34$) | 0 (hard edge) | 0.0029 ($0.0031 \pm 0.0003$, $p = 0.54$) |
| Rows of $r = 2{,}048$ | 2.2085 ($2.2249 \pm 0.0167$, $p = 0.32$) | 0.2485 ($0.2545 \pm 0.0039$, $p = 0.12$) | 0.0047 ($0.0056 \pm 0.0007$, $p = 0.12$) |
| Rows of $r = 2{,}047$ | 2.2256 ($2.2306 \pm 0.0162$, $p = 0.79$) | 0.2558 ($0.2540 \pm 0.0042$, $p = 0.71$) | 0.0050 ($0.0056 \pm 0.0006$, $p = 0.28$) |
| Rows of $r = 4{,}096$ | 1.5453 ($1.5495 \pm 0.0114$, $p = 0.79$) | 0.5643 ($0.5693 \pm 0.0056$, $p = 0.46$) | 0.0090 ($0.0103 \pm 0.0013$, $p = 0.38$) |

The delay matrix $H[i, k] = c(i + k)$ gives $\frac1K H H^{\mathsf T}$, the Toeplitz matrix of the sample
autocorrelations up to lag $L - 1$; its reference law is the pooled spectrum of 20 coin sequences, because for coins
it is not the Marchenko-Pastur law: at $L = 256$ the coin spectrum spans 0.9597 to 1.0417 against the law's support
0.9690 to 1.0315 (KS distance 0.063). The column cut into $2^{20}/r$ rows of $r$ cells has independent entries under
the null, and its reference is the Marchenko-Pastur law with ratio $\min(m, r)/\max(m, r)$. The smallest of the 17
informative $p$-values is 0.040, as expected among 17.

**What it means.** Up to the resolution stated, the single cell's diagram is in local equilibrium with the invariant
measure everywhere right of the front $x = -t/4$ and more than about 38 cells inside the right edge, including near
$x = 0$: no patch statistic, linear or learned, separates it from the control diagram, and the exact test bounds what
any classifier of $4 \times 8$ or $6 \times 6$ patches could find. The structure the projections do find is the
structure already known: the periodic left diagonals, now located at $x/t \approx -1/4$ with onsets near $4j/3$, and
the periodic right diagonals. None of this reaches the single cell's column beyond the range tested or proves anything
about density; it says that the chaotic region offers no local statistical handle of these kinds. The matrix forms of
the column add nothing to the [randomness tests](randomness-tests.md): the spectrum of the delay matrix is close to a
smoothed periodogram, whose null is not the Marchenko-Pastur law.

**Reproduce.**

```bash
python -m computations.projections profile                     # 4 x 8 profile, about 1 min
python -m computations.projections profile --height 6 --width 6 --bands 1   # about 30 s
python -m computations.projections edge                        # right edge and its diagonals, about 1 min
python -m computations.projections front                       # onsets to depth 80,000, about 1 min
python -m computations.projections learned                     # projections, about 40 min on a loaded 4-core machine
python -m computations.projections recheck                     # refits and stronger plants, about 12 min
python -m computations.projections column                      # column spectra, about 20 min
```

[tests/test_projections.py](../../tests/test_projections.py) checks the patches against direct runs of the rule, the
exact law against plain enumeration, the covariance against its closed form ($-1/2$ between $(t + 1, x)$ and
$(t, x - 1)$, which is the kit's `measure_diag_eq` in `Mixing`), the chi-square moments against multinomial draws, the streamed onsets against a full table and the
settling constants of [settled runs](../../findings/diagonals/settled-runs.md), the right diagonals' periods against
a spacetime run, and the column matrices against direct products and the Marchenko-Pastur law. The sklearn
classifiers, autoencoder and t-SNE are not in the suite (importing sklearn alone takes most of a file's budget); the
regular bins of the `learned` command are their positive control.
