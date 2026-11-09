---
title: For 11 ≤ a ≤ 13 the a leftmost cells of the cone are pairwise distinguishable at every t ≥ 19, 21, 24, by white and single black cell completions, so left-to-right ordered decision diagrams of the center have width 2^a at level a for every such t
category: complexity
problems: [3]
status: proved
lean: Rule30Open.Complexity.LateSeedCutWide
headline: [late_seed_cut_wide, late_seed_width_wide, lateSep_11, lateSep_12, lateSep_13]
kit: new
kit_modules: [Rule30Diagonals]
evidence: [computations/late_seed_cut.py, tests/test_late_seed_cut.py]
---

# For 11 ≤ a ≤ 13 the a leftmost cells of the cone are pairwise distinguishable at every t ≥ 19, 21, 24, by white and single black cell completions, so left-to-right ordered decision diagrams of the center have width 2^a at level a for every such t

The statement and the argument are those of [LateSeedCut](LateSeedCut.md), with more cells; only the kernel checks are
new. Write $c_t$ for the center after $t$ steps, $\mathrm{splice}_b(x, z)$ for the row equal to $x$ left of cell $b$
and to $z$ from $b$ on, and $\delta_m$ for the row white except a black cell at $m$.

## Statement

Let $11 \le a \le 13$, $t_A(a) = 19, 21, 24$ (`lateStartWide`) and $R_a = 17, 18, 17$ (`lateRWide`).

- `late_seed_cut_wide`: for every $t \ge t_A(a)$, if the rows $x$ and $y$ differ at some cell $i$ with
  $-t \le i \le -t + a - 1$, then $c_t(\mathrm{splice}_{-t+a}(x, z)) \ne c_t(\mathrm{splice}_{-t+a}(y, z))$ for $z$
  white, or for $z = \delta_m$ with $m = t - (a \bmod 2) - 2R - d$, $0 \le R \le R_a$, $d \in \{0, 1\}$,
  $R + d + \lceil a/2 \rceil \le t$.
- `late_seed_width_wide`: for every $t \ge t_A(a)$, every factorization
  $c_t(\mathrm{splice}_{-t+a}(x, z)) = G(F(x), z)$ has at least $2^a$ states: an ordered binary decision diagram that
  reads the row from the left has at least $2^a$ nodes at level $a$, at every such $t$.

The thresholds are those of the family: it fails at $t_A(a) - 1 = 18, 20, 23$ (computed by
`computations/late_seed_cut.py`).

## Argument

`lateSep_all` of [LateSeedCut](LateSeedCut.md) reduces every $t \ge t_A(a)$ to the checks at
$t_A(a) \le t < t_0 + 8$, $t_0 = s_0 + R_a + 1 + \lceil a/2 \rceil$, given that the low $J = 2R_a + 3$ bits of the
single cell's left edge repeat with period 8 from $s_0$ on. Here $J = 37, 39, 37$ and $s_0 = 46, 48, 46$
(`edge_period_37`, `edge_period_39`, the least onsets), so $t_0 = 70, 73, 71$ and the checks cover
$19 \le t < 78$, $21 \le t < 81$ and $24 \le t < 79$: 59, 60 and 55 values of $t$, split into theorems of 15
(`late_checks_11_0`, ...) that the kernel checks in parallel. Each check runs the probes the last
$\lceil a/2 \rceil + R_a + 1$ steps on all $2^a$ values of the left cells at once and splits them with `refineMasks`;
the module takes about 4 minutes of processor time, most of it in `refineMasks` (13,000 splits of 8,192-bit masks for
one check at $a = 13$).

## What it means

With [LateSeedCut](LateSeedCut.md) the width $2^a$ of left-to-right ordered decision diagrams at level $a$ holds for
every $t \ge t_A(a)$ for every $a \le 13$. The probes needed grow slowly ($R_a \le 18$), and the onsets of the left edge
grow linearly with the depth $2R_a + 3$, so each further $a$ costs a few more checks of twice the size.

## Reproduce

```bash
python -m computations.late_seed_cut --scan 11 13 --tmax 100                 # t_f(a) = t_A(a) - 1 and R_a (about 1 min)
python -m computations.late_seed_cut --lean 11 13 --check 11 13 --tmax 100  # the mirrored kernel checks (about 2 min)
```
