---
title: The periods and preperiods of the single cell's past, to depth 3,000, checked in the kernel
category: frames
problems: [1]
status: proved
lean: Rule30Open.Frames.SeedPastTable
headline: [phiIter_period, phiIter_eq_rho, tailPeriod_gcd, minTailPeriod_dvd, rho_min_period_dvd, seedCerts_ok, seedCerts_rho, rho_min_period, rho_period_dvd_of_ge, rho_preperiod_small, rho_preperiods, rho_two, rho_ten, rho_twentyEight, ring48_dies]
kit: new
kit_modules: [Rule30Equivalents.TFunctionCycles]
evidence: [computations/seed_past_lean.py, computations/frames.py]
---

# The periods and preperiods of the single cell's past, to depth 3,000, checked in the kernel

[The seed's past](../../findings/frames/seed-past.md) computes the row $\rho_k$ that becomes the single black cell
after $k$ steps in the moving frame, with its period and preperiod, for $k \le 3{,}000$. [SeedPast](SeedPast.md) proves
that every $\rho_k$ repeats from some bit on, and [SeedPastPeriods](SeedPastPeriods.md) that the periods are unbounded.
This module proves the computed table itself, with the Lean kernel checking stored certificates.

## Statement

Say that $\rho_k$ has **least period** $p$ when it repeats with period $p$ from some bit on and with no smaller
period from any bit on (`MinTailPeriod`), and **preperiod** $N$ for $p$ when it repeats with period $p$ from bit $N$
and from no earlier bit (`IsPreperiod`).

1. **Least periods** (`rho_min_period`). For $1 \le k \le 3{,}000$ the least period of $\rho_k$ is

   | $k$ | 1 | 2, 3 | 4 to 9 | 10 to 17 | 18 to 65 | 66 to 3,000 |
   |---|---:|---:|---:|---:|---:|---:|
   | least period | 1 | 3 | 6 | 12 | 24 | 48 |

2. **Preperiods** (`rho_preperiod_small`, `rho_preperiods`). For $1 \le k \le 28$ the preperiod is 0 or 1; at
   $k$ = 30, 66, 300, 1,000 and 3,000 it is 4, 188, 1,509, 4,968 and 15,615.
3. **Examples** (`rho_one` in [SeedPastRing](SeedPastRing.md), `rho_two`, `rho_ten`, `rho_twentyEight`). Reading bit
   0 first, $\rho_1$ is all black, $\rho_2$ is the word $100$ repeated, $\rho_{10}$ the word $100100010010$ repeated,
   and $\rho_{28}$ the word $100010011101010111000110$ repeated, each from bit 0. (In Lean a word is a number whose
   binary digits are the word reversed, as `0b010010001001` for $\rho_{10}$.) With
   [SeedPastRing](SeedPastRing.md) (`seedRow_evolve`), the last repeated leftward from a cell, white right of it,
   becomes exactly one black cell after 28 steps.
4. **Rings of 48 cells** (`ring48_dies`). For every $k$ from 66 to 3,000 there is a row of period 48 that Rule 30
   turns all white in exactly $k$ steps, and not before.
5. **Divisibility** (`rho_min_period_dvd`, `rho_period_dvd_of_ge`). For every $k$, the least period of $\rho_k$
   divides that of $\rho_{k+1}$. For every $k \ge 66$, beyond the checked range too, every period of $\rho_k$ is a
   multiple of 48.

## Argument

1. **Certificates** (`seedCerts`, `SeedTable.bits`). A certificate $(k, N, P, a, w)$ claims that bit $j$ of $\rho_k$
   is bit $j$ of $a$ for $j < N$ and bit $(j - N) \bmod P$ of $w$ for $j \ge N$. The list holds one for each
   $k \le 66$ and for $k$ = 300, 1,000 and 3,000, written by
   [computations/seed_past_lean.py](../../computations/seed_past_lean.py) from `frames.seed_past`.
2. **Links** (`SeedTable.linkOk`, `SeedTable.link_sound`). For consecutive certificates of $k$ and $k + d$, with
   periods $P_0$ and $P_1$ and preperiods $N_0$ and $N_1$, the kernel checks that $P_0$ divides $P_1$ and that $d$
   steps of $\varphi(y) = y \oplus (2y \lor 4y)$, computed modulo $2^B$ on the first $B = \max(N_1 + 2d, N_0) + P_1$
   bits (`SeedTable.expand`, `SeedTable.iterW`), take the upper certificate to the lower one. A period of a row from
   bit $N$ is a period of its image from bit $N + 2$ (`phiF_period`, `phiIter_period`), so both sides repeat with
   period $P_1$ from bit $B - P_1$; they agree on the full period below $B$, hence everywhere (`agree_of_period`).
   So $\varphi^d$ takes the upper row to the lower one exactly.
3. **The chain** (`SeedTable.chain_sound`, `seedCerts_ok`, `seedCerts_rho`). The certificate $(0, 1, 1, 1, 0)$ is the
   single cell, $\rho_0$. A row that $d$ steps take to $\rho_k$ is $\rho_{k+d}$, since $\varphi$ is a bijection
   (`phiIter_eq_rho`). Along the chain of links every certificate is the row $\rho_k$ of its depth.
4. **Minimality** (`SeedTable.minPerOk`, `SeedTable.preOk`, `SeedTable.cert_facts`). For each $q$ with $0 < q < P$ the
   kernel finds a bit $N + r$, $r < P$, with bit $N + r + q$ different; if $q$ were a period from some bit $N'$, then
   shifting both bits by a multiple of $P$ past $N'$ would make them equal. And bit $N - 1$ differs from bit
   $N - 1 + P$, so the period $P$ does not start before $N$.
5. **Between certificates** (`rho_sub_period`). $\varphi^{k'-k}(\rho_{k'}) = \rho_k$ and a period passes to the image,
   so a period of $\rho_{3000}$ is one of every $\rho_k$ with $k \le 3{,}000$, and a period of $\rho_k$ with $k \ge 66$
   is one of $\rho_{66}$. The least periods of $\rho_{66}$ and $\rho_{3000}$, both 48, give it for every $k$ between.
6. Statement 4 is [SeedPastRing](SeedPastRing.md) (`rho_tail_dies`) applied to $\rho_k$ with its period 48.
7. **Divisibility.** If $a \le b$ are periods from bit $N$, so is $b - a$ (`tailPeriod_sub`); by Euclid's algorithm
   so is $\gcd(a, b)$ (`tailPeriod_gcd`). A least period $q$ and any period $p$ therefore give the period
   $\gcd(q, p) \le q$ far enough out, which must be $q$, so $q$ divides $p$ (`minTailPeriod_dvd`). A period of
   $\rho_{k+1}$ from bit $N$ is a period of $\varphi(\rho_{k+1}) = \rho_k$ from bit $N + 2$, so the least period of
   $\rho_k$ divides every period of $\rho_{k+1}$. For $k \ge 66$ a period of $\rho_k$ is one of $\rho_{66}$
   (`rho_sub_period`), so 48 divides it (`rho_period_dvd_of_ge`).

The module builds in under 5 seconds. Each step of a link is a handful of shifts, masks and comparisons on numbers
of at most 19,663 bits, which the kernel evaluates with its built-in arithmetic; the longest link, from depth 3,000 to
1,000, has 2,000 steps.

## What it covers

This is the table of [the finding](../../findings/frames/seed-past.md), proved in its stated range; with
[SeedPast](SeedPast.md), [SeedPastPeriods](SeedPastPeriods.md) and [SeedPastRing](SeedPastRing.md) every statement of
the finding is proved in Lean, with $\rho_1$ and $\rho_2$ as bit sequences rather than 2-adic numbers. Past
$k = 3{,}000$ the least period is not determined here: it is a multiple of 48 for every $k \ge 66$ (`rho_period_dvd_of_ge`),
and [SeedPastPeriods](SeedPastPeriods.md) gives the general bound $k \le 2^p$. The past exists whatever the center
column does later, so the table gives no constraint toward Problem 1 by itself.

## Relation to the kit

The kit's equivalent forms prove that every nonzero finite configuration has unbounded cycle lengths modulo $2^n$ in
the frame of its right edge
([`TFunctionCycles`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/equivalents/Rule30Equivalents/TFunctionCycles.lean),
`per_unbounded`), a statement about the forward orbit. Neither the pinned kit nor its current main branch has the
backward orbit of the single cell, its periods or its preperiods.

## Lean

`Rule30Open.Frames.SeedPastTable`: `TailPeriod`, `MinTailPeriod`, `IsPreperiod`, `phiIter_period`, `phiIter_eq_rho`,
`tailPeriod_mono`, `tailPeriod_mul`, `tailPeriod_sub`, `tailPeriod_gcd`, `minTailPeriod_dvd`, `rho_min_period_dvd`;
in `SeedTable`, `bits`, `bits_period`, `rep`, `rep_testBit`, `expand`, `expand_testBit`, `stepW`, `stepW_testBit`,
`iterW`, `iterW_testBit`, `linkOk`, `link_sound`, `chainOk`, `chain_sound`, `certOf`, `certOf_mem`, `checkBelow`,
`checkBelow_spec`, `minPerOk`, `minPer_sound`, `preOk`, `pre_sound` and `cert_facts`; then `seedCerts`, `seedCerts_ok`,
`seedCerts_rho`, `seedPeriod`, `seedPeriod_of_ge`, `factOk`, `factOk_sound`, `smallOk`, `smallOk_all`, `rho_small`,
`fact_30`, `fact_66`, `fact_300`, `fact_1000`, `fact_3000`, `rho_min_period`, `rho_period_dvd_of_ge`,
`rho_preperiod_small`, `rho_preperiods`,
`rho_two`, `rho_ten`, `rho_twentyEight` and `ring48_dies`.
