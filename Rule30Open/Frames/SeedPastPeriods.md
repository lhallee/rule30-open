---
title: The periods of the single cell's past grow without bound
category: frames
problems: [1]
status: proved
lean: Rule30Open.Frames.SeedPastPeriods
headline: [phiF_topAt, rho_not_evZero, rho_iter, agree_of_period, pigeonhole, rho_period_bound, rho_no_short_period]
kit: refines
kit_modules: [Rule30Equivalents.TFunctionCycles]
---

# The periods of the single cell's past grow without bound

[SeedPast](SeedPast.md) proves that the single black cell has exactly one predecessor $\rho_k$ at each depth $k$ in the
moving frame, and that each $\rho_k$ repeats with some period far to the left. Here: one step back or more, $\rho_k$ is
not white far out, and a period of $p$ cells forces $k \le 2^p$, so the periods are unbounded. These are the second and
third facts of [the finding](../../findings/frames/seed-past.md), now proved in general.

## Statement

1. **Infinitely many black cells** (`rho_not_evZero`). For $k \ge 1$, $\rho_k$ is not white from any bit on.
2. **The bound** (`rho_period_bound`). If $\rho_k$ repeats with period $p > 0$ from some bit on, then $k \le 2^p$.
3. **Unbounded periods** (`rho_no_short_period`). Once $k > 2^p$, $\rho_k$ has no period of $p$ cells or fewer, from
   any bit on.

## Argument

1. **The top black cell moves up** (`phiF_topAt`). If bit $n$ of $y$ is its highest black bit, bit $n + 2$ of $\varphi(y)$
   is $0 \oplus (0 \lor 1) = 1$ and every higher bit is white. After $k$ steps the top is at $n + 2k$ (`phiIter_topAt`),
   so a row white far out with a black bit never reaches the single cell, whose top is bit 0, in $k \ge 1$ steps; a white
   row stays white (`phiIter_white`). Since $\varphi^k(\rho_k)$ is the single cell, statement 1 follows.
2. **Periods move out two cells per step** (`phiF_period`, `rho_sub_period`). Bit $j$ of $\varphi(y)$ reads bits
   $j, j - 1, j - 2$, so a period from bit $N$ is a period of $\varphi(y)$ from bit $N + 2$. Since $\rho_{k-m}$ is
   $\varphi^m(\rho_k)$ (`rho_iter`), all of $\rho_k, \rho_{k-1}, \dots, \rho_1$ repeat with period $p$ from bit
   $M = N + 2k$.
3. **Their windows are distinct.** Read bits $M, \dots, M + p - 1$ of each as a number below $2^p$ (`window`,
   `window_lt`). If $\rho_{k-a}$ and $\rho_{k-b}$, $a < b < k$, had the same window, they would agree from bit $M$ on,
   both having period $p$ there (`window_inj`, `agree_of_period`). After $k - b$ steps the second is the single cell
   and the first is $\rho_{b-a}$; two rows that agree from bit $M$ agree from bit $M + 2$ after a step (`agree_iter`), so
   $\rho_{b-a}$ would be white far out, against statement 1.
4. **Pigeonhole** (`pigeonhole`). $k$ distinct numbers below $2^p$ need $k \le 2^p$.

## What it covers

On a ring of $p$ cells the window evolves by Rule 30 followed by a rotation, since the row has period $p$ there, and the
argument says that it is nonzero for $k$ steps and white at step $k$: the tail of $\rho_k$ dies on its ring in exactly
$k$ steps, the paper argument of the finding. The computed table of periods, 1, 3, 6, 12, 24 and 48, first reached at
$k$ = 1, 2, 4, 10, 18 and 66 and still 48 at $k = 3{,}000$, stays a computation
([computations/frames.py](../../computations/frames.py)); the bound $p \ge \log_2 k$ is far below those values. As for
SeedPast, the past exists whatever the center column does later, so this gives no constraint toward Problem 1 by
itself.

## Relation to the kit

The kit's equivalent forms prove that every nonzero finite configuration has unbounded cycle lengths modulo $2^n$ in
the frame of its right edge
([`TFunctionCycles`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/equivalents/Rule30Equivalents/TFunctionCycles.lean),
`per_unbounded`), a statement about the forward orbit; this one is about the backward orbit of the single cell, and
uses only the definitions of SeedPast.

## Lean

`Rule30Open.Frames.SeedPastPeriods`: `TopAt`, `phiF_topAt`, `phiIter_topAt`, `phiIter_white`, `exists_top`, `EvZero`,
`rho_not_evZero`, `phiF_period`, `phiF_rho_succ`, `rho_iter`, `rho_sub_period`, `phiF_agree`, `agree_iter`,
`agree_of_period`, `window`, `window_lt`, `window_split`, `window_inj`, `pigeonhole`, `rho_period_bound` and
`rho_no_short_period`.
