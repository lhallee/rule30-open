---
title: Infinitely many seeds share the center column
category: seeds
problems: [1, 2, 3]
status: proved
lean: Rule30Open.Seeds.SeedExtensions
headline: [center_sigma, center_tau, sigma_difference, tau_difference, center_column]
kit: new
---

# Infinitely many seeds share the center column

The seeds $(10)^k1$ and $(10)^k11$, for every $k \ge 0$, give exactly the center column of the single black cell. So
the prize's sequence comes from infinitely many finite rows, and every statement about it holds for all of them. The
seed $11$ is the case $k = 0$ of the second family.

## Statement

Let $\sigma_k$ be the row that is 1 at the even cells $0, 2, \dots, 2k$, and $\tau_k$ the row that is also 1 at
$2k + 1$. For every $k$ and $t$:

- `center_sigma`, `center_tau`: the center columns from $\sigma_k$ and $\tau_k$ equal `Rule30Prize.center`.
- `sigma_agrees`, `tau_agrees`: both rows agree with the single cell's row at every cell left of $t$.
- `sigma_difference`, `tau_difference`: the cells where they differ, as offsets $x - t$. For $\sigma_k$: the even
  offsets $2, \dots, 2k$ at even $t$; at odd $t$ with $k > 0$, the offsets $0$, the odd ones up to $2k - 1$, and $2k$.
  For $\tau_k$: the even offsets $2, \dots, 2k$ and $2k + 1$ at even $t$; at odd $t$, the offsets $0$ and the odd ones
  up to $2k + 1$.
- `center_column`, `difference`: the seed $11$ gives the same center column, and its row differs from the single
  cell's exactly at $t + 1$, and also at $t$ when $t$ is odd.

## Argument

Follow the right edge. Each seed has two windows, functions of the offset $o = x - t$ for $o \ge -2$, with zeros
beyond them: $W_0$ is the seed itself and $W_1$ is its row at $t = 1$. For $\sigma_k$, $W_1$ reads
$1\,1\,0\,(1\,0)^{k-1}\,1\,1$ from offset $-2$ (and $1\,1\,1$ when $k = 0$, the single cell); for $\tau_k$ it reads
$1\,1\,0\,(1\,0)^k\,1$.

1. **One step swaps the windows.** If the row at time $t$ reads $W_0$ from cell $t - 2$ on, the row at $t + 1$ reads
   $W_1$ from cell $t - 1$ on, and the other way around. Cell $x \ge t - 1$ at time $t + 1$ reads cells
   $x - 1, x, x + 1 \ge t - 2$, all inside the window, so this is an identity between explicit functions of $o$:
   Rule 30 applied to $W_0$ at $o - 1, o, o + 1$ gives $W_1(o - 1)$. It holds for every $k$, and the proof splits on
   the values of the four cells involved and refutes the impossible combinations by linear arithmetic.
2. **So the rows are the windows.** By induction, the row at even $t$ reads $W_0$ and at odd $t$ reads $W_1$, from
   cell $t - 2$ on (`Windows.rows`).
3. **The windows agree with the single cell's where it matters.** All of them read $0\,0$ at offsets $-2, -1$ for even
   $t$ and $1\,1$ for odd $t$, as the single cell's windows do.
4. **Everything left of $t - 2$ agrees.** By induction on $t$: cell $x < t - 2$ at time $t$ reads cells left of
   $t - 1$ at time $t - 1$, where the rows agree by the hypothesis, and cells $t - 2$ and $t - 1$ agree by step 3
   (`Windows.agree`).

Cell 0 lies left of $t$ for every $t \ge 1$, and at $t = 0$ all three seeds are 1 there, so the center columns agree.
The difference statements read off where $W_0$ and $W_1$ differ from the single cell's windows (`Windows.difference`).

## In Lean

`sigma k` and `tau k` are the seeds, `sigmaOdd k` and `tauOdd k` their odd windows, and the structure `Windows`
packages steps 1 and 3. The four step lemmas `sigma_step`, `sigmaOdd_step`, `tau_step` and `tauOdd_step` are step 1
for every $k$, each proved by case analysis with `omega`. `seed11_eq` identifies the seed $11$ with `tau 0`.

## Why it matters

These seeds are the only right extensions of the single cell up to 40 cells that keep the center column (see
[the extension search](../../findings/seeds/no-other-extensions.md)). They also bound what a proof can use: any argument
that reconstructs the row from its center column has to lose everything right of the center, since these seeds differ
there and nowhere else. The kit's open statement `EdgeObservable`
([`Rule30TraceEdge`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/7d665044b904117af9e82328aeb90a30692b2b85/lean/Ruliology/CellularAutomata/Rule30TraceEdge.lean))
asks that finite rows with equal center columns have equal left edges; these seeds all share the left edge at 0, as it
requires.
