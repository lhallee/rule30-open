---
title: The alternating domains time the period-two condition
category: period-two
problems: [1]
status: proved
lean: Rule30Open.PeriodTwo.Domains
headline: [held_domains_odd, held_countdown, held_disagree, held_agree_stepB]
kit: independent
kit_modules: [Rule30ZeroBoundaryStripe]
---

# The alternating domains time the period-two condition

The period-two question asks for a finite half whose cell next to the held column reads 1 at every odd step
([HeldColumn.md](HeldColumn.md)). Two infinite halves do it: the alternating halves $1010\dots$ and $0101\dots$, read
outward from the column. Near them the condition is a countdown: a half that matches the first domain on exactly $k$
cells keeps the condition for exactly $k$ steps. The countdown is why the question resembles a Collatz problem, and
the domains are why any proof must use that the half is finite.

## Statement

Let $A_j = 1$ for even $j$ and $B_j = 1$ for odd $j$; as 2-adic numbers $A = 1 + 4 + 16 + \dots = -1/3$ and
$B = 2A = -2/3$.

- `held_domains_odd`: in the orbits of both $A$ and $B$ the cell next to the column reads 1 at every odd step.
- `held_disagree`: if two halves agree below $k + 1$ and differ at $k + 1$, their images agree below $k$ and differ at
  $k$.
- `held_countdown`: if $u$ agrees with $A$ below $k$ and differs at $k$, the cell next to the column reads 1 at steps
  $0, \dots, k - 1$ and 0 at step $k$.
- `held_agree_stepB`: if $u$ agrees with $B$ below $m + 2$ and differs at $m + 2$, two steps later it agrees with $B$
  below $m$ and differs at $m$.

## Argument

1. **The domains.** `held` fixes $A$: $A_1 \oplus A_0 = 1 = A_0$, and for $j \ge 1$ one of $A_j, A_{j-1}$ is 1, so
   bit $j$ becomes $\lnot A_{j+1} = A_j$. On $B$ the same computation leaves every bit $j \ge 1$ in place and sets bit
   0 to $B_1 \oplus B_0 = 1$; one more step restores bit 0 to $1 \oplus 1 = 0$. So $B$ has period 2, with bit 0 equal
   to 1 at the odd steps (`held_domainA`, `held_held_domainB`).
2. **Disagreement moves inward** (`held_disagree`). Bit $j$ of the image reads bits $j - 1$, $j$ and $j + 1$, so
   below $k$ the images agree. At $k$ each image is its bit $k + 1$, which differs between the two, XOR the same
   function of bits $k$ and $k - 1$.
3. **The countdown** (`held_countdown`). Apply step 2 with the fixed point $A$ as the second half: after $s$ steps,
   $u$ agrees with $A$ below $k - s$ and differs at $k - s$. For $s < k$ bit 0 agrees with $A_0 = 1$; at $s = k$ it
   differs.
4. **Domain B** (`held_agree_stepB`). Apply step 2 twice with the 2-cycle $B$.

Read $u$ as a 2-adic integer $U$. Agreeing with $-1/3$ on exactly the $k$ lowest bits means $3U + 1$ is divisible by
$2^k$ and not by $2^{k+1}$, so $k$ is the 2-adic valuation of $3U + 1$. The spot check `held_countdown_spot` takes
$U = 85$: $3 \cdot 85 + 1 = 256 = 2^8$, and the orbit is odd at steps 0 to 7 and even at step 8.

## What this says about period two

A finite half keeps the condition at an odd step only by matching a domain near the column, and every stretch of
domain erodes from the far side toward the column, one bit per step for $A$ and two bits per two steps for $B$. To
survive forever, the half must keep regrowing such stretches from the chaotic region behind them. Proving that it
cannot is the open problem; computation finds that it never does for small halves
([the left-half finding](../../findings/period-two/left-half-alone.md)).

## Relation to the kit

The kit's
[`Rule30ZeroBoundaryStripe`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30ZeroBoundaryStripe.lean)
proves that the stripe $A$ is a fixed point of the zero-boundary dynamics and that the first deviation from it moves
one depth toward the wall per step. Those facts are proved here independently; the domain $B$, the valuation reading
and the two-step erosion of $B$ are additions.
