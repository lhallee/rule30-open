---
title: No finite certificate settles period two
category: period-two
problems: [1]
status: negative
kind: dead-end
---

# No finite certificate settles period two

**Idea.** Period two reduces to one integer map ([HeldColumn.md](../../Rule30Open/PeriodTwo/HeldColumn.md)): show that no
positive integer $U$ has $H^t(U)$ odd at every odd $t$, with $H(U) = (U \gg 1) \oplus (U \lor (U \ll 1))$. Searches
kill every $U$ below $2^{52}$ ([the left-half finding](../../findings/period-two/left-half-alone.md)). A proof needs
something uniform: an invariant, a finite certificate, or a descent. Each kind tried fails.

**Attempts and why they fail.**

- **Bounded survival.** How long a half survives past its width looks random: for left halves constrained by the right
  side, of widths 70 to 110, the longest survival past the width was 6, 8, 14, 13 and 14 steps over 560 to 19,273
  starts, with a geometric histogram. The maximum grows with the number of starts, so no uniform bound of the kind a
  finite certificate gives can hold.
- **Linear parity checks.** Over 14 free cells the only GF(2) parity checks every constrained half satisfies are
  $y_1 = 1$ and $y_2 + y_3 = 1$; no window of 10 cells beyond them carries one.
- **Renormalization.** The kit's eight-column identity
  ([`Rule30SpacingRenormalization`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/7d665044b904117af9e82328aeb90a30692b2b85/lean/Ruliology/CellularAutomata/Rule30SpacingRenormalization.lean))
  turns a solution of width $W$ with a spaced gate into one of width $W - 8$ with the gate $G'(r) = G(r + 2) \oplus
  G(r + 4)$. It holds for the gates the right half actually produces, but $G'$ is never spaced again, so the descent
  stops after one step; and no second renormalization column exists up to depth 300 in either phase, or for any
  periodic word of period up to 8.
- **Merging survivors.** The last survivors at each width merge (two preimages into one within a double step; at width
  19, nine survivors into two configurations), which explains plateaus in the survivor counts, but the merged halves
  are chaotic next to the column, with no stripe-like regime before they die.
- **Forced rows.** Forcing the even-position cells white beyond the width leaves the odd positions at density 0.44 to
  0.55, random-looking; $2^{W/2}$ forced prefixes give about $1.78^{W/2}$ distinct tails, so merging is real but the
  tails still grow.

**What it means.** Survival near the column is decided by the chaotic region behind it, and every finite object tried
sees that region as random. The obstacle has the shape of a Collatz problem
([Domains.md](../../Rule30Open/PeriodTwo/Domains.md)): a stretch of a domain counts down and something must regrow it.

**Evidence.** Quoted from code that is not in this repository.
