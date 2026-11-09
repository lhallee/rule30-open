---
title: Every integer below 2^52 fails the period-two condition, near step 2M
category: period-two
problems: [1]
status: computed
formalization: partial
evidence: [computations/held_map.py]
---

# Every integer below 2^52 fails the period-two condition, near step 2M

[Period two reduces](../../Rule30Open/PeriodTwo/HeldColumn.md) to the map $H(U) = (U \gg 1) \oplus \bigl(U \lor (U \ll
1)\bigr)$: an eventually alternating center column needs a positive integer $U$ with $H^t(U)$ odd at every odd $t$. No
integer with at most 52 bits has this property, and an integer with $M$ bits fails it no later than step $2M + 5$.

## Result

For each support $M$ (the integers with exactly $M$ bits) and each phase (checks at odd steps, or at even steps), the
latest first failure over all $2^{M-1}$ integers lies between $2M - 13$ and $2M + 5$ for odd checks and between $2M -
16$ and $2M + 8$ for even checks, at every $M$ from 1 to 52. At $M = 20$ it is step 37 for odd checks and step 30 for
even checks.

Alone, the left half lasts longer than with the right side's constraint ([the 120-cell
finding](alternating-within-120.md)), because a stretch of the alternating domain next to the column, a fixed point of
the held map, keeps the condition until the chaos from the left edge erodes it
([Domains.md](../../Rule30Open/PeriodTwo/Domains.md)). The right side forbids that domain.

## Why 2M

**The count at step M - 1 (proved on paper).** Bit 0 of $H^t(U)$ is bit $t$ of $U$ plus a function of the lower bits
([the shift model](shift-model.md)), so the checks at the odd steps below $M$ fix the odd bits of $U$ below its top bit.
For odd $M$ the top bit $M - 1$ is even and is fixed only by the support, the even bits below it are free, and exactly
$2^{(M-1)/2}$ of the integers with exactly $M$ bits keep the condition through step $M - 1$ (also checked against
stepping integers for every odd $M \le 11$).

**The halving (a heuristic).** From step $M$ on, $U$ has no bit left to fix: each check at an odd step $t \ge M$ asks
that a function of the free bits take the value the vacuum bit $t$ needs, one more equation in $(M - 1)/2$ unknowns. If
each such check halved the survivors, about $2^{(M-1)/2 - k}$ would remain after $k$ of them and none after $k \approx
M/2$, at step about $2M$. The counts follow this until the last few: of the integers with 23 bits, 2,048, 1,008, 444,
223, 118, 59, 33, 15, 9, 3 and 2 keep the condition through the steps 22, 24, ..., 42, against 2,048, 1,024, 512, ...,
2, and the last two fail at step 43. So the law "no later than about $2M$" is what independent checks would give, and
`Q01` asks that these equations have no common solution for any $M$; they are dense polynomials of full degree in the
free bits ([forced bits](../../negative-results/period-two/forced-bits-dense.md)), so no sparse certificate decides
them.

## Reproduce

[computations/held_map.py](../../computations/held_map.py) checks every integer of each support up to about 24 in NumPy
(support 22 in about 5 s), using that bit 0 of $H^t(U)$ depends only on bits $0, \dots, t$ of $U$:

```bash
python -m computations.held_map 22
python -m computations.held_map 23 --survivors   # the survivors at each step, against the halving (about 30 s)
```

The supports from 25 to 52 ran in a compiled search along the spacetime's diagonals that is not in this repository
(support 52 in about 1 s on 32 threads, with peaks of $2^{26}$ and $2^{25}$ branches), checked against an independent
bit-sliced search.

## Relation to the kit

The kit proves the same statement in Lean for every start of width at most 52, as its statement Q01
([`Rule30PeriodTwo`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30PeriodTwo.lean)).
The new information here is the location of the latest failure, which grows linearly with the width: every finite search
moves the bound, and none reaches every integer.
