---
title: Every integer below 2^52 fails the period-two condition, near step 2M
category: period-two
problems: [1]
status: computed
formalization: partial
evidence: [computations/held_map.py]
---

# Every integer below 2^52 fails the period-two condition, near step 2M

[Period two reduces](../../Rule30Open/PeriodTwo/HeldColumn.md) to the map
$H(U) = (U \gg 1) \oplus \bigl(U \lor (U \ll 1)\bigr)$: an eventually alternating center column needs a positive
integer $U$ with $H^t(U)$ odd at every odd $t$. No integer with at most 52 bits has this property, and an integer with
$M$ bits fails it no later than step $2M + 5$.

## Result

For each support $M$ (the integers with exactly $M$ bits) and each phase (checks at odd steps, or at even steps), the
latest first failure over all $2^{M-1}$ integers lies between $2M - 13$ and $2M + 5$ for odd checks and between
$2M - 16$ and $2M + 8$ for even checks, at every $M$ from 1 to 52. At $M = 20$ it is step 37 for odd checks and step 30
for even checks.

Alone, the left half lasts longer than with the right side's constraint
([the 120-cell finding](alternating-within-120.md)), because a stretch of the alternating domain next to the column, a
fixed point of the held map, keeps the condition until the chaos from the left edge erodes it
([Domains.md](../../Rule30Open/PeriodTwo/Domains.md)). The right side forbids that domain.

## Reproduce

[computations/held_map.py](../../computations/held_map.py) checks every integer of each support up to about 24 in
NumPy (support 22 in about 5 s), using that bit 0 of $H^t(U)$ depends only on bits $0, \dots, t$ of $U$:

```bash
python -m computations.held_map 22
```

The supports from 25 to 52 ran in a compiled search along the spacetime's diagonals that is not in this repository
(support 52 in about 1 s on 32 threads, with peaks of $2^{26}$ and $2^{25}$ branches), checked against an independent
bit-sliced search.

## Relation to the kit

The kit proves the same statement in Lean for every start of width at most 52, as its statement Q01
([`Rule30PeriodTwo`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/7d665044b904117af9e82328aeb90a30692b2b85/lean/Ruliology/CellularAutomata/Rule30PeriodTwo.lean)).
The new information here is the location of the latest failure, which grows linearly with the width: every finite
search moves the bound, and none reaches every integer.
