---
title: The word 0001 comes down to the period-two map, and the ether is its domain
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.EtherDomain
headline: [center_period_four_0001_integer, period_four_0001_held, held_etherLeft, ether_fits, ether_countdown, domainB_repeats]
kit: refines
kit_modules: [Rule30PeriodFourSkeleton, Rule30Ether]
evidence: [computations/held_map.py]
---

# The word 0001 comes down to the period-two map, and the ether is its domain

Least period 4 of Prize Problem 1 has three words, $0001$, $0011$ and $0111$. For $0001$ the question comes down to the
same integer map as period 2, $H(U) = (U \gg 1) \oplus \bigl(U \lor (U \ll 1)\bigr)$, with a denser condition: if the
center column ended in $0001$ repeated, some positive integer $U$ would have $H^t(U)$ even at every $t \equiv 0, 2$
and odd at every $t \equiv 3 \pmod 4$, and $H^t(U)$, $H^{t+4}(U)$ never both odd at $t \equiv 1$. Nobody knows whether
such an integer exists. Where period 2 has the alternating stripes as its infinite solutions, this condition has the
ether: the stripe that meets the three fixed phases breaks the right half's check, and the ether, the 2-adic number
$-8/127$, keeps the condition forever.

## Statement

Write $c(t)$ for the center column, $u_j(t)$ for the cell $j + 1$ places left of it, and $E_\varphi$ for the kit's ether
read leftward from its second $0001$ column at phase $\varphi$: $E_\varphi(j)$ is column $(5 - j) \bmod 7$ of the table
$B_1 B_2 B_3 B_4 B_5\, c\, c$ (`etherLeft`). At phase 0 it reads $0001000$ repeated, the 2-adic $-8/127$.

- `period_four_0001_held`: if $c(t) = 1$ exactly when $(t - T) \bmod 4 = 3$, for all $t \ge T$, then from some later
  step the cells left of the center are the `held` orbit of a nonzero half that is 0 beyond some cell, and next to
  the column it reads 0 at the steps $4s$ and $4s + 2$, 1 at the steps $4s + 3$, and not 1 at both $4s + 1$ and
  $4s + 5$.
- `center_period_four_0001_integer`: the same for `Rule30Prize.center` as a positive integer $U$ and the map $H$.
- `held_etherLeft`, `ether_fits`: $\mathrm{held}(E_\varphi) = E_{\varphi + 1}$, and next to the column $E$ reads
  $0001$ at every period, so the infinite half $E_0$ meets the condition with every free bit 0.
- `ether_countdown`: a half that agrees with $E_\varphi$ exactly on its $k$ lowest bits reads what $E$ reads next to
  the column for exactly $k$ steps, and the opposite at step $k$. `ether_countdown_spot` checks it on $U = 1032$,
  with $127 \cdot 1032 + 8 = 2^{17}$.
- `domainB_repeats`: domain B of period 2 ($0101\dots$ read from the column) meets the three fixed phases, but it reads
  1 at every odd step, so its free bits are 1 at every period.

## Argument

1. **No kicks.** By [the kicked form](KickedForm.md) the cells left of any column follow `held`, except that the cell
   next to it is flipped when the column reads 1 at two consecutive steps (`left_kicked_zero`). The word $0001$ never
   does, so from $T$ on the left half follows `held` exactly. This is the kit's effective boundary
   ($c(t) \land c(t+1) = 0$ for $0001$, `Rule30PeriodFourSkeleton.effWord_0001`), read in the orbit of the single cell.
2. **The skeleton.** The kit proves, with a rank certificate and masked Jen, that an eventual $0001$ forces column 1
   white at phase 0 and black at phase 2, and column $-1$ white, equal to column 1, white and black at phases 0 to 3
   (`skeleton_0001_explicit`); and that column 1 at phase 1 is never black in two consecutive periods
   (`no11_0001`). Column $-1$ is the cell next to the column, bit 0 of the half.
3. **The start.** Take a step $S$ past both bounds, at phase 0, with $S \ge 1$. The half at $S$ is nonzero, since the
   single cell's leftmost 1 is at $-S$, and 0 beyond it (`left_edge`). Its `held` orbit is the left half from $S$ on,
   by step 1, and step 2 gives the three fixed phases and the check at phase 1.
4. **As an integer.** Bit $j$ of $H(U)$ is $u_{j+1} \oplus (u_j \lor u_{j-1})$, which is `held`
   ([HeldColumn.md](../PeriodTwo/HeldColumn.md), `heldNat_repeat`), and the cell next to the column is the parity.
5. **The ether is a 4-cycle of `held`** (`held_etherLeft`). The kit's ether is a Rule 30 orbit with spatial period 7
   and temporal period 4 (`Rule30Ether.ether_rule`). Read leftward from its second $c$ column, its cells beyond the
   first follow `held` exactly. The first does too, because that $c$ column is black only at phase 3, where the
   column left of it, the other $c$, is black as well, so the OR in its update is the same with the column held at 0.
   Its cell next to the column is that other $c$ column, $0001$ (`etherLeft_zero`), which fits the condition with the
   free bit 0 (`ether_fits`).
6. **The countdown** (`ether_countdown`). The lowest bit at which two halves differ moves one bit toward the column at
   each step ([Domains.md](../PeriodTwo/Domains.md), `held_disagree`). Applied to a half and the 4-cycle $E$, it gives
   exactly $k$ steps of agreement next to the column. As a number, the bits $U$ shares with $E_0$ are counted by the
   2-adic valuation of $127U + 8$, since $E_0 = 8 + 8 \cdot 2^7 + 8 \cdot 2^{14} + \dots = -8/127$.
7. **The stripe fails the check** (`domainB_repeats`). Domain B is a 2-cycle of `held` reading 0 at even steps and 1
   at odd ones, so it meets phases 0, 2 and 3; but phase 1 is odd too, so its free bit is 1 at every period.

So the right half's check removes the stripe, but not the ether: at least one infinite half keeps the condition with
the check, and a proof must use that the half is finite, as for period 2.

## Computation

[computations/held_map.py](../../computations/held_map.py) searches the condition over every integer with exactly
$M$ bits in each of the four phases, using that bit 0 of $H^t(U)$ depends only on bits $0, \dots, t$ of $U$. The latest
first failure lies between step $M$ and step $M + 9$ for every $M$ from 1 to 24, for example 29 at $M = 24$; with the
right half's check it is never more than 2 steps earlier. Period 2's condition, which checks only every other step,
lasts to about $2M$ ([the left-half finding](../../findings/period-two/left-half-alone.md)).

```bash
python -m computations.held_map 24 --word 0001
```

This takes about 2 minutes. The same dependence makes the search a tree: bit 0 of $H^t(U)$ is bit $t$ of $U$ XOR a
function of the lower bits, so the integers below $2^M$ that keep the condition through step $M - 1$ are as many as
the readings it allows, $F_{k + 2}$ for $M = 4k$ with the check ($F$ the Fibonacci numbers). Followed along that tree,
at phase 0 with the check (the statement above), every positive integer below $2^{140}$ fails, the latest at step 166;
the margin past $M$ is 6 at $M = 32$, 10 at 64, 15 at 100 and 26 at 140
([the C3 finding](../../findings/columns/left-half-c3.md) has the method and the kit's three statements).

```bash
python -m computations.held_map 140 --tree check
```

This takes about 8 minutes, and 4 s up to $M = 100$.

## In Lean

`period_four_0001_held` combines `left_kicked_zero` and `left_kicked_succ` with the kit's skeleton, as
`period_two_held` does with `left_of_alternating`; the start $S$ is $T + 4(T_1 + T_2 + 1)$ for the skeleton's bound
$T_1$ and the check's bound $T_2$. `held_etherLeft_small` checks the ether's `held` step on 8 cells and 4 phases by
`decide`; `etherLeft_congr` reduces every cell and phase to it.

## Relation to the kit

The kit reduces least period 4 to the open statements `C3 w` about the left half driven by the effective boundary
([`Rule30PeriodFourSkeleton`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/7d665044b904117af9e82328aeb90a30692b2b85/lean/Ruliology/CellularAutomata/Rule30PeriodFourSkeleton.lean),
`least_period_four_of_C3`), and to the open absorption of the right half into its ether-and-wall traps
([`Rule30Ether`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/7d665044b904117af9e82328aeb90a30692b2b85/lean/Ruliology/CellularAutomata/Rule30Ether.lean)).
This module restates `C3 0001`, with the kit's check on the free bit added, as a condition on the integer map of
period 2, and shows that the ether that the kit uses on the right half is also the infinite solution on the left. The
kit has the reduction and the ether; the integer form, the ether's left half as a `held` orbit, the countdown and the
stripe's failure are additions.
