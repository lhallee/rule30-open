---
title: Period two reduces to an integer map
category: period-two
problems: [1]
status: proved
lean: Rule30Open.PeriodTwo.HeldColumn
headline: [period_two_held, period_two_integer, center_period_two_integer, heldNat_testBit]
kit: independent
kit_modules: [Rule30PeriodTwo]
---

# Period two reduces to an integer map

Period 2 is the first open case of Prize Problem 1: could the center column end in $0101\dots$? This module turns the
question into one about a single map on the positive integers,

$$H(U) = (U \gg 1) \oplus \bigl(U \lor (U \ll 1)\bigr),$$

with bitwise operations. If the center column alternated from some time on, some positive integer $U$ would have
$H^{2s+1}(U)$ odd for every $s \ge 0$. Nobody knows whether such an integer exists.

## Statement

- `period_two_held`: if column $k$ of the orbit of a row with a leftmost 1 alternates from time $T$ on, then from some
  later time the cells left of it are the orbit under `held` of a nonzero half that is 0 beyond some cell, and the
  cell next to the column reads 1 at every odd step of that orbit.
- `heldNat_testBit`: on the number whose bit $j$ is the cell $j + 1$ places left of the column, `held` is $H$.
- `period_two_integer`: under the same hypothesis there is $U > 0$ with $H^{2s+1}(U)$ odd for every $s$.
- `center_period_two_integer`: the same for `Rule30Prize.center`.

## Argument

1. **No kicks.** By [the kicked form](../Columns/KickedForm.md), the half left of the column follows `held` except for a
   flip when the column reads 1 at two consecutive steps. An alternating column never does, so from time $T$ on the
   half follows `held` exactly. Directly: left of a 1 that is followed by a 0 the cell is 1 (`left_of_alternating`),
   so at every 1 of the column the OR in the next update of that cell is 1 already, as if the column were 0.
2. **The condition.** At each 1 of the column the same fact says the cell next to it is 1. Start the orbit at a time
   when the column reads 0; the column then reads 1 at the odd steps, so the cell next to it reads 1 at every odd step
   of the orbit.
3. **The half is finite and nonzero.** It is 0 beyond the leftmost 1 of the row ([Evolve.md](../Foundations/Evolve.md),
   `left_edge`). It is not zero, because `held` fixes the zero half, whose cell next to the column is 0 at every step.
4. **As an integer.** Read the half as $U = \sum_j u_j 2^j$. Bit $j$ of $U \gg 1$ is $u_{j+1}$ and bit $j$ of
   $U \ll 1$ is $u_{j-1}$ (0 for $j = 0$), so bit $j$ of $H(U)$ is $u_{j+1} \oplus (u_j \lor u_{j-1})$, which is
   `held`. The cell next to the column is bit 0, the parity of $U$.

The single cell's center column, the official one, is the case $k = 0$ of a row with its leftmost 1 at 0.

## In Lean

`held` and `heldOrbit` are the map on halves and its orbit, `heldNat` is $H$, and `natOf u N` reads the first $N$ cells
of a half as a number. `heldNat_repeat` follows the orbit bit by bit. `heldNat_orbit_one` is a spot check: the orbit
of 1 begins $1, 3, 6, 13, 25, 55, 100, 222$, odd at steps 1, 3 and 5 and even at step 7.

## Relation to the kit

The kit's
[`Rule30PeriodTwo`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30PeriodTwo.lean)
reaches the same question for the single cell, as its statement Q01 on the zero-driven left half, and proves it for
every start of width at most 52. This reduction is independent and holds at every column of every row with a leftmost
1. What is known about the map is in [Domains.md](Domains.md) and in
[the period-two findings](../../findings/period-two/left-half-alone.md).
