---
title: Rule 210 keeps the period-two condition
category: analogs
problems: [1]
status: proved
lean: Rule30Open.Analogs.Rule210
headline: [rule210_finite_half, orbit210_checkerboard]
kit: new
kit_modules: [Rule30Realization]
---

# Rule 210 keeps the period-two condition

Rule 210 agrees with Rule 30 at every cell that reads 0 and differs at every cell that reads 1. It shares the
features the period-two reduction uses: it is left-permutive, it moves a leftmost 1 one cell left per step, and an
alternating column fixes the cell left of it at each of its 1s. Yet under Rule 210 a finite nonzero half does keep the
analogous condition forever. So a proof that no finite half keeps the Rule 30 condition
([HeldColumn.md](../PeriodTwo/HeldColumn.md)) must use what Rule 30 does at a cell reading 1.

## Statement

Rule 210 is $x' = l \oplus (\lnot c \land r)$ for the left neighbor $l$, the cell $c$ and the right neighbor $r$. Let
the column read 0 at even steps and 1 at odd steps, and let the half left of it evolve by Rule 210.

- `orbit210_checkerboard`: if the half is 0 at every odd distance $j$ at step 0, then at step $n$ it is 0 at every
  $j$ with $j + n$ odd.
- `rule210_finite_half`: a single 1 next to the column, a finite nonzero half, reads 0 next to the column at every odd
  step, forever.

## Argument

1. **Where the rules differ.** At $c = 0$ both rules give $l \oplus r$. At $c = 1$ Rule 30 gives $\lnot l$ and
   Rule 210 gives $l$.
2. **The analogous condition.** Under Rule 210 the column's update at a 1 is $l \oplus 0 = l$, so a column reading 1
   then 0 has 0 left of it at the 1. That is the Rule 210 version of the period-two condition: 0 next to the column at
   every odd step, where Rule 30 demands 1.
3. **The checkerboard** (`orbit210_checkerboard`). A cell with both neighbors 0 becomes 0 under Rule 210, whatever it
   reads. Suppose at step $n$ the half is 0 wherever $j + n$ is odd. A cell with $j + n + 1$ odd has both neighbors at
   distances with $j \pm 1 + n$ odd, so they are 0, and it becomes 0. For the cell next to the column the right
   neighbor is the column, which reads 0 at the even steps $n$ where this case arises.
4. **The finite half** (`rule210_finite_half`). The single 1 at distance 0 is on the even color. At every odd step $n$
   the cell next to the column has $0 + n$ odd, so it is 0: the condition holds forever.

Under Rule 30 the argument breaks at step 3: a cell reading 1 between two 0s stays 1, since
$0 \oplus (1 \lor 0) = 1$, so 1s cross colors.

## In Lean

`drive210` is one step of the half beside the column and `orbit210` its orbit. `orbit210_single` checks the first five
steps from the single 1 by `decide`.

## Relation to the kit

The kit's
[`Rule30Realization`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Realization.lean)
shows a related barrier from the single cell: under Rules 90, 150 and 210 its center column is eventually constant.
Both results say that the properties Rule 30 shares with these rules cannot prove Problem 1 alone.
