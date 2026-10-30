---
title: Right halves white on their first 91,129 to 201,172 cells enter the walls of period 9
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.NineWhite
headline: [highRightW_of_entry, white_first_wall, white_first_wall_eight, white_second_wall, white_second_wall_zero]
kit: new
kit_modules: [Rule30EtherThreeReach, Rule30FiniteConfigs, Rule30Coupled]
evidence: [computations/lock_chain.py]
---

# Right halves white on their first 91,129 to 201,172 cells enter the walls of period 9

[NineTraps](NineTraps.md) reduces the blocks $001011111$ and $001010011$ of period 9 to entry: if every finitely
supported right half driven by the block enters its wall, a trap of 43 or 41 cells, the center column does not
eventually repeat the block. The white right half enters both walls from most phases, but only after $10^5$ steps or
more ([trap entry](../../negative-results/columns/trap-entry.md)). Here those entries are checked in Lean and carried,
by the light cone, to every right half white on enough cells, whatever lies beyond: the analogue for period 9 of the
kit's entry of the white half into `t001` and of [HighThree](HighThree.md).

## Statement

`HighRightW b B φ` says that no finite configuration whose cells $1, \dots, B$ are white has a center column that
repeats $b$ from phase $\varphi$, whatever its left half and its cells beyond $B$.

1. **Entry along the light cone** (`highRightW_of_entry`). If the white right half, driven by the block of a checked
   trap of [WordTraps](WordTraps.md) from phase $\varphi$, has its first $K$ cells equal to a state of the trap at step
   $T$, with the label of the right phase, then `HighRightW b (T + K) φ`.
2. **The first wall** (`white_first_wall`, `white_first_wall_eight`). `HighRightW` holds for $001011111$ with
   $B = 119{,}992$ from phases 0, 1 and 2, and with $B = 201{,}172$ from phase 8.
3. **The second wall** (`white_second_wall`, `white_second_wall_zero`). `HighRightW` holds for $001010011$ with
   $B = 91{,}129$ from phases 5, 6 and 7, and with $B = 169{,}141$ from phases 0, 1 and 2.

## Argument

1. **The run in parts.** The kit's `rowN` packs the driven right half into a number, bit $i$ for column $i + 1$. A run
   of $T$ steps is cut into parts of 16,384 steps. The first $L$ cells after $n$ steps depend only on the first $L + n$
   cells at the start (`rowN_mod`, from the light cone `drv_cone` of [WhiteGap](WhiteGap.md)), so the row at step $s$ is
   kept only on its first $T - s + K$ cells, the ones that can still reach the window at step $T$. Each part is one
   kernel computation (`runDrive`, which forces every step with a `Nat.ble 0` test as [WideWindow](WideWindow.md) does),
   from a literal row to the next, and `part` chains them (`rowN_add`). The white half enters the first wall at step
   119,947 from phase 2 and at step 201,129 from phase 8, and the second wall at step 91,086 from phase 7 and at step
   169,098 from phase 2, 38 parts in all.
2. **Earlier phases.** When the block reads white at phase $\varphi$, the white half is still white one step later, at
   phase $\varphi + 1$ (`rowN_delay`). So phases 0 and 1 of both blocks follow from phase 2, and phases 5 and 6 of
   $001010011$ from phase 7, one and two steps later.
3. **Entry excludes the block.** A finite configuration whose cells $1, \dots, T + K$ are white has, at step $T$, the
   same first $K$ cells right of the center as the white half, by the light cone, so its window is a state of the trap
   with the label of the right phase. It has a leftmost black cell, since the block has a black letter
   (`Rule30FiniteConfigs.exists_leftmost`), and [WordTraps](WordTraps.md)'s `wtrap_column` then makes two adjacent
   columns eventually periodic, which Jen's theorem rules out.

## What it covers

The cells beyond $B$ are arbitrary, so this covers right halves of any length that begin with a long white stretch.
It is a class of halves for which the hypothesis of [NineTraps](NineTraps.md)'s reduction holds, for 4 of the 9 phases
of $001011111$ and 6 of the 9 of $001010011$; the white half from the other phases does not enter within 1,000,000
steps, except from phases 3 and 4 of $001010011$, where it enters at step 659,740, a run left out here for its length.
It says nothing about the right half of the single cell's orbit, which is not white near the center.

## Relation to the kit

The kit proves that the white half enters `t001` at step 1,270 (`Rule30EtherThreeReach.t001_reached`), and
[HighThree](HighThree.md) carries that along the light cone; the kit has no trap and no entry for a block of period 9.
The packed rows `rowN` and `stepN` and their link to the driven half, `rowN_eq_drv`, are the kit's.

## Lean

`Rule30Open.Columns.NineWhite`. The literal rows and the parts come from `python -m computations.lock_chain
--lean-white`; the 38 kernel checks take about five minutes.
