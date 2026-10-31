---
title: A right half white on its first 1,317 cells enters the kit's trap for 001
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.HighThree
headline: [highRight3_of_entry, highRight_001]
kit: refines
kit_modules: [Rule30EtherThreeTrap, Rule30EtherThreeReach]
---

# A right half white on its first 1,317 cells enters the kit's trap for 001

The kit reduces least period three for the word $001$ to three statements, one of them `AbsorptionT t001`, false as
stated ([Traps001](Traps001.md)): every finite right half, driven by a center that repeats $001$, enters the kit's
trap `t001`, a set of 815 states of the 47
columns next to the center on which column 1 repeats with period 21 at the white times. The kit and
[EmptyRight](EmptyRight.md) show that the white right half enters, at step 1270, 1269 or 1268 by phase. Here that
entry is carried to every right half white on its first 1,317 cells, whatever lies beyond.

## Statement

1. **Entry along the light cone** (`highRight3_of_entry`). If the white right half, driven by $001$ from phase
   $\varphi$, is in `t001` at step $t_1 \ge 2$ with a label of the right phase, then no finite configuration whose cells
   $1, \dots, t_1 + 47$ are white has a center column that repeats $001$ from phase $\varphi$.
2. **The word 001** (`highRight_001`). No finite configuration whose cells $1, \dots, 1317$ are white has a center
   column that repeats $001$, in any phase, whatever its left half and its cells beyond 1,317.

## Argument

1. The trap reads columns $1, \dots, 47$ at step $t_1$, and column $p$ at step $t$ reads only the initial cells
   $1, \dots, p + t$ ([WhiteGap](WhiteGap.md), `drv_cone`). So a right half white on cells $1, \dots, t_1 + 47$ is in
   the same state of the trap at step $t_1$ as the white half. Entry then excludes the word by the kit's labelled trap
   and masked Jen for finite configurations (`no_finite_of_ptrap` of [EmptyRight](EmptyRight.md)).
2. The white half enters at step 1270, 1269 or 1268 at phase 0, 1 or 2 (the kit's `rowN_empty_eq` and
   `rowN_001_1`, `rowN_001_2` of EmptyRight), so 1,317 cells cover every phase; a longer white stretch is a stronger
   hypothesis (`highRight3_mono`).

## What it covers

The cells beyond 1,317 are arbitrary, so this covers right halves of any length, the analogue for $001$ of the kit's
`absorption_high` for $0001$ (white on cells 1 to 30). The kit's study found right halves that enter `t001` only after
about $2 \cdot 10^5$ steps, so the same argument from a nonempty small half would need a white stretch of that length;
small halves other than the white one are not covered.

## Lean

`Rule30Open.Columns.HighThree`: `HighRight3`, `highRight3_of_entry`, `highRight3_mono` and `highRight_001`.
