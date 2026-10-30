---
title: No finite configuration whose cells 9 to 3,058 are white has a center column that repeats 0000010001
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.TenGap
headline: [prefixRightW_of_entry, gapRightW_of_entries, ten_gap, ten_white]
kit: new
kit_modules: [Rule30Coupled, Rule30FiniteConfigs, Rule30EtherThreeReach]
evidence: [computations/lock_chain.py]
---

# No finite configuration whose cells 9 to 3,058 are white has a center column that repeats 0000010001

[TenTraps](TenTraps.md) reduces the block $0000010001$ of period 10 to entry into its wall `ten0`, a trap of 16 cells,
and every right half with support in cells 1 to 8 enters it from every phase. Here the kernel checks those entries, and
the light cone carries each to every half that agrees with it far enough: entry for a class of halves, as
[WhiteGap](WhiteGap.md) gives for the words of period four and [NineWhite](NineWhite.md) for the walls of period 9.

## Statement

1. `prefixRightW_of_entry`: if the run of a right half $r$, driven by the block of a checked trap from phase $\varphi$,
   has its first $K$ cells in a state of the trap at step $T$, with the label of its phase, then no finite
   configuration whose cells $1, \dots, T + K$ read the bits of $r$ has a center column that repeats the block from
   phase $\varphi$. For $r = 0$ this is NineWhite's `highRightW_of_entry`.
2. `gapRightW_of_entries`: if each of the $2^n$ halves of at most $n$ cells has such an entry with $T + K \le B$,
   checked by `gapEntriesOk`, then no finite configuration whose cells $n + 1, \dots, B$ are white has a center column
   that repeats the block from phase $\varphi$, whatever its first $n$ cells, its cells beyond $B$ and its left half.
3. `ten_gap`: for $0000010001$ from every phase, with $n = 8$ and $B = 3{,}058$.
4. `ten_white`: for $0000010001$ from every phase, every configuration white on cells 1 to 90.

## Argument

1. **The light cone.** Column $p$ at step $t$ of a driven right half depends only on the center and the initial cells
   $1, \dots, p + t$ (`drv_cone` of [WhiteGap](WhiteGap.md)), so at step $T$ the first $K$ cells of a half that agrees
   with $r$ on cells $1, \dots, T + K$ are those of the run of $r$.
2. **Entry excludes.** Once those cells are a state of the trap at its label they stay in the trap, whatever arrives
   from the right, and column 1 is fixed at the white times, which masked Jen forbids beside a column that repeats the
   block (`wtrap_column` of [WordTraps](WordTraps.md)). The block has a black letter, so the configuration is not
   white, and it has a leftmost black cell.
3. **The entries.** For each phase the kernel runs the 256 halves of at most eight cells (`runDrive`) to their entry
   steps, at most 3,042, and checks the state, its label and the bound (`gapEntriesOk`, one declaration per phase); a
   configuration white on cells 9 to 3,058 agrees on cells 1 to 3,058 with the half of its first eight cells
   (`pack_gap` of [WhiteGap](WhiteGap.md)). The white half enters by step 74 from phase 0 and by steps 11 to 73 from
   the others, so for it cells 1 to 90 suffice. The module builds in about five minutes with a peak near 2.5 GB.

## What it covers

Every finite configuration whose right half has at most eight cells, or is white from cell 9 to cell 3,058 whatever
lies beyond, or is white on cells 1 to 90, has a center column that does not repeat $0000010001$ from the start, in any
phase. For the words of period four the same kind of statement holds with six cells and bounds of 310 to 535
([WhiteGap](WhiteGap.md)). Entry for every finite right half, which would exclude the block, stays open.

## Relation to the kit

The driven right half and `evol_zero` are the kit's `Rule30Coupled`, the leftmost cell its `Rule30FiniteConfigs`, and
the packed rows `rowN` with `rowN_eq_drv` its `Rule30EtherThreeReach`. The kit has no trap for a block of period 10.

## Lean

`Rule30Open.Columns.TenGap`: `PrefixRightW`, `prefixRightW_of_entry`, `GapRightW`, `gapEntriesOk`,
`gapRightW_of_entries`, `highRightW_of_prefix`, `ten0_check`, the entries `tenGap0` to `tenGap9` with their checks
`tenGap<φ>_ok` and `tenGap<φ>_len`, `ten_gap` and `ten_white`. The entries come from
`python -m computations.lock_chain --lean-ten-gap`.
