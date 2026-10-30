---
title: No finite configuration white on cells 9 to 1,610 has a center repeating 00000011011, nor one white on cells 9 to 2,357 a center repeating 001011100111
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.WallGaps
headline: [eleven_gap, eleven_white, twelve_gap, twelve_white]
kit: new
kit_modules: [Rule30Coupled, Rule30FiniteConfigs, Rule30EtherThreeReach]
evidence: [computations/lock_chain.py]
---

# No finite configuration white on cells 9 to 1,610 has a center repeating 00000011011, nor one white on cells 9 to 2,357 a center repeating 001011100111

[TenGap](TenGap.md) carries the entries of the 2,560 right halves of at most eight cells into the wall of period 10
along the light cone. The same works for two of the walls that [ElevenTraps](ElevenTraps.md) and
[TwelveTraps](TwelveTraps.md) carry: every right half with support in cells 1 to 8 enters the wall of $00000011011$,
16 cells with 313 states and the phase modulo 11, within 1,594 steps, and the wall of $001011100111$, 16 cells with 119
states and the phase modulo 12, within 2,341 steps, from every phase.

## Statement

1. `eleven_gap`: no finite configuration whose cells 9 to 1,610 are white has a center column that repeats
   $00000011011$ from any phase, whatever its left half, its first eight cells and its cells beyond 1,610.
2. `eleven_white`: the same for every configuration white on cells 1 to 680.
3. `twelve_gap`, `twelve_white`: the same for $001011100111$, with cells 9 to 2,357, or cells 1 to 852.

## Argument

The argument of [TenGap](TenGap.md), with its `prefixRightW_of_entry` and `gapRightW_of_entries`, applied to the walls
`el0_0` of [ElevenTraps](ElevenTraps.md) and `tw0_0` of [TwelveTraps](TwelveTraps.md): for each phase the kernel runs
the 256 halves of at most eight cells to their entry steps and checks the state, its label and the bound, one
declaration per phase, and a configuration white on cells 9 to $B$ agrees on cells 1 to $B$ with the half of its first
eight cells. The white half enters the first wall by step 664 and the second by step 836, from every phase. The module
builds in under ten minutes with a peak near 2.4 GB.

## What it covers

With [TenGap](TenGap.md), one block of each of the periods 10, 11 and 12 is excluded for every finite configuration
whose right half has at most eight cells, or is white on its cells from 9 to a bound of 1,610 to 3,058, whatever lies
beyond. The third wall of [TwelveTraps](TwelveTraps.md), $000110110011$, takes every half of at most eight cells too,
within 2,810 steps (`gap_entries`), and could be added the same way. Entry for every finite right half stays open.

## Relation to the kit

As for [TenGap](TenGap.md): the driven right half and `evol_zero` are the kit's `Rule30Coupled`, the leftmost cell
its `Rule30FiniteConfigs`, and the packed rows `rowN` with `rowN_eq_drv` its `Rule30EtherThreeReach`. The kit has no
trap for a block of period 11 or 12.

## Lean

`Rule30Open.Columns.WallGaps`: `el0_0_check`, `tw0_0_check`, the entries `elGap0` to `elGap10` and `twGap0` to
`twGap11` with their checks `<prefix><φ>_ok` and `<prefix><φ>_len`, `eleven_gap`, `eleven_white`, `twelve_gap` and
`twelve_white`. The entries come from `python -m computations.lock_chain --lean-wall-gaps`.
