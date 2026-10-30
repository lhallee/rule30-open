---
title: A trap of 61,857 states for the block 00010001011 of period 11, checked in parts
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.NaturalTrapsLarge
headline: [allRange_cover, nat00010001011_check, not_eventually_00010001011_of_trap]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/lock_chain.py]
---

# A trap of 61,857 states for the block 00010001011 of period 11, checked in parts

Driven by $00010001011$ for 12,000 steps, the white right half and each of the 30 random halves of 64 cells of
[the natural scan](../../findings/columns/natural-traps.md) end inside one closed set of windows of 30 cells, with the
phase counted modulo 22, on which column 1 is fixed at the white phases. It is the one trap of that scan, at periods 10
to 12, for a block that the kit and the finite game do not exclude and that no wall carries, that
[NaturalTraps](NaturalTraps.md) leaves out: packed as a `WTrap`, its tables are numbers of about two million bits, too
large for one kernel check. This module checks it in parts.

## Statement

1. **Parts cover the range** (`allRange_cover`). If a test of the states holds on each of the ranges $[c k, c k + c)$
   for $k < q$ (`allRangeT`) and on $[c q, c q + r)$, it holds below $c q + r$.
2. **The trap** (`nat00010001011_check`). `nat00010001011`, 61,857 windows of 30 cells with labels modulo 22, passes
   the check of [WordTraps](WordTraps.md).
3. **The reduction** (`not_eventually_00010001011_of_trap`). If every finitely supported right half driven by the
   block enters it (`WTrap.Absorption`), the center column does not eventually repeat $00010001011$.

## Argument

1. **The trap** is the closure, under both values of the cell beyond, of the window of the white half driven by the
   block at step 12,000, at the least width from 16 to 64 whose closure fixes column 1 at the white phases
   (`natural_tables` in [computations/lock_chain.py](../../computations/lock_chain.py)); every half of the scan settles
   into it, up to a shift of its labels by 11.
2. **Two costs, two remedies.** Lean reads a numeral one digit at a time, in time quadratic in its length: declaring the
   trap with its three numbers as literals of 93,104 to 595,852 digits took 4 minutes 48 seconds here. Written as sums
   of pieces of 65,536 bits, each shifted into place (`lean_number`), the declaration takes seconds, and the kernel
   evaluates each sum once per declaration. Checked whole, the kernel keeps every shifted number it computes, and the
   check needed more than 13 GB; in 61 parts of 1,024 states, each its own declaration and elaborated in turn, the
   tables of one part at a time are in memory.
3. **Gathering the parts.** `nat00010001011_parts` collects the 60 full parts by cases on the index, `allRange_cover`
   joins them with the last part of 417 states, and `allBelowT_of_forall` turns the result into the check's
   `allBelowT`. [WordTraps](WordTraps.md)'s `absorption_excludes` then gives the reduction.

## What it covers

The trap reduces $00010001011$ to entry. Every right half with support in cells 1 to 4, driven from each of the 11
phases, enters it within 12,584 steps, a median of 2,386 (`extra_entry`). Entry for every finite right half stays open,
as for the kit's traps. The two remedies apply to any trap: a larger one, as natural scans at longer periods may find,
needs only more parts.

## Relation to the kit

The kit has no trap for a block of period 11 and does not exclude this one. The block lies in the chain of no wall of
[ElevenTraps](ElevenTraps.md), and the finite game leaves it open at widths 6, 10 and 14.

## Lean

`Rule30Open.Columns.NaturalTrapsLarge`: `allRangeT`, `allRangeT_spec`, `allBelowT_of_forall`, `allRange_cover`, the
trap `nat00010001011` with its parts `nat00010001011_0` to `nat00010001011_60` and `nat00010001011_parts`,
`nat00010001011_check` and `not_eventually_00010001011_of_trap`. The trap and its parts come from
`python -m computations.lock_chain --lean-large`.
