---
title: Traps for 34 more blocks of periods 10 to 12, the closed sets that driven right halves settle into
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.NaturalTraps
headline: [naturalTraps_check, naturalTraps_blocks, natural_absorption_excludes]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/lock_chain.py]
---

# Traps for 34 more blocks of periods 10 to 12, the closed sets that driven right halves settle into

[The natural scan](../../findings/columns/natural-traps.md) drives the white right half and 30 random halves of 64
cells by every block of periods 10 to 12 and closes the window of each half whose column 1 locks under both values of
the cell beyond. It finds traps for 153 blocks. The walls of [TenTraps](TenTraps.md), [ElevenTraps](ElevenTraps.md)
and [TwelveTraps](TwelveTraps.md) carry traps to 100 of them, and the kit or the finite game excludes 18 more. This
module checks the traps of 34 of the other 35, and [NaturalTrapsLarge](NaturalTrapsLarge.md) the 35th, in parts.

## Statement

1. **The traps** (`naturalTraps`, `naturalTraps_check`). A list of 34 labelled traps `WTrap`, each passing the check of
   [WordTraps](WordTraps.md) (`nat<block>_check`), with 107 to 15,752 states. Twenty-nine have 16 cells and labels
   modulo the period, or twice the period for $00000110101$ and $01101111111$; the others are those of $0001010101$ (31
   cells, labels modulo 20), $0010010101$ (40 cells, modulo 30), $0011010101$ (26 cells, modulo 20), $00001111011$ (22
   cells, modulo 22) and $000101001001$ (44 cells, modulo 24).
2. **The blocks** (`naturalTraps_blocks`). Of period 10: $0001010101$, $0010010101$ and $0011010101$. Of period 11:
   $00000000101$, $00000010001$, $00000011101$, $00000110011$, $00000110101$, $00001111011$, $00010011101$,
   $00011111111$, $00110011111$, $00111111011$, $00111111101$, $01101111111$ and $01110111111$. Of period 12:
   $000000001011$, $000001001101$, $000001100011$, $000001101011$, $000001111011$, $000010010001$, $000010101001$,
   $000011011011$, $000011111111$, $000101001001$, $000101101011$, $001001101111$, $001011011111$, $001011111011$,
   $001110111101$, $001111101111$, $010101010111$ and $010111111011$.
3. **The reduction** (`natural_absorption_excludes`). For each of them, if every finitely supported right half driven
   by the block enters its trap (`WTrap.Absorption`), the center column does not eventually repeat the block.

## Argument

1. **The traps.** Each is the closure, under both values of the cell beyond, of the window of one driven half at step
   12,000 (`natural_tables` in [computations/lock_chain.py](../../computations/lock_chain.py)): of the white half, or
   for $0001010101$, $0010010101$, $0011010101$, $00001111011$ and $000101001001$ of a random half, at the least width
   from 16 to 64 whose closure fixes column 1 at the white phases. For each block every half of the scan that settles
   into a trap settles into this one, up to a shift of its labels by a multiple of the period. The kernel checks each
   trap, so the closure is not trusted.
2. **The reduction** is [WordTraps](WordTraps.md)'s `absorption_excludes` for each member of the list.

## What it covers

Each trap reduces its block to entry, as the kit's `t001` does for $001$. For 29 of the blocks every one of the 31
halves of the scan is inside the trap at step 12,000; for $0001010101$, $0010010101$, $0011010101$, $00001111011$ and
$000101001001$, one, five, two, one and one of them. Small halves enter the traps of 16 cells fast: every right half
with support in cells 1 to 4, driven from every phase, enters each of the 29 within 8,622 steps, and for 26 of them
within 2,500 (`extra_entry`). The five wider traps are entered less: 7 to 52 of the 160 to 192 pairs of such a half
and a phase within 20,000 steps. With a fair coin in column 17 in place of the cells beyond, every window enters each
trap of 16 cells, the chance of staying out falling by a factor of 0.952 to 0.9993 per step ([natural
traps](../../findings/columns/natural-traps.md)). Entry for every finite right half stays open, as for the kit's
traps.

**The test of reach.** In the game of 20 cells every trap here passes the test of [MissedTraps](MissedTraps.md): every
node can reach a window whose first cells form a state of the trap, cut to 20 cells when the trap is wider ([what
failed](../../negative-results/columns/missed-traps.md)). Entry needs this but is not implied by it.

## The 35th block

The 35th block, $00010001011$ of period 11, has a natural trap of 61,857 windows of 30 cells with labels modulo 22,
whose packed numbers have about two million bits. [NaturalTrapsLarge](NaturalTrapsLarge.md) writes them in pieces and
checks the trap in parts of 1,024 states. Every right half with support in cells 1 to 4, from each of the 11 phases,
enters it within 12,584 steps.

## Relation to the kit

The kit's traps are `t001` for $001$ and its ether-and-wall family for the words of period four; it has none for a
block of period 10, 11 or 12, and none of these blocks is among those it excludes. None lies in the chain of a wall of
[TenTraps](TenTraps.md), [ElevenTraps](ElevenTraps.md) or [TwelveTraps](TwelveTraps.md), at any distance
(`wall_chains`), so carrying a wall does not give these traps.

## Lean

`Rule30Open.Columns.NaturalTraps`: the traps `nat<block>` with their checks `nat<block>_check`, `naturalTraps`,
`naturalTraps_check`, `naturalTraps_blocks` and `natural_absorption_excludes`. The tables come from
`python -m computations.lock_chain --lean-extra`.

## Reproduce

```bash
python -m computations.lock_chain --extra-entry --cells 4 --steps 20000
```

It prints, for each trap here and in [NaturalTrapsLarge](NaturalTrapsLarge.md), how many pairs of a half and a phase
enter within the steps, with the median and the latest entry, in about four minutes.
