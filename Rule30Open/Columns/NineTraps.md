---
title: Traps for 21 of the 56 blocks of period 9, from a wall of period nine that driven right halves enter
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.NineTraps
headline: [nineTraps_check, nineTraps_blocks, nine_absorption_excludes]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/lock_chain.py]
---

# Traps for 21 of the 56 blocks of period 9, from a wall of period nine that driven right halves enter

No window of up to 18 cells locks for a block of period 9 ([window
locks](../../negative-results/columns/window-locks.md)). Wider ones do. The right half that a column repeating
$001011111$ drives can enter a trap of 43 cells, with the phase counted modulo 9: the closure of its true window under
both values of the cell beyond is a set of 233 states that the rule never leaves, on which the cell beside the column is
fixed at the white phases (`trap001011111`, in [WordTraps](WordTraps.md)). This module carries that trap leftward and
checks a trap for each of the 21 blocks of period 9 that the carrying reaches.

## Statement

1. **The traps** (`nineTraps`, `nineTraps_check`). A list of 21 labelled traps `WTrap`, all passing the check of
   [WordTraps](WordTraps.md): the trap of $001011111$ (43 cells), and for $d$ = 1 to 18, 20 and 21 a trap of $43 + d$
   cells, each with 233 states and labels modulo 9.
2. **The blocks** (`nineTraps_blocks`). They are for $001011111$, $000010011$, $010101111$, $000011111$, $000001011$,
   $010111011$, $001101011$, $001011011$, $001001101$, $001010101$, $011101111$, $000110011$, $001100111$, $000010001$,
   $000100101$, $001101111$, $000101011$, $001110111$, $000011001$, $000111011$ and $000001101$: 21 of the 56 primitive
   blocks of period 9.
3. **The reduction** (`nine_absorption_excludes`). For each of them, if every finitely supported right half driven by
   the block enters its trap (`WTrap.Absorption`, the kit's `AbsorptionT` for any period), the center column does not
   eventually repeat the block.

## Argument

1. **The wall.** `trap001011111` is the closure, at width 43 and with the phase modulo 9, of the window of a right
   half driven by $001011111$ at step 12,000, a half that enters it at step 6,084; the kernel checks it in
   [WordTraps](WordTraps.md). On it the first cell is fixed at the three white phases of the block, to white, black and
   white.
2. **Carrying it leftward.** If column $m$ repeats $001011111$ and column $m + 1$ reads those values at its white
   phases, column $m - 1$ repeats the block that the rule gives from the two, and so on leftward: column $m - j$ is
   column $m - j + 1$ at the next phase xor (column $m - j + 1$ or column $m - j + 2$). Put the $d$ columns between
   $m - d + 1$ and $m$ in front of every state of the wall, at its phase: the result is closed under the cell beyond and
   fixes the column left of column $m - d$, so it is a trap of $43 + d$ cells for the block of column $m - d$ (`carried`
   in [computations/lock_chain.py](../../computations/lock_chain.py), as in [lock
   chains](../../findings/columns/lock-chains.md)). The kernel checks all 21 at once (`nineTraps_check`), so the
   carrying is not trusted.
3. **The background.** From distance 10 the carried columns repeat with spatial period 135, every one a block of period
   9: 13 distinct blocks, from $000001101$ to $011101111$. It is a background of period 9 as the kit's ether is one of
   period 4, and the chain of $0\,1^8$, which has no lock, enters the same one from distance 8. The blocks at distances
   0 to 9 lie between the wall and the background. Beyond distance 21 the chain holds no block of period 9 that is not
   already in the list.
4. **The reduction** is [WordTraps](WordTraps.md)'s `absorption_excludes` for each member of the list.

## What it covers

Each trap reduces its block to entry, the route of the kit's `t001` for $001$, and unlike the traps of
[WordTraps](WordTraps.md) for other periods, this one is entered. Of the right halves with support in cells 1 to 8,
driven from each of the 9 phases, 247 of 2,304 enter `trap001011111` within 50,000 steps, a median of 17,403 steps in
and the latest at 49,425, so entries are still coming at the end; of 31 random halves of 64 cells, the traps at
distances 0 to 6 and 16 are each entered by one or two within 20,000 steps ([trap
entry](../../negative-results/columns/trap-entry.md)). The white right half does not enter within 100,000 steps from any
phase, and its column 1 does not repeat at the white times over steps 30,000 to 60,000, so entry for every finite half
has only partial support. Entry under $001$ into the kit's `t001` is faster: about 91% of the halves of up to ten cells
by step 50,000 ([the census for 001](../../findings/columns/t001-census.md)). The other 35 blocks of period 9 have no
trap from this wall; $001010011$ locks column 1 from one of 31 random starts, but the closure of its window at widths up
to 160 is not a trap. Entry for every finite right half stays open, as for the kit's traps.

## Relation to the kit

The kit's traps are `t001` for $001$ and its ether-and-wall family for the words of period four; the kit has none for
a block of period 9, and its table of strip certificates has no block of period 9. Its period-four picture has the
same shape: an ether, and a wall whose chain enters it, the lock of $0\,1^7$ carried eight columns ([lock
chains](../../findings/columns/lock-chains.md)).

## Lean

`Rule30Open.Columns.NineTraps`: the traps `nine1` to `nine21` (without `nine19`), `nineTraps`, `nineTraps_check`,
`nineTraps_blocks` and `nine_absorption_excludes`. The tables come from `python -m computations.lock_chain --lean`.
