---
title: Traps for 57 of the 186 blocks of period 11, from walls of period eleven carried leftward
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ElevenTraps
headline: [elevenTraps_check, elevenTraps_blocks, eleven_absorption_excludes]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/lock_chain.py]
---

# Traps for 57 of the 186 blocks of period 11, from walls of period eleven carried leftward

[The natural scan](../../findings/columns/natural-traps.md) finds that the commonest traps at period 11, of 313, 103 and
138 states, are walls of 16 cells: the closures of the true windows of right halves driven by $00000011011$,
$00110100111$ and $00001101001$ at step 12,000, under both values of the cell beyond. Their chains become periodic in
the distance, with spatial periods 143, 275 and 143 from distances 23, 9 and 0, as the wall of period 10 does in
[TenTraps](TenTraps.md). This module carries the walls leftward up to 40 columns and checks the traps of the 57 blocks
of period 11 that they reach there and that the kit does not exclude.

## Statement

1. **The traps** (`elevenTraps`, `elevenTraps_check`). A list of 57 labelled traps `WTrap`, all passing the check of
   [WordTraps](WordTraps.md): for each block, the wall that reaches it first carried to the least distance $d \le 40$
   that holds it, a trap of $16 + d$ cells with the wall's number of states and labels modulo 11.
2. **The blocks** (`elevenTraps_blocks`): 57 distinct blocks of period 11, 33 by the first wall and 24 by the second;
   the third reaches no block the first two do not.
3. **The reduction** (`eleven_absorption_excludes`). For each of them, if every finitely supported right half driven by
   the block enters its trap (`WTrap.Absorption`), the center column does not eventually repeat the block.

## Argument

As in [TenTraps](TenTraps.md) and [NineTraps](NineTraps.md): each wall is a closed set of windows on which column 1 is
fixed at the white phases; if column $m$ repeats the block and column $m + 1$ reads the wall's values at its white
phases, each column to the left is a function of the two to its right, and putting the $d$ columns between
$m - d + 1$ and $m$ in front of every state gives a trap of $16 + d$ cells for the block of column $m - d$ (`carried`
in [computations/lock_chain.py](../../computations/lock_chain.py)). The kernel checks every trap, so the carrying is not
trusted, and [WordTraps](WordTraps.md)'s `absorption_excludes` gives each reduction.

## What it covers

Each trap reduces its block to entry. The walls themselves are entered fast: every right half with support in cells 1 to
8 enters the wall of $00000011011$ from every phase within 1,594 steps, and the white half within 664, which
[WallGaps](WallGaps.md) carries along the light cone; of the halves of at most four cells, 166 of the 176 pairs of a
half and a phase enter the wall of $00110100111$ within 20,000 steps. The traps carried farther are entered less: of the
57, small halves enter 7 from every one of the 176 pairs within 20,000 steps, 12 from some, and 38 from none
(`walls_entry`). Entry for every finite right half stays open, as for the kit's traps.

**The test of reach.** Cut to their first 20 cells, 27 of the 57 traps here, of 23 to 49 cells, fail the test of
[MissedTraps](MissedTraps.md): some node of the finite game of 20 cells cannot reach the trap's states so cut, so a
right half whose first 20 cells start there never enters, and entry into the trap is false ([what
failed](../../negative-results/columns/missed-traps.md)). For 27 of their blocks no trap of any module passes, so the
reduction is empty. The other 30 traps pass the test, which entry needs but does not imply.

## Relation to the kit

The kit's traps are `t001` for $001$ and its ether-and-wall family for the words of period four; it has none for a
block of period 11, and none of these blocks is among those it excludes.

## Lean

`Rule30Open.Columns.ElevenTraps`: the traps `el<wall>_<distance>`, `elevenTraps`, `elevenTraps_check`,
`elevenTraps_blocks` and `eleven_absorption_excludes`. The tables come from
`python -m computations.lock_chain --lean-walls 11`.
