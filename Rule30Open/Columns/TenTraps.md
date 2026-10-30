---
title: Traps for 25 blocks of period 10, from one background of period ten whose edge driven right halves enter
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.TenTraps
headline: [tenTraps_check, tenTraps_blocks, ten_absorption_excludes]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/lock_chain.py]
---

# Traps for 25 blocks of period 10, from one background of period ten whose edge driven right halves enter

The right half that a column repeating $0000010001$ drives locks column 1 inside a trap of 16 cells: the closure of its
true window under both values of the cell beyond is a set of 100 states, with the phase counted modulo 10, that the
rule never leaves and on which the cell beside the column is fixed at the white phases (`ten0`). Every right half with
support in cells 1 to 8 enters it, from every phase, within 3,042 steps. Carried leftward by its chain, as the wall of
period 9 is in [NineTraps](NineTraps.md), it gives a trap of 100 states to each block of period 10 in the chain. This
module checks the traps of the 25 blocks there that the kit does not exclude.

## Statement

1. **The traps** (`tenTraps`, `tenTraps_check`). A list of 25 labelled traps `WTrap`, all passing the check of
   [WordTraps](WordTraps.md): for $d$ = 0 to 3, 5 to 17 and 23 to 30, a trap of $16 + d$ cells with 100 states and
   labels modulo 10.
2. **The blocks** (`tenTraps_blocks`). They are, by distance, $0000010001$, $0001001101$, $0011010111$, $0001010111$,
   $0010101111$, $0001101111$, $0001110011$, $0001000111$, $0000010101$, $0001011111$, $0000100111$, $0011110101$,
   $0000111111$, $0000001011$, $0101111011$, $0001101011$, $0010110111$, $0000000001$, $0011111101$, $0000011101$,
   $0001111111$, $0000000101$, $0111011111$, $0000110011$ and $0011001111$: 25 of the 99 primitive blocks of period 10.
3. **The reduction** (`ten_absorption_excludes`). For each of them, if every finitely supported right half driven by
   the block enters its trap (`WTrap.Absorption`), the center column does not eventually repeat the block.

## Argument

1. **The wall.** `ten0` is the closure, at width 16 and with the phase modulo 10, of the window of the white right half
   driven by $0000010001$ at step 12,000. On it columns 1 to 11, 12 or 13 are fixed at each label, and only the last
   three to five cells vary with what arrives from the right.
2. **Carrying it leftward** (`carried` in [computations/lock_chain.py](../../computations/lock_chain.py)). If column
   $m$ repeats the block and column $m + 1$ reads the trap's values at the white phases, each column left of $m$ is a
   function of the two to its right; putting the $d$ columns between $m - d + 1$ and $m$ in front of every state gives a
   trap of $16 + d$ cells for the block of column $m - d$. The kernel checks all 25 at once (`tenTraps_check`), so the
   carrying is not trusted.
3. **One background.** The chain repeats with period 155 in the distance from its start: column $m - 155$ is column
   $m$, and every column is a block of period 10 or 2. So the wall is the right edge of a background of period 10 in
   time and 155 in space, as the kit's ether is one of period 4 with its wall. The background's columns hold 28 blocks
   of period 10, each first by distance 30; three of them, $0^8\,1\,1$, $0\,0\,1^8$ and $0\,1^9$, the kit excludes.
   At distances 20 to 28 lie the nine blocks of period 10 that have a locked window of 13 cells, the chain of
   $0\,1^9$ of [lock chains](../../findings/columns/lock-chains.md): those window locks are columns of the same
   background.
4. **The reduction** is [WordTraps](WordTraps.md)'s `absorption_excludes` for each member of the list.

## What it covers

Each trap reduces its block to entry, as the kit's `t001` does for $001$. For the wall itself entry is fast: of the
right halves with support in cells 1 to 8, driven from each of the 10 phases, all 2,560 enter `ten0` within 50,000
steps, a median of 238 steps in and the latest at 3,042, and the white right half enters from every phase by step 74.
The carried traps are entered less evenly: of the 640 pairs of a right half with support in cells 1 to 6 and a phase,
every one enters the traps at distances 0, 2, 5, 6, 7 and 9 within 20,000 steps, some enter those at distances 1, 3, 8,
10, 12, 13, 14 and 16, and none those at distances 11, 15, 17 and 23 to 30 (`ten_entry`); for the blocks at distances 23
to 30, [the natural scan](../../findings/columns/natural-traps.md) finds narrower traps, of 16 cells, that every sampled
half enters. In that scan every one of 31 driven halves ends inside a trap of 100 states for $0000010001$, $0011010111$,
$0010101111$, $0001101111$, $0001110011$ and $0000010101$, at the least width that holds a trap: this wall at distances
0, 2, 5, 6, 7 and 9. The finite game does not exclude $0000010001$ at any width up to 18: one component of 5,337 to
34,044 nodes at widths 12 to 16 lets a free cell beyond the window keep column 1 from locking. In Lean,
[TenGap](TenGap.md) checks the entries of the 2,560 small halves and carries them along the light cone: no finite
configuration whose cells 9 to 3,058 are white, or 1 to 90, has a center column that repeats $0000010001$. Entry for
every finite right half stays open, as for the kit's traps.

## Relation to the kit

The kit's traps are `t001` for $001$ and its ether-and-wall family for the words of period four; it has none for a block
of period 10. Its strip certificates exclude $0^8\,1\,1$, $0\,0\,1^8$ and $0\,1^9$, three blocks of this background,
which the list leaves out. [LockBlocks11](LockBlocks11.md) reduces five of the blocks with locked windows of 13 cells,
$0000000101$, $0000011101$, $0001111111$, $0011111101$ and $0111011111$, to a condition on column 14 instead.

## Lean

`Rule30Open.Columns.TenTraps`: the traps `ten0` to `ten30` (at the distances of `ten_distances`), `tenTraps`,
`tenTraps_check`, `tenTraps_blocks` and `ten_absorption_excludes`. The tables come from
`python -m computations.lock_chain --lean-ten`.
