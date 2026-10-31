---
title: Natural traps for 60 blocks of periods 10 to 14 whose wall traps fail the test of reach
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.NaturalTrapsWalls
headline: [naturalTrapsWalls_check, naturalTrapsWalls_blocks, naturalWalls_absorption_excludes, natw00101101111_excludes, natw00101101111_0_not_absorption]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/lock_chain.py]
---

# Natural traps for 60 blocks of periods 10 to 14 whose wall traps fail the test of reach

The walls of [TenTraps](TenTraps.md), [ElevenTraps](ElevenTraps.md), [TwelveTraps](TwelveTraps.md),
[ThirteenTraps](ThirteenTraps.md) and [FourteenTraps](FourteenTraps.md), carried leftward along the chains of their
backgrounds, give traps to many blocks, and for those blocks [the natural scan](../../findings/columns/natural-traps.md)
was not needed. But entry into many of the carried traps is false: in the game of 20 cells some node cannot reach them,
the test of [MissedTraps](MissedTraps.md) ([what failed](../../negative-results/columns/missed-traps.md)). The natural
scans of periods 10 to 14 give closed sets for 66 of the blocks of these modules left with no trap that passes. This
module checks those that survive two tests, for 60 blocks: 9 of period 10, 13 of period 11, 14 of period 12, 8 of
period 13 and 16 of period 14. For 54 one trap passes; for 6 the sampled halves split between two traps, and only entry
into one of the two can hold.

## Statement

1. **The traps** (`naturalTrapsWalls`, `naturalTrapsWalls_check`). A list of 54 labelled traps `WTrap` with labels
   modulo the period, 52 of 16 cells, one of 17 ($00111011011$) and one of 18 ($00001101101$), with 110 to 11,099
   states, each passing the check of [WordTraps](WordTraps.md) in its own declaration (`natw<block>_check`), eight of
   more than 3,000 states in parts of 1,024.
2. **The blocks** (`naturalTrapsWalls_blocks`): 8 blocks of period 10, 12 of period 11, 12 of period 12, 7 of period 13
   and 15 of period 14, each a block of one of the five wall modules.
3. **The reduction** (`naturalWalls_absorption_excludes`). For each of them, if every finitely supported right half
   driven by the block enters its trap (`WTrap.Absorption`), the center column does not eventually repeat the block.
4. **Six blocks with two traps** (`natw<block>_excludes`), each trap passing the check:

   | block | first trap | second trap |
   |---|---|---|
   | $0001010111$ | 19 cells, 100 states | 20 cells, 100 states |
   | $00101101111$ | 16 cells, 1,402 states | 19 cells, 103 states |
   | $000000101101$ | 17 cells, 150 states | 26 cells, 116 states |
   | $000010011111$ | 16 cells, 150 states | 18 cells, 313 states, labels modulo 24 |
   | $0000001111111$ | 16 cells, 3,032 states | 25 cells, 718 states |
   | $00101101101101$ | 16 cells, 126 states | 32 cells, 126 states |

   If every such half enters one of the two (`WTrap.AbsorptionSome` of [TrapPairs](TrapPairs.md)), the center column
   does not eventually repeat the block.
5. **Entry into either alone is false** (`natw<block>_0_not_absorption`, `natw<block>_1_not_absorption`, for each
   pair but that of $0000001111111$). Each trap of a pair is a closed set apart from the other: no state of the wider,
   cut to the narrower width, is a state of the narrower with a label of the same phase. So a half inside either never
   enters the other. For $0000001111111$ the kernel's check of the separation, over 3,032 by 718 pairs of states, runs
   out of memory here, and the separation is computed (`halves_apart`).

## Argument

Each trap is the closure, under both values of the cell beyond, of the window of one driven half at step 12,000 at the
least width from 16 whose closure fixes column 1 at the white phases (`natural_tables` in
[computations/lock_chain.py](../../computations/lock_chain.py)): of the white half for 51 of the 54, of a random half of
64 cells for $00001111001$, $00111011011$ and $000100111101$, and for each pair, of the white half for one trap and of
a random half for the other. The kernel checks each, so the closure is not trusted, and [WordTraps](WordTraps.md)'s
`absorption_excludes` gives each reduction. For the pairs, `absorption_some_excludes` of [TrapPairs](TrapPairs.md)
gives the reduction to entry into one of the two, and `not_absorption` and `not_absorption_wide` of
[MissedTraps](MissedTraps.md) refute entry into each alone, with the other trap as the closed set apart from it.

## Which traps were kept

Of the closed sets the scans give, the module keeps those that pass two tests, both necessary for entry.

- **The test of reach at 20 cells.** Every node of the finite game of 20 cells, with the phase counted modulo the
  period, must be able to reach a window whose first cells form a state of the trap (`trap_reach`). In the game of 20
  cells the cells after a trap of 16 follow the rule and only cell 21 is free, so a trap can pass in the game of its own
  width and fail in a wider one; the nodes that cannot reach form a set that no move leaves, and a half that starts
  there never enters. The 54 kept traps pass at 18 and at 20 cells. The natural traps of 16 cells of five blocks fail
  at 20 cells, with 99.01% to 99.88% of the nodes able to reach: $0000101011001$, $0001001110111$, $0001011100111$,
  $0010111101101$, and $0001110010011$, whose natural trap is the trap of the wall of
  [ThirteenTraps](ThirteenTraps.md) itself. That of $00110111111$, of 23 cells, fails cut to 20 cells, with 1.15%.
  These six blocks are left with no trap that passes.
- **No half apart.** No half of the scan, closing windows of 16 to 64 cells, may be inside a closed set apart from the
  trap: such a half never enters (`halves_apart`). For each of the six pairs the halves of the scan split between its
  two traps, which are apart: for $0001010111$, 12 of the 31 halves are inside the trap of 19 cells and 19 inside that
  of 20; for $00101101111$, 6 and 25 inside those of 16 and 19 cells; for $000000101101$, 27 and 3 inside those of 17
  and 26; for $000010011111$, 3 and 28 inside those of 16 and 18; for $0000001111111$, 27 and 4 inside those of 16 and
  25; for $00101101101101$, 30 and 1 inside those of 16 and 32. The first traps of $000000101101$, $0000001111111$ and
  $00101101101101$ pass the test of reach at 20 cells, so only this test refutes them. For every kept single trap, no
  half of the scan is inside a trap apart from it.

For the six pairs each trap alone fails: at 20 cells, with 68.21% to 99.63% of the nodes able to reach, except the
three first traps that only the halves apart refute. But every node of the game of 20 cells can reach one of the two,
the wider traps cut to their first 20 cells, and the six blocks are reduced to entry into one of the two, as the four
blocks of [TrapPairs](TrapPairs.md) are.

## What it covers

Each trap reduces its block to entry. For 47 of the 54 blocks every one of the 31 halves of the scan is inside the trap
at step 12,000; for 5 more, 26 to 30 of them; for $00111011011$ and $00001111001$, 10 and 3. The 60 blocks count among
those reduced to entry into a trap that passes the test, in [the coverage table](../../findings/columns/coverage.md).
The test only grows stricter with the width: in the game of 22 cells the trap of $0010011110101$ and the pair of
$00101101111$ fail it, with 99.992% and 99.994% of the nodes able to reach, so entry into either is false too ([what
failed](../../negative-results/columns/missed-traps.md)); the other 53 traps and five pairs pass there. Passing the test
is necessary for entry, not sufficient: entry for every finite right half stays open, as for the kit's traps.

## Relation to the kit

The kit's traps are `t001` for $001$ and its ether-and-wall family for the words of period four; it has none for a
block of period 10 to 14, and none of these blocks is among those it excludes. Its `Absorption` for the period-four
words asks entry into one member of a family after its single certificates fail (`Rule30Ether.never_enters_S0001`
and the two after it); the six pairs here are the same move for two traps.

## Lean

`Rule30Open.Columns.NaturalTrapsWalls`: the traps `natw<block>` with their checks, `naturalTrapsWalls`,
`naturalTrapsWalls_check`, `naturalTrapsWalls_blocks` and `naturalWalls_absorption_excludes`; for the six pairs
`natw<block>_0`, `natw<block>_1`, the list `natw<block>` and `natw<block>_excludes`, and for five of them
`natw<block>_0_not_absorption` and `natw<block>_1_not_absorption`, with `WTrap.closedCheck_of_check`, which reads the
closure of a checked trap off its check. The tables come from `python -m computations.lock_chain --lean-wall-natural`;
the kernel checks the module in about 90 seconds.

## Reproduce

```bash
python -m computations.lock_chain --lean-wall-natural
```

```bash
python -m computations.lock_chain --halves-apart
```

The traps, rebuilt from the natural scans' starts, in a few seconds; the halves of the natural scans inside traps apart
from them, in about seven minutes. `test_wall_natural` checks each trap, its half, its block, and for the pairs that the
two traps are apart and that one of them can be reached from every node of the game of 18 cells.
