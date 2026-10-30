---
title: The finite game excludes 261 of the 22,242 blocks of period 17 and 18
category: columns
problems: [1]
status: computed
formalization: partial
evidence: [computations/game.py, computations/bit_game.py, computations/wall_segments.py]
---

# The finite game excludes 261 of the 22,242 blocks of period 17 and 18

[The finite game](../../Rule30Open/Columns/FiniteGame.md), run on every primitive block of period 17 and 18 at widths
6, 10 and 14 in turn, excludes 261 of the 22,242 blocks as the eventual period of any column of any row with a leftmost
1: 119 of the 7,710 of period 17 and 142 of the 14,532 of period 18. The kit excludes 26 of them, all 26 that it
excludes at these periods, [WallSets](../../Rule30Open/Columns/WallSets.md) 80 more, and 155 are new. Lean checks the
80 by WallSets' check and 141 of the 155 by the game decided in the kernel
([BitBlocks17](../../Rule30Open/Columns/BitBlocks17.md), [BitBlocks18](../../Rule30Open/Columns/BitBlocks18.md)); the
other 14 need a game of 13 or 14 cells.

## Result

| Period | Blocks | Excluded | By the kit | By WallSets | New | New, in Lean |
|---:|---:|---:|---:|---:|---:|---:|
| 17 | 7,710 | 119 | 12 | 35 | 72 | 64 |
| 18 | 14,532 | 142 | 14 | 45 | 83 | 77 |

- **Widths.** Of the 261, the game excludes 187 at width 6, 53 at width 10 and 21 at width 14. At the least width the
  155 new blocks need 5 to 14 cells: 3 need 5, 80 need 6, 11 need 7, 22 need 8, 7 need 9, 11 need 10, 3 need 11, 4
  need 12, 8 need 13 and 6 need 14.
- **Runs.** Every excluded block has a run of at least six equal values; up to period 16 the least is five, for
  $000001011111011$ of period 15. The least here are $00000010110000011$, $00000010111101111$, $00000010111111011$,
  $000000101110000011$ and $000000110111111011$, each with six 0s in a row.
- **Nine 1s.** Up to period 16 WallSets and the game agree on every block with nine 1s in a row. At periods 17 and 18
  WallSets excludes 97 blocks, the game all of them, and the game excludes 11 more blocks with nine 1s in a row, 4 of
  period 17 and 7 of period 18, such as $00100101111111111$ and $000101111111111001$.
- **The bit check.** `criterion` in [computations/bit_game.py](../../computations/bit_game.py) decides each of the 238
  blocks that the kit's tables, long runs and padded words leave, at its least width, with at most 158 images, 3 rounds
  and closures of 140 steps.

## Against the kit

`kit_blocks` in [computations/game.py](../../computations/game.py) lists 26 blocks of period 17 and 18 that the pinned
kit excludes: 17 whose runs of 1s all last at least nine steps, 6 padded words ($0^q 1$, $0^r 11$, $0^q 10111$) and 3
of its white-padding certificate families, $0^{13} 1011$ and $0^{14} 1011$ of family I ($r \ge 13$) and $0^{14} 1101$ of
family B ($r \ge 14$), which reach these periods for the first time. Its other families, Theorem B′ ($1^r u$ with
$r \ge 18$), the white-padding families A and C to H, the tails of at most six cells after at least 69 white cells and
its suffix families, start at period 19 or later. The game excludes all 26.

## The 14 left out of Lean

Eight of period 17 and six of period 18 need 13 or 14 cells, such as $00000000000101101$ and $0^{15} 111$. The kernel
runs the bit check on them, but at width 14 one block takes 34 to 83 seconds and 7 to 9.5 GB, measured on
$0^{15} 111$ and $000010111111110111$; the module would add several minutes and too much memory to the build.

## Reproduce

```bash
python -m computations.game --min-period 17 --max-period 18 --widths 6,10,14 --workers 4
```

It takes about 17 minutes with four processes and prints the 261 blocks with the first width that excludes each.
`kit_blocks(18)`, `wall_segments.in_set_family` and `bit_game.criterion` give the other columns of the table.
