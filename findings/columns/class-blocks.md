---
title: The game with cyclic classes at 16 cells closes ten blocks of period 13 to 16 that nothing else excludes
category: columns
problems: [1]
status: computed
formalization: partial
evidence: [computations/class_survey.py, computations/game.py, computations/class_blocks.py, computations/class_certificate.py]
---

# The game with cyclic classes at 16 cells closes ten blocks of period 13 to 16 that nothing else excludes

[The game with cyclic classes](class-game.md) was run at 16 cells on every primitive block of period 13 to 16 with both
colors, 8,053 blocks. It closes 186 of them; the plain game at 16 cells closes 176, and the class test closes ten more,
which neither the kit nor any other exclusion of this repository reaches. Lean proves all ten: no column of a row with a
leftmost 1, the center column of the single cell among them, eventually repeats any of them, in any rotation
([ClassBlocks](../../Rule30Open/Columns/ClassBlocks.md), [ClassBlocks13](../../Rule30Open/Columns/ClassBlocks13.md),
[ClassBlocks14](../../Rule30Open/Columns/ClassBlocks14.md), [ClassBlocks16](../../Rule30Open/Columns/ClassBlocks16.md),
[ClassBlocks16Wide](../../Rule30Open/Columns/ClassBlocks16Wide.md)). The plain game at 15 or 16 cells also closes three
blocks that its surveys at widths up to 14 miss and that nothing else excludes; those are not in Lean yet.

## Result

| Period | Blocks | Closed by the game at 16 cells | of those, not at 14 cells | Closed by the classes only | New |
|---:|---:|---:|---:|---:|---:|
| 13 | 630 | 21 | 0 | 2 | 2 |
| 14 | 1,161 | 32 | 1 | 1 | 1 |
| 15 | 2,182 | 53 | 0 | 1 | 1 |
| 16 | 4,080 | 70 | 2 | 6 | 6 |

"Closed by the classes only" counts the blocks where the class test passes and the plain game fails, both at 16 cells;
"New" counts those that neither [the kit](../../computations/game.py) (`game.kit_blocks`: its strip certificates,
padded words, long runs of 1s and padding and black-run families), nor [WallSets](../../Rule30Open/Columns/WallSets.md)
(`wall_segments.in_set_family`), nor [limit windows](limit-windows.md) of 14 cells (`limit_windows.is_good`) excludes.
Every block that the plain game closes, the class test closes too, and every block of these periods that the kit
excludes, the plain game at 16 cells closes.

The ten blocks, each with the least width at which the class test closes it:

| Block | Period | Least width | Components at 16 cells that can hold a play: nodes (cyclic period) |
|---|---:|---:|---|
| $0000001011011$ | 13 | 15 | 18,132 (13); 147 (39, mixed by phase); 17 (13) |
| $0001011111011$ | 13 | 15 | 10,565 (13); 2,246 (26, mixed by phase); 2,073 (13); 1,070 (13); 72 (13) |
| $00100101111111$ | 14 | 15 | 14,405 (14); 237 (28, mixed by phase); 82 (28, mixed by phase); 63 (28, mixed by phase); 48 (14) |
| $000000001101001$ | 15 | 11 | 6,267 (15); 33 (30, mixed by phase) |
| $0000000001101001$ | 16 | 9 | 7,755 (16); 200 (32, mixed by phase) |
| $0000000011011001$ | 16 | 14 | 1,937 (16); 1,493 (32, mixed by phase); 1,261 (16); 151 (16); 18 (16) |
| $0000001101111011$ | 16 | 14 | 8,882 (16); 61 (32, mixed by phase) |
| $0001101111111001$ | 16 | 16 | 5,338 (16); 1,889 (16); 72 (32); 67 (32, mixed by phase); 64 (32, mixed by phase); 23 (16) |
| $0011110011111111$ | 16 | 13 | 21,222 (16); 83 (32, mixed by phase) |
| $0110110111111111$ | 16 | 16 | 12,916 (16); 198 (64, mixed by phase); 140 (32, mixed by phase); 19 (16) |

"Mixed by phase" marks a component in which the column left of the repeating one takes both values at one phase, which
is where the plain game fails. Each such component has a cyclic period of two, three or four periods of the block, and
on each of its cyclic classes the left column has one value, so a play that stays in it gives the left column a period
and [the adjacent-column theorem](../../Rule30Open/Columns/AdjacentColumns.md) excludes the block. In every case the
component of cyclic period equal to the block's period is the largest, where the plain game's test already holds, as
for $000000001011$ at period 12 ([the class game](class-game.md)).

The three blocks the plain game closes at 15 or 16 cells and not at 14 are $00110011111111$ (16 cells),
$0000000000111011$ and $0000101111111001$ (15 cells each). They are not in [the game blocks up to period
16](game-blocks.md), which ran the game at widths 6, 10 and 14, and the kit, WallSets and limit windows do not exclude
them. [NaturalTrapsWalls](../../Rule30Open/Columns/NaturalTrapsWalls.md) and
[FourteenTraps](../../Rule30Open/Columns/FourteenTraps.md) hold traps for $00110011111111$, which hold once the column
enters them.

At 17 cells the same survey of the 8,053 blocks finds three more blocks that the class test closes and nothing else
excludes, $00001011111011$ (period 14), $000000000111011$ (15) and $0011001111111111$ (16), each first at 17 cells.
Their components mixed by phase have cyclic periods $5P$ and $6P$ (277 and 299 nodes), $3P$ (84 nodes), and $2P$ and
$4P$ (105 and 338 nodes). The plain game at 17 cells closes one more block, $000000001101001$,
which the class test closes from 11 cells on; it closes no block that the class test leaves open, and no block closed
at 16 cells opens at 17. These three are not in Lean; [NaturalTrapsLong](../../Rule30Open/Columns/NaturalTrapsLong.md)
and [CensusTraps15](../../Rule30Open/Columns/CensusTraps15.md) hold traps for the first two, which hold once the column
enters them.

## Checks

- **The components twice.** `class_survey.classify` finds the components and the cyclic classes in one pass (one search
  for the components, one breadth-first search from a node joined to a root of each); for each of the ten blocks
  `game.component_periods`, which builds the graph with `game.game_graph` and searches each component on its own, gives
  the same components at 16 cells and at the least width, and at one cell fewer a component mixed in a class.
  `tests/test_class_survey.py` compares the two on every block of periods 3, 5, 6, 7 and 8 and on random blocks of
  period 9 to 13, at widths 6 to 10, and checks that both tests only gain blocks as the width grows.
- **The plain game.** `game.bad_pairs` is positive for each of the ten at widths 6, 10, 14, 15 and 16, so no game
  module reaches them; a pass at some width implies a pass at every larger one, so the game closes none of them at any
  width up to 16.
- **The repository.** No Lean module or finding names any of the ten as excluded; four have traps that hold once the
  column enters them, $0000001011011$ ([NaturalTrapsLongLarge](../../Rule30Open/Columns/NaturalTrapsLongLarge.md),
  [CensusTraps13](../../Rule30Open/Columns/CensusTraps13.md)),
  $0001011111011$ ([NaturalTrapsLong](../../Rule30Open/Columns/NaturalTrapsLong.md)), $00100101111111$
  ([CensusTrapsLarge](../../Rule30Open/Columns/CensusTrapsLarge.md)) and $000000001101001$
  ([CensusTrapsLarge15](../../Rule30Open/Columns/CensusTrapsLarge15.md)).
- **The certificates.** For each block `class_blocks` builds the certificate of
  [ClassGame](../../Rule30Open/Columns/ClassGame.md) at the least width and `class_certificate.check` re-runs its
  conditions node by node in plain Python, 4,916 to 147,940 nodes for the widths and 551 to 40,564 for the classes.

## Lean

The five ClassBlocks modules check each block's certificate in the kernel, one `decide +kernel` per width and phase and
one per phase of the classes, and apply ClassGame's general soundness `class_column`, so each gives
`column_not_<b>`, `center_not_<b>` and `not_eventually_<b>`. That the ten are all the class test adds at 16 cells, and
the counts above, rest on the computation. The three blocks the plain game closes at 15 or 16 cells are not in
Lean yet; the same certificates would prove them, since the game's test is the class test's case $d = P$.

## Reproduce

```bash
python -m computations.class_survey --periods 13 16 --width 16 --workers 2   # the tables, about 18 minutes
python -m computations.class_survey --periods 13 16 --width 17 --workers 2   # width 17, about 80 minutes
python -m computations.class_survey --block 0000001011011 --width 16          # one block, a few seconds
python -m computations.class_blocks                                          # the ten certificates, checked, 20 s
```

