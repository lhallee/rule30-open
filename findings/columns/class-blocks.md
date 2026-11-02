---
title: The game with cyclic classes closes ten blocks of period 13 to 16, eight of period 17 and fifteen of period 18 that nothing else excludes
category: columns
problems: [1]
status: computed
formalization: partial
evidence: [computations/class_survey.py, computations/game.py, computations/class_blocks.py, computations/class_blocks_wide.py, computations/class_blocks_split.py, computations/class_blocks_18.py, computations/class_blocks_18_split.py, computations/class_certificate.py]
---

# The game with cyclic classes closes ten blocks of period 13 to 16, eight of period 17 and fifteen of period 18 that nothing else excludes

[The game with cyclic classes](class-game.md) was run at 16 cells on every primitive block of period 13 to 16 with both
colors, 8,053 blocks. It closes 186 of them; the plain game at 16 cells closes 176, and the class test closes ten more,
which neither the kit nor any other exclusion of this repository reaches. Lean proves all ten: no column of a row with a
leftmost 1, the center column of the single cell among them, eventually repeats any of them, in any rotation
([ClassBlocks](../../Rule30Open/Columns/ClassBlocks.md), [ClassBlocks13](../../Rule30Open/Columns/ClassBlocks13.md),
[ClassBlocks14](../../Rule30Open/Columns/ClassBlocks14.md), [ClassBlocks16](../../Rule30Open/Columns/ClassBlocks16.md),
[ClassBlocks16Wide](../../Rule30Open/Columns/ClassBlocks16Wide.md)). The plain game at 15 or 16 cells also closes three
blocks that its surveys at widths up to 14 miss and that nothing else excludes;
[GameBlocksWide](../../Rule30Open/Columns/GameBlocksWide.md) proves them with the same certificates.

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
enters them. [GameBlocksWide](../../Rule30Open/Columns/GameBlocksWide.md) excludes all three unconditionally.

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
the counts above, rest on the computation. The three blocks the plain game closes at 15 or 16 cells are in
[GameBlocksWide](../../Rule30Open/Columns/GameBlocksWide.md), with the same certificates: the game's test is the class
test's case $d = P$.

## Reproduce

```bash
python -m computations.class_survey --periods 13 16 --width 16 --workers 2   # the tables, about 18 minutes
python -m computations.class_survey --periods 13 16 --width 17 --workers 2   # width 17, about 80 minutes
python -m computations.class_survey --block 0000001011011 --width 16          # one block, a few seconds
python -m computations.class_blocks                                          # the ten certificates, checked, 20 s
```

## Period 17

The same survey at 16 cells on every primitive block of period 17 with both colors, 7,710 blocks, finds five more
blocks that nothing else excludes, and Lean proves all five ([ClassBlocks17](../../Rule30Open/Columns/ClassBlocks17.md),
[ClassBlocks17Mid](../../Rule30Open/Columns/ClassBlocks17Mid.md),
[ClassBlocks17Wide](../../Rule30Open/Columns/ClassBlocks17Wide.md)). The plain game at 16 cells closes 120 blocks, the
119 that [the game blocks of period 17 and 18](game-blocks-18.md) find at widths up to 14 and one more; the class test
closes those 120 and four more. The 12 blocks of period 17 that the kit excludes are among the 120.

| Block | Closed by | Least width of the class test | Components at that width that can hold a play: nodes (cyclic period) |
|---|---|---:|---|
| $00000000011111001$ | classes only | 12 | 1,894 (17); 100 (34, mixed by phase); 45 (34, mixed by phase); 32 (17) |
| $00011011111111001$ | the game at 15 cells, not at 14 | 13 | 1,077 (17); 432 (17); 122 (17); 61 (51, mixed by phase); 28 (17); 25 (17) |
| $00000000010010001$ | classes only | 14 | 1,212 (17); 603 (17); 394 (17); 105 (51, mixed by phase); 39 (17); 27 (17); 18 (17) |
| $00000011011111011$ | classes only | 14 | 2,768 (17); 231 (17); 89 (34, mixed by phase); 56 (17); 53 (17); 52 (17); 49 (17); 22 (17); 22 (17) |
| $00000000001000001$ | classes only | 16 | 12,686 (17); 175 (68, mixed by phase); 149 (17); 77 (17); 31 (17) |

"Classes only" means the plain game does not close the block at 16 cells (`game.bad_pairs` is 2, 5, 1 and 1 at 16
cells, in the table's order). For none of the five does `class_survey.elsewhere` find the kit, the wall sets or the
limit windows of 14 cells, and no other Lean module names any of them. The certificates, at the least
widths above, check 16,040 to 150,894 nodes over the widths and 4,820 to 43,758 nodes for the classes
(`class_blocks_wide`, each checked node by node by `class_certificate.check`).

At 17 cells the survey of period 17 closes three blocks more, which nothing else excludes either: the class test
closes $00011111111110101$ and $01010111111111111$ (the plain game fails at one phase in a component of 142 nodes and
cyclic period 51, and of 151 nodes and cyclic period 34), and both tests close $01111011111111111$; neither test closes
any of the three at 16 cells. At 17 cells the plain game also closes $00000000010010001$, which the class test closes
at 14. So at 17 cells the plain game closes 122 blocks of period 17 and the class test 127, and the blocks that nothing
else excludes number eight. The certificates of the three at 17 cells check 175,714 to 227,810 nodes over the widths
and 51,430 to 65,607 for the classes. Lean proves all three:
[ClassBlocks17Cells](../../Rule30Open/Columns/ClassBlocks17Cells.md) proves $01010111111111111$, the smallest, in one
module, and [ClassBlocks17Split](../../Rule30Open/Columns/ClassBlocks17Split.md) proves $00011111111110101$ (205,288
nodes over the widths and 58,385 for the classes) and $01111011111111111$ (227,810 and 65,607), each certificate checked
over three modules: widths 1 to 15, widths 16 and 17, and the classes (`class_blocks_split`). The check of a width reads
only the heights of that width and the one before, so the checks on a certificate with the first widths carry to the
full one ([ClassSplit](../../Rule30Open/Columns/ClassSplit.md)). So all eight blocks of period 17 that the class test
closes at 16 or 17 cells and nothing else excludes are excluded in Lean.

The three blocks of period 14 and 16 that the plain game closes at 15 or 16 cells are proved in
[GameBlocksWide](../../Rule30Open/Columns/GameBlocksWide.md) with the same certificates; the class test closes
$00110011111111$ at 13 cells, three fewer than the plain game needs, and the other two at 15.

```bash
python -m computations.class_survey --periods 17 17 --width 16 --workers 2 --out rows17.jsonl   # about 45 minutes
python -m computations.class_blocks_wide --report rows17.jsonl   # the five blocks, their widths and other exclusions
python -m computations.class_survey --periods 17 17 --width 17 --workers 2 --out rows17w.jsonl  # about 75 minutes
python -m computations.class_blocks_wide --report rows17w.jsonl  # the eight blocks at 17 cells
python -m computations.class_blocks_wide                         # all eleven certificates, checked node by node, 40 s
python -m computations.class_blocks_split                        # the two split certificates, checked, 20 s
```

## Period 18

The same survey at 16 cells on every primitive block of period 18 with both colors, 14,532 blocks, finds fifteen blocks
that the plain game at widths up to 14 leaves open, that the game or the class test closes at 16 cells, and that
nothing else excludes. The plain game at 16 cells closes 147 blocks: the 142 that [the game blocks of period 17 and
18](game-blocks-18.md) find at widths up to 14, and five more, one first at 15 cells and four first at 16. The class
test closes those 147 and ten more. The 14 blocks of period 18 that the kit excludes are among the 147. For none of
the fifteen does `class_survey.elsewhere` find the kit, the wall sets or the limit windows of 14 cells; no Lean module
outside those below names any of them, and no rotation of any of them appears in the Lean sources of the pinned kit or
of the kit's main branch, whose new families (four-category grammars, white runs of at least 17, black runs $1^r u$
with $u$ of at most five cells) do not contain them. Lean proves all fifteen: the five with the smallest certificates,
$001111111111011101$, $001001101111111111$, $000000000100000001$, $000000000010010011$ and $000000000000111011$, each
certificate in a single module ([ClassBlocks18](../../Rule30Open/Columns/ClassBlocks18.md),
[ClassBlocks18Mid](../../Rule30Open/Columns/ClassBlocks18Mid.md),
[ClassBlocks18Wide](../../Rule30Open/Columns/ClassBlocks18Wide.md)), and the other ten with each certificate checked
over two or three modules ([ClassBlocks18Split](../../Rule30Open/Columns/ClassBlocks18Split.md)).

| Block | Closed by | Least width of the class test | Components at that width that can hold a play: nodes (cyclic period) |
|---|---|---:|---|
| $001111111111011101$ | classes only | 8 | 369 (18); 129 (36, mixed by phase); 64 (18); 22 (18) |
| $001001101111111111$ | classes only | 11 | 393 (18); 333 (36, mixed by phase); 149 (18); 41 (18) |
| $000000000100000001$ | the game at 16 cells | 13 | 3,083 (18); 90 (54, mixed by phase); 29 (18) |
| $001010100111111111$ | classes only | 14 | 8,745 (18); 542 (36, mixed by phase) |
| $000000000000111011$ | classes only | 15 | 6,861 (18); 459 (36, mixed by phase); 32 (18); 20 (18) |
| $000000000010010011$ | classes only | 15 | 2,538 (18); 1,292 (36, mixed by phase); 88 (18); 73 (18); 42 (18) |
| $000011111111111101$ | classes only | 15 | 7,701 (18); 292 (18); 214 (18); 161 (36, mixed by phase); 63 (18); 59 (18) |
| $011110111111111111$ | classes only | 15 | 4,864 (18); 219 (18); 166 (54, mixed by phase) |
| $000000000011000101$ | the game at 16 cells | 15 | 8,227 (18); 57 (36, mixed by phase); 53 (18); 30 (18); 27 (18); 24 (18) |
| $001111001111111111$ | the game at 15 cells | 15 | 12,331 (18); 52 (18); 26 (18) |
| $000000000011111001$ | classes only | 16 | 13,724 (18); 1,505 (18); 119 (36, mixed by phase) |
| $000010111111111001$ | classes only | 16 | 14,726 (18); 470 (36, mixed by phase); 222 (36, mixed by phase) |
| $001011111111110111$ | classes only | 16 | 14,228 (18); 576 (36, mixed by phase); 145 (36); 55 (18); 53 (18) |
| $000000000001000001$ | the game at 16 cells | 16 | 12,331 (18); 52 (18); 26 (18) |
| $000000011011111001$ | the game at 16 cells | 16 | 6,774 (18); 105 (18); 24 (18) |

"Classes only" means the plain game does not close the block at 16 cells (`game.bad_pairs` at 16 cells is 1 to 4 for
the ten). "The game at 15 cells" and "at 16 cells" give the least width at which the plain game closes the block; it
does not at 14 cells, so [BitBlocks18](../../Rule30Open/Columns/BitBlocks18.md) and
[BitPhases](../../Rule30Open/Columns/BitPhases.md) do not reach it. The class test closes $000000000100000001$ at 13
cells, three fewer than the plain game needs. Every component mixed by phase has a cyclic period of two or three
periods of the block. The certificates at the least widths above check 3,696 to 152,538 nodes over the widths and 998
to 43,557 for the classes (`class_blocks_18`, each checked node by node by `class_certificate.check`). The ten in
[ClassBlocks18Split](../../Rule30Open/Columns/ClassBlocks18Split.md) have certificates of 87,205 to 194,697 nodes in
all; `class_blocks_18_split` checks each over a module of the heights of every width, or two (widths 1 to 15 and width
16) for the five at 16 cells, and a module of the classes, so that no module holds more than 98,060 nodes of tables,
the same way as [ClassBlocks17Split](../../Rule30Open/Columns/ClassBlocks17Split.md). The 25 modules peak at 1.1 to
2.2 GB.

```bash
python -m computations.class_survey --periods 18 18 --width 16 --workers 2 --out rows18.jsonl   # about 40 minutes
python -m computations.class_blocks_wide --report rows18.jsonl   # the fifteen blocks, their widths and other exclusions
python -m computations.class_blocks_18                           # all fifteen certificates, checked node by node, 45 s
python -m computations.class_blocks_18_split                     # the ten split certificates, every part's size, 45 s
```
