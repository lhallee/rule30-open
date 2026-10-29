---
title: The finite game excludes 197 of the 8,800 blocks up to period 16
category: columns
problems: [1]
status: computed
formalization: partial
evidence: [computations/game.py]
---

# The finite game excludes 197 of the 8,800 blocks up to period 16

[The finite game](../../Rule30Open/Columns/FiniteGame.md) was run on every primitive block of period at most 16, at
widths 6, 10 and 14 in turn. It excludes 197 of the 8,800 blocks as the eventual period of any column of any row with a
leftmost 1, the center column of the single cell included. The kit excludes 61 of the 197 for the center column, and
136 are new. Lean checks 129 of the 136 by kernel computation ([the game in bit masks](../../Rule30Open/Columns/GameBlocks.md)
for 32 of period at most 14, [its sequel](../../Rule30Open/Columns/GameBlocksLong.md) for 97 of period 15 and 16); for
the other seven the computation is the proof.

## Result

The excluded blocks are both constant blocks, 3 of period 8 ($00000001$, $00000011$, $01111111$), 3 of period 10, 7 of
11, 9 of 12, 21 of 13, 31 of 14, 53 of 15 and 68 of 16. None of period 2 to 7 or 9 is excluded. Every excluded block of
period at most 14 that is not constant has a run of at least six 0s or seven 1s; at period 15 two do not,
$000001011111011$, whose runs are at most five long, and $000010111111011$, with four 0s and six 1s at most. The 28
blocks whose runs of 1s all last at least nine steps are among the 197, as
[the long-runs theorem](../../Rule30Open/Columns/LongRuns.md) requires, and so are the 64 blocks of the family of
[WallSegments](../../Rule30Open/Columns/WallSegments.md), which proves them, with every period of the family, by one
argument; of the 77 blocks with nine 1s in a row that the game excludes, 13 are outside that family, and
[WallSets](../../Rule30Open/Columns/WallSets.md), with sets of three-cell windows, proves all 77 the same way.

A certificate at one width gives one at every larger width, since a play of the larger game, read on its first cells,
is a play of the smaller one. So these are exactly the blocks of period at most 16 that the game excludes at some width
up to 14.

For blocks with only short runs, $01$ among them, the game fails at every width tried: some component of the game that
can hold a play shows the column left of the repeating one taking both values at one phase. A long run synchronizes
the cells beside the column; short runs leave the free cell's influence alive.

## Against the kit

`kit_blocks` in [computations/game.py](../../computations/game.py) lists the 62 primitive blocks of period at most 16
that the pinned kit excludes for the center column: its strip certificates, the blocks whose runs of 1s all last at
least nine steps, and the padded words $0^q1$ ($q \ge 9$), $0^r11$ ($r \ge 8$) and $0^q10111$ ($q \ge 9$). The kit's
other families, its white-padding families, its black-run blocks (Theorem B′) and its suffix families, only reach
periods above 16. Of the game's 197 blocks, 61 are among the kit's 62; the kit's $0^91$ is the one the game does not
exclude. The 136 blocks only the game excludes are 1 of period 8 ($00000001$), 2 of period 11, 2 of 12, 6 of 13, 23 of
14, 44 of 15 and 58 of 16.

[`GameBlocks`](../../Rule30Open/Columns/GameBlocks.md) checks 32 of the 34 of period at most 14 in Lean, at widths 5 to
12 with 448 to 32,768 nodes; the other two are $00000001001111$, which needs width 13 and 114,688 nodes, and
$00000000010001$, which needs width 14 and 229,376 nodes. [`GameBlocksLong`](../../Rule30Open/Columns/GameBlocksLong.md)
checks 97 of the 102 of period 15 and 16, at widths 5 to 9 with 134,720 nodes in all; the other five need width 12 to 14
and 65,536 to 262,144 nodes: $000000000101101$ and $000001011111011$ at width 14, $0000001011111011$ at 12,
$0000101111111011$ at 13 and $0001011111111001$ at 14.

## Reproduce

```bash
python -m computations.game --max-period 16 --widths 6,10,14
python -m computations.game --max-period 16 --widths 6,10,14 --kit
```

The first takes about 20 minutes on a laptop and prints the 197 blocks with the first width that excludes each; the
second also prints the 136 the kit does not exclude, with their least widths and node counts. With `--max-period 14`
they take about 2.5 minutes.

`game_certificate` in [computations/game.py](../../computations/game.py) exports a certificate for `FiniteGame.lean` when
the ranks fit in 8 bits, and `lean_certificate` prints it; `game_mask` and `lean_mask` export the bit-mask certificates
that `GameBlocks.lean` and `GameBlocksLong.lean` check.

## Open

The seven certificates left out have the same form as the others. At widths 12 to 14 each holds 65,536 to 262,144 nodes,
so together they would add a few megabytes of hexadecimal, and the kernel pays more per node there: about 0.1 ms at
width 12 and about 0.7 ms at width 14, where each number of ranks holds 16,384 of them. Packing the ranks in smaller
numbers may bring the time down. Adding them would make every one of the 197 exclusions kernel-checked, here or in the
kit.
