---
title: The finite game excludes 76 of the 2,538 blocks up to period 14
category: columns
problems: [1]
status: computed
formalization: partial
evidence: [computations/game.py]
---

# The finite game excludes 76 of the 2,538 blocks up to period 14

[The finite game](../../Rule30Open/Columns/FiniteGame.md) was run on every primitive block of period at most 14, at
widths 6, 10 and 14 in turn. It excludes 76 of the 2,538 blocks as the eventual period of any column of any row with a
leftmost 1, the center column of the single cell included. The kit excludes 42 of the 76 for the center column, and
34 are new. Lean checks 32 of the 34 by kernel computation ([the game in bit masks](../../Rule30Open/Columns/GameBlocks.md));
for the other two the computation is the proof.

## Result

The excluded blocks are both constant blocks, 3 of period 8 ($00000001$, $00000011$, $01111111$), 3 of period 10, 7 of
11, 9 of 12, 21 of 13 and 31 of 14. None of period 2 to 7 or 9 is excluded. Every excluded block has a run of at least
six 0s or seven 1s, and the 15 blocks whose runs of 1s all last at least nine steps are among them, as
[the long-runs theorem](../../Rule30Open/Columns/LongRuns.md) requires.

A certificate at one width gives one at every larger width, since a play of the larger game, read on its first cells,
is a play of the smaller one. So these are exactly the blocks of period at most 14 that the game excludes at some width
up to 14.

For blocks with only short runs, $01$ among them, the game fails at every width tried: some component of the game that
can hold a play shows the column left of the repeating one taking both values at one phase. A long run synchronizes
the cells beside the column; short runs leave the free cell's influence alive.

## Against the kit

`kit_blocks` in [computations/game.py](../../computations/game.py) lists the 43 primitive blocks of period at most 14
that the pinned kit excludes for the center column: its strip certificates, the blocks whose runs of 1s all last at
least nine steps, and the padded words $0^q1$ ($q \ge 9$), $0^r11$ ($r \ge 8$) and $0^q10111$ ($q \ge 9$). The kit's
other families only reach periods above 14. Of the game's 76 blocks, 42 are among the kit's 43; the kit's $0^91$ is
the one the game does not exclude. The 34 blocks only the game excludes are 1 of period 8 ($00000001$), 2 of period 11,
2 of 12, 6 of 13 and 23 of 14, each listed with the least width the game needs.

[`GameBlocks`](../../Rule30Open/Columns/GameBlocks.md) checks 32 of the 34 in Lean, at widths 5 to 12 with 448 to
32,768 nodes. The other two are $00000001001111$, which needs width 13 and 114,688 nodes, and $00000000010001$, which
needs width 14 and 229,376 nodes.

## Reproduce

```bash
python -m computations.game --max-period 14 --widths 6,10,14
python -m computations.game --max-period 14 --widths 6,10,14 --kit
```

The first takes about 2.5 minutes on a laptop and prints the 76 blocks with the first width that excludes each; the
second also prints the 34 the kit does not exclude, with their least widths and node counts.

`game_certificate` in [computations/game.py](../../computations/game.py) exports a certificate for `FiniteGame.lean` when
the ranks fit in 8 bits, and `lean_certificate` prints it; `game_mask` and `lean_mask` export the bit-mask certificates
that `GameBlocks.lean` checks.

## Open

The certificates for $00000001001111$ and $00000000010001$ have the same form as the 32 in `GameBlocks`. They are left
out of the build because together they would add about 0.9 MB of hexadecimal to the module, and checked on their own
they take about 16 s and 163 s. The cost per node grows with the width, from about 0.1 ms at width 12 to about 0.7 ms
at width 14, where each number of ranks holds 16,384 of them; packing the ranks in smaller numbers may bring it down.
Adding them would make every one of the 76 exclusions kernel-checked, here or in the kit.
