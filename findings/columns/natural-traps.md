---
title: Driven right halves settle into traps for 27 of the 99 blocks of period 10, 51 of the 186 of period 11 and 75 of the 335 of period 12
category: columns
problems: [1]
status: computed
formalization: partial
evidence: [computations/lock_chain.py, computations/locks.py, computations/game.py]
---

# Driven right halves settle into traps for 27 of the 99 blocks of period 10, 51 of the 186 of period 11 and 75 of the 335 of period 12

A trap reduces a block to entry ([WordTraps](../../Rule30Open/Columns/WordTraps.md)): if every finitely supported right
half driven by the block reaches a set of windows that the rule never leaves, on which the cell beside the column is
fixed at the white phases, the center column does not eventually repeat the block. At periods 5, 6 and 7 driven halves
almost never settle near the center, and at period 9 a few do ([trap
entry](../../negative-results/columns/trap-entry.md)). From period 10 on many do, for a large share of the blocks.

## Method

`natural_scan` in [computations/lock_chain.py](../../computations/lock_chain.py), as in [trap
entry](../../negative-results/columns/trap-entry.md): the white right half and 30 random halves of 64 cells
(`right_half.random_starts(30, 64)`) are driven by every primitive block for 20,000 steps. A half whose column 1 repeats
at the white times over the second half, and keeps repeating to step 60,000, is closed at steps 12,000, 16,000 and
19,999 under both values of the cell beyond, at each width from 16 to 64 and with the phase counted modulo the lock's
period or twice it; the least width whose closure has at most 100,000 states and fixes column 1 at the white phases is
a trap that the half has entered.

## Result

| Period | Blocks | Lock for some start | A start inside a trap | Every start inside one | Trap wider than 16 cells | Phase modulo a multiple | Locked window of 13 cells | Excluded by the game |
|---|---|---|---|---|---|---|---|---|
| 8 | 30 | 8 | 8 | 8 | 0 | 0 | 8 | 3 |
| 10 | 99 | 36 | 27 | 18 | 15 | 3 | 9 | 3 |
| 11 | 186 | 53 | 51 | 38 | 20 | 4 | 21 | 7 |
| 12 | 335 | 78 | 75 | 48 | 34 | 1 | 32 | 9 |

The last four columns count blocks with a trap: those whose least trap needs more than 16 cells, those whose traps all
count the phase modulo a multiple of the period, those with a locked window of 13 cells (`locks.has_lock`), and those
[the finite game](game-blocks.md) excludes. Every block of these periods with a locked window of 13 cells has a start
inside a trap but one of period 11. At period 8 the traps are exactly the window locks of 13 cells, of the eight blocks
that have one, each entered by every start, and none needs more than 16 cells. The same scan finds none at period 5, 6
or 7, and one start each for six blocks of period 9.

- **Period 10: one background.** The traps found there have 100 states in 269 of the 618 pairs of a block and a start
  inside a trap. They are one trap: the wall of $0000010001$, 16 cells, carried leftward by its chain to the blocks
  $0011010111$, $0010101111$, $0001101111$, $0001110011$ and $0000010101$ at distances 2, 5, 6, 7 and 9, where it is the
  least trap of each. The chain repeats with period 155 in the distance, so the wall is the edge of a background of
  period 10 in time and 155 in space; its columns hold 28 blocks of period 10, among them, at distances 20 to 28, the
  nine with locked windows of 13 cells ([TenTraps](../../Rule30Open/Columns/TenTraps.md)). Every right half with support
  in cells 1 to 8 enters the wall from every phase within 3,042 steps, a median of 238, and the white half by step 74.
  Entry does not wait for a long tail to clear: random halves of 16, 64, 256 and 1,024 cells all enter, 120 of each from
  phases 0 and 5, with medians of 172 to 266 steps and the latest at 2,955. Rule 30's own halves enter about as fast as
  a fair coin in column 17 would bring them: every window can enter within 81 steps, with a coin the expected entry is
  at most 482 steps and the chance of staying out falls by a factor 0.99746 per step, below $7 \cdot 10^{-14}$ after
  12,000 steps from every window, and one word of 569 values of column 17, mostly white, brings every window at phase 0
  in, while a constant column 17 does not (`ten_coin`, `ten_lengths`). For the words of period four, a few percent of
  Rule 30's halves stay out of the coin's certificate by building ether plugs ([a fair coin beyond it](coin-lock.md));
  here none of those sampled does.
- **Periods 11 and 12: backgrounds too.** The traps recur with few sizes there as well: of the 1,364 pairs at period 11,
  263 are inside traps of 313 states, 181 of 103 and 74 of 138; of the 1,857 at period 12, 386 of 119, 159 of 116 and
  110 of 150. Each of these six is a wall whose chain becomes periodic in the distance (`wall_chains`): at period 11 the
  walls of $00000011011$, $00110100111$ and $00001101001$, 16 cells each, with spatial periods 143, 275 and 143 from
  distances 23, 9 and 0, whose chains hold 33, 31 and 13 blocks of period 11, 57 in all; at period 12 the walls of
  $001011100111$, $000110110011$ and $000010011111$, with spatial periods 60, 138 and 138 from distances 41, 0 and 7,
  holding 50, 45 and 51 blocks, 97 in all, 95 of them beyond the kit. At period 10 the three commonest sizes, 100, 6,413
  and 18,038 states, are walls of the one background of spatial period 155. In Lean, the walls carried up to 40 columns
  give traps to 57 blocks of period 11 and 83 of period 12 that the kit does not exclude
  ([ElevenTraps](../../Rule30Open/Columns/ElevenTraps.md), [TwelveTraps](../../Rule30Open/Columns/TwelveTraps.md));
  every half of at most eight cells enters the walls of $00000011011$, $001011100111$ and $000110110011$ within 1,594,
  2,341 and 2,810 steps, and [WallGaps](../../Rule30Open/Columns/WallGaps.md) carries the first two along the light
  cone, as [TenGap](../../Rule30Open/Columns/TenGap.md) does at period 10.
- **The traps found, in Lean.** Of the 153 blocks of periods 10 to 12 with a start inside a trap, the walls carry traps
  to 100 in Lean, the kit or the game excludes 18, and the other 35 have the trap the scan finds, one per block up to a
  shift of its labels; none of the 35 lies in the chain of a wall. Every right half with support in cells 1 to 4 enters
  30 of these traps from every phase within 20,000 steps, 29 of them within 8,622; the other five, 22 to 44 cells wide,
  are entered by 7 to 52 of the 160 to 192 pairs of a half and a phase (`extra_entry`). The kernel checks all 35
  ([NaturalTraps](../../Rule30Open/Columns/NaturalTraps.md)), the trap of $00010001011$, 61,857 windows of 30 cells, in
  parts ([NaturalTrapsLarge](../../Rule30Open/Columns/NaturalTrapsLarge.md)).
- **A fair coin beyond the window.** As for the period-10 wall, a fair coin in column 17 in place of the cells beyond
  brings every window into each of the 29 traps of 16 cells of [NaturalTraps](../../Rule30Open/Columns/NaturalTraps.md):
  every window can enter within 59 to 123 steps, the expected entry is at most 79 to 1,549 steps, and the chance of
  staying out falls by a factor of 0.952 to 0.9993 per step, below $2.5 \cdot 10^{-4}$ after 12,000 steps for every
  trap and below $10^{-11}$ for 25 of them (`natural_coin`, the power iteration capped at 2,000 periods). A constant
  column 17 brings every window in for 8 of them, white for five and black for five. The trap slowest under the coin,
  that of $001110111101$, is also the one Rule 30's own small halves take longest to enter, within 8,622 steps.
- **Periods 13 and 14, windows of 16 cells.** Closing windows of 16 cells only (`--max-width 16`, since wider closures
  make the scan of these periods run for hours), the scan finds traps for 86 of the 630 blocks of period 13, every
  sampled start inside one for 76 of them, and for 109 of the 1,161 of period 14, every start for 105; at periods 10 to
  12 the same width holds traps for 12, 31 and 41 blocks. The commonest traps are again walls of one background each, of
  689 cells at period 13 and of 728 at period 14 ([backgrounds periodic in time](space-time-backgrounds.md)), and
  carried leftward the smallest wall of each gives traps to every block of the period among that background's columns,
  53 and 101 ([ThirteenTraps](../../Rule30Open/Columns/ThirteenTraps.md),
  [FourteenTraps](../../Rule30Open/Columns/FourteenTraps.md)). Of the other blocks with a trap that nothing excludes,
  the 74 whose traps have at most 3,000 states have them checked as they are
  ([NaturalTrapsLong](../../Rule30Open/Columns/NaturalTrapsLong.md)); every right half of up to four cells enters 61 of
  those from every phase.

## What it means

The gap of the trap route at periods 5, 6 and 7 does not persist: from period 10 about a quarter of the blocks have
traps that random halves enter, often every sampled half and within a few thousand steps, as small halves enter the
kit's family for the words of period four ([the absorption census](absorption-census.md)). For these blocks the
reduction to entry has the same kind of support as the kit's period-four reduction, and the same open step: entry for
every finite half. Period 9 sits between, with two walls that small halves enter at a slow, steady rate. At each of
periods 9 to 12 the traps are the edges of backgrounds, periodic in time and in space, and the chains of one to three
walls reach close to a third of the blocks of the period: 21 of the 56 of period 9, 28 of 99, 57 of 186 and 97 of 335,
though the traps carried far from a wall are rarely entered. The traps are found from the dynamics, not from the game,
which excludes few of these blocks: for $0000010001$ the game stays open at every width up to 18, and at widths 12 to 16
through one large component even with Jen's theorem on farther columns, where a free cell beyond the window keeps column
1 from locking.

## Reproduce

```bash
python -m computations.lock_chain --natural 8 --steps 20000
python -m computations.lock_chain --natural 10,11,12 --steps 20000 --workers 4 > natural.txt
python -m computations.lock_chain --natural-from natural.txt
python -m computations.lock_chain --entry trap0000010001 --cells 8 --steps 50000
python -m computations.lock_chain --entry trap0000010001 --cells 0 --steps 200000
python -m computations.lock_chain --ten-entry --cells 6 --steps 20000
python -m computations.lock_chain --ten-coin
python -m computations.lock_chain --walls-entry 11 --cells 4 --steps 20000
python -m computations.lock_chain --walls-entry 12 --cells 4 --steps 20000
python -m computations.lock_chain --extra-entry --cells 4 --steps 20000
python -m computations.lock_chain --natural 13,14 --steps 20000 --max-width 16 --workers 3
python -m computations.lock_chain --natural-coin
```

The first takes under two minutes and the second about 48 with four processes and prints each block that locks for some
start, with its traps, and the summary of each period, which the third prints again from the saved output, with the
walls of the commonest traps and their chains; the fourth takes about a minute, the fifth seconds, the sixth, entry into
each trap of [TenTraps](../../Rule30Open/Columns/TenTraps.md), about 7 minutes, and the seventh, the coin and the halves
of growing length, about a minute and a half; the eighth and ninth, entry into each trap of
[ElevenTraps](../../Rule30Open/Columns/ElevenTraps.md) and [TwelveTraps](../../Rule30Open/Columns/TwelveTraps.md), about
20 minutes each; and the last, entry into each trap of [NaturalTraps](../../Rule30Open/Columns/NaturalTraps.md) and
[NaturalTrapsLarge](../../Rule30Open/Columns/NaturalTrapsLarge.md), about four minutes; the scan of periods 13 and 14
with windows of 16 cells takes about 40 minutes with three processes, and the coin for the 29 traps about 50 minutes.
