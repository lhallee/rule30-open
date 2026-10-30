---
title: No window of up to 18 cells locks for any block of period 2, 3, 5, 6, 7 or 9
category: columns
problems: [1]
status: negative
kind: no-signal
evidence: [computations/locks.py, computations/right_half.py]
---

# No window of up to 18 cells locks for any block of period 2, 3, 5, 6, 7 or 9

**Question.** Let column $k$ of a row with a leftmost 1 repeat a block $b$ of period $P$. A window of the $W$ cells
right of column $k$, at a phase of $b$, is locked when along every continuation, whatever the cell beyond the window
does, column $k - 1$ reads one value at each phase; Jen's theorem on adjacent columns forbids a locked window in the
true row. The finite game excludes $b$ only when every play eventually reaches a locked window, and
[steering](../../findings/columns/steerable-locks.md), [the coin lock](../../findings/columns/coin-lock.md) and
[LockWord](../../Rule30Open/Columns/LockWord.md) all lead windows into locked ones. For which periods does a locked
window exist at all?

**What was done.** `lock_census` in [computations/locks.py](../../computations/locks.py) runs `lock_info`, which finds
the locked windows of the game as the complement of the windows from which some play shows column $k - 1$ taking both
values at one phase, on every primitive block of a period at the given widths. It ran on periods 2 to 12 at width 13,
on the periods without a locked window at widths 16 and 18, and on periods 2 and 3 at width 20. A lock that repeats
with a multiple of $P$ contradicts Jen's theorem as well, so it also ran the game for blocks repeated, with the phase
counted modulo a multiple of $P$: modulo the least common multiple of $P$ and 4, the period of the kit's ether, for
every period, and modulo 10 and 21 for the periods of the partial locks of [the locking
simulation](../../findings/columns/period-four-locking.md).

**Outcome.**

- With the phase counted modulo $P$, no block of period 2 or 3 has a locked window at any width up to 20, and no block
  of period 5, 6, 7 or 9 at any width up to 18.
- With the phase counted modulo a multiple: $01$ modulo 4 has none up to width 18, and from width 19 it has the kit's
  ether-and-wall family, locked windows that only about half the windows can reach ([the absorption route for period
  two](../period-two/absorption-route.md)). The six blocks of period 5 have none modulo 10 up to width 16 or modulo 20
  up to width 18; $01$, $001$ and $011$ have none modulo 14 and 21 up to width 16; $001$ and $011$ none modulo 12 and
  the blocks of period 6 none modulo 12 up to width 16, those of period 7 none modulo 28 up to width 16, and those of
  period 9 none modulo 36 at width 13.
- The controls find locks where they exist. At width 13, 1 of the 3 primitive blocks of period 4 has a locked window, 8
  of the 30 of period 8, 9 of the 99 of period 10, 22 of the 186 of period 11 and 32 of the 335 of period 12; at width
  16 all three of period 4 have one. Both constant blocks lock, since the game excludes them ([the game
  blocks](../../findings/columns/game-blocks.md)).
- Wherever a block of period at most 12 has a locked window at width 13, every window of 13 cells can be steered into
  one: the blocks with a locked window are exactly the 72 steerable blocks.
- **Period 9 is singular.** In each of three families, $0^k 11101$, $0\,0\,1^k 0\,1$ and $0^k 101$, the blocks have
  locked windows of 13 cells at every period from 8 to the largest tried (17, 16 and 15), except 9; none has one at a
  period below 8. The locked windows of the first family show the mechanism: while the center is white, column 1 stays
  black whatever lies right of it, which fixes column $-1$ through the white run, and the lock holds when the block's
  last, black, phase finds columns 1 and 2 white, so that column 1 turns black as the run starts. At period 9 the
  mechanism fails completely: for $000011101$ and $001111101$ every window can reach both values of column $-1$ at every
  white phase.

**What it means.** The finite game and every lock built inside a window beside the repeating column say nothing about
periods 2, 3, 5, 6, 7 and 9 below these widths: the game cannot exclude such a block, and no sequence in a column beyond
the window constrains it. The gap matches two other observations, and period 9 sits inside it although periods 8, 10 and
11 do not. The game excludes no block of these periods up to period 16 ([the game
blocks](../../findings/columns/game-blocks.md)), and in [the locking
simulation](../../findings/columns/period-four-locking.md) no word of these periods locks from every start. Of the locks
that do occur there from some starts, those of $001$ (period 21) are wider: the kit's trap for $001$ is a strip of 47
columns whose first 38 repeat with period 21 ([the census for 001](../../findings/columns/t001-census.md)), and the
three starts that lock stay locked to step 200,000. Those of $01111$ are not locks at all: columns 1 to 8 to 12 repeat
with period 10 or 20 for thousands of steps, but no window of up to 18 cells locks even with the phase counted modulo
20, and followed to step 200,000 every one of the nine starts breaks, first between steps 12,385 and 20,905, and then
more than a thousand times (`right_half.lock_breaks`). For period two, [the absorption
route](../period-two/absorption-route.md) records that about half the windows of 19 to 21 columns cannot enter the kit's
family at all.

Heuristic: the kit's ether, the background of its period-four family, repeats with period 4 in time, which fits periods
4, 8 and 12; the locks at periods 10 and 11 rest on other structures, and none of the structures found at these widths
fits periods 2, 3, 5, 6, 7 or 9.

**Reproduce.**

```bash
python -m computations.locks --periods 2,3,5,6,7,9 --census 13,16,18 --workers 3
python -m computations.locks --periods 2,3 --census 20
python -m computations.locks --periods 2,3 --census 13,16 --repeat 7
python -m computations.locks --periods 5 --census 13,16 --repeat 2
python -m computations.locks --periods 2 --census 16,18,19,20 --repeat 2
python -m computations.locks --periods 3,7 --census 13,16 --repeat 4
python -m computations.locks --periods 6 --census 13,16 --repeat 2
python -m computations.locks --periods 9 --census 13 --repeat 4 --workers 2
python -m computations.locks --periods 4,8,10,11,12 --census 13 --workers 3
python -m computations.locks --census 13 --family '0^k 11101'   # also '00 1^k 01' and '0^k 101'
python -m computations.locks --mixed 000011101,001111101 --width 13
python -m computations.right_half 200000 30 --follow 01111:10
python -m computations.right_half 200000 30 --follow 001:21
```

The first takes about 20 minutes with three processes, most of it at width 18, and the census of periods 3 and 7
modulo 12 and 28 about 20 minutes with one; the others a few minutes each. The census with the phase modulo 20 for the
blocks of period 5 is `python -m computations.locks --periods 5 --census 13,16,18 --repeat 4`.
