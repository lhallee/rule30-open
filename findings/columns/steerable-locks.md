---
title: For 72 blocks of period at most 12, every window of 13 cells can be steered into a lock
category: columns
problems: [1]
status: computed
formalization: partial
evidence: [computations/locks.py, computations/lock_word.py, computations/game.py, computations/right_half.py]
---

# For 72 blocks of period at most 12, every window of 13 cells can be steered into a lock

Let column $k$ of a row with a leftmost 1 repeat a block $b$. A node of [the finite
game](../../Rule30Open/Columns/FiniteGame.md) at width 13 is a phase of $b$ and the cells $k + 1, \dots, k + 13$;
call it locked when along every continuation, whatever column $k + 14$ does, column $k - 1$ reads one value at each
phase. Jen's theorem on adjacent columns forbids a locked node in the true row. The game excludes $b$ when every play
is eventually locked. This finding asks a weaker question: whether some values of column $k + 14$ lead every node to a
locked one. Of the 745 primitive blocks of period 2 to 12, 72 have this property: 1 of period 4, 8 of period 8, 9 of
period 10, 22 of period 11 and 32 of period 12, and none of period 2, 3, 5, 6, 7 or 9. The game excludes 22 of them and
the kit one more, $0^9 1$. For the other 49, one sequence of 71 to 1,749 values leads every node, from every phase, to a
locked node, so once column $k$ repeats $b$, column $k + 14$ never reads that sequence; Lean proves this for all 49
([LockBlocks11](../../Rule30Open/Columns/LockBlocks11.md), [LockBlocks12](../../Rule30Open/Columns/LockBlocks12.md)).
Sixteen of the 49 have no run of more than four equal values, a kind of block the game has never excluded.

## Result

`lock_info` in [computations/locks.py](../../computations/locks.py) computes the locked nodes as the complement of the
nodes from which some play reaches both values of column $k - 1$ at one phase, and the nodes from which some play
reaches a locked one. A block is steerable when some node is locked and every node can reach one. For the 50 steerable
blocks that the game does not exclude at width 14, the table gives the longest run (read cyclically), the share of
nodes that are locked, the length of the sequence `steering` builds, and the growth rate per step of the number of
sequences of column $k + 14$ that keep a node out of the locked ones (`lock_word.avoid_growth`), with its base-2
logarithm.

| Block | Longest run | Locked | Sequence | Growth | Entropy at most |
|---|---:|---:|---:|---:|---:|
| $0111$ | 3 | 5.8% | 323 | 1.969279 | 0.97767 |
| $00000101$ | 5 | 5.3% | 398 | 1.983241 | 0.98786 |
| $00011101$ | 3 | 6.9% | 903 | 1.991728 | 0.99402 |
| $00011111$ | 5 | 11.0% | 280 | 1.965533 | 0.97492 |
| $00111101$ | 4 | 14.3% | 332 | 1.972016 | 0.97967 |
| $00111111$ | 6 | 43.1% | 93 | 1.901928 | 0.92746 |
| $0000000001$ (the kit's) | 9 | 28.1% | 78 | 1.903817 | 0.92889 |
| $0000000101$ | 7 | 7.4% | 254 | 1.989813 | 0.99263 |
| $0000011101$ | 5 | 11.2% | 449 | 1.982016 | 0.98697 |
| $0001111111$ | 7 | 16.0% | 275 | 1.976424 | 0.98289 |
| $0011111101$ | 6 | 23.3% | 199 | 1.949595 | 0.96317 |
| $0111011111$ | 5 | 4.3% | 655 | 1.992615 | 0.99466 |
| $00000000101$ | 8 | 14.0% | 222 | 1.976369 | 0.98285 |
| $00000011101$ | 6 | 21.0% | 141 | 1.904319 | 0.92928 |
| $00000110001$ | 5 | 0.9% | 1,409 | 1.999982 | 0.99999 |
| $00000110011$ | 5 | 5.0% | 554 | 1.983648 | 0.98816 |
| $00001001101$ | 4 | 5.6% | 863 | 1.982912 | 0.98762 |
| $00001101011$ | 4 | 14.6% | 513 | 1.972758 | 0.98021 |
| $00001111111$ | 7 | 35.9% | 289 | 1.905988 | 0.93054 |
| $00011111111$ | 8 | 28.6% | 314 | 1.986528 | 0.99025 |
| $00101101111$ | 4 | 10.8% | 1,725 | 1.999890 | 0.99992 |
| $00110011111$ | 5 | 2.5% | 620 | 1.983483 | 0.98804 |
| $00111111101$ | 7 | 42.8% | 250 | 1.969569 | 0.97788 |
| $01010101011$ | 2 | 3.3% | 534 | 1.985754 | 0.98969 |
| $01011111011$ | 5 | 26.2% | 711 | 1.983639 | 0.98815 |
| $01110111111$ | 6 | 11.9% | 466 | 1.980582 | 0.98592 |
| $01111011111$ | 5 | 1.6% | 1,749 | 1.998606 | 0.99899 |
| $000000001011$ | 8 | 28.2% | 81 | 1.846324 | 0.88466 |
| $000000010001$ | 7 | 7.9% | 165 | 1.955976 | 0.96789 |
| $000000011101$ | 7 | 18.2% | 179 | 1.928166 | 0.94723 |
| $000000110011$ | 6 | 18.1% | 321 | 1.984249 | 0.98859 |
| $000001001101$ | 5 | 3.5% | 946 | 1.994771 | 0.99622 |
| $000001101011$ | 5 | 11.1% | 197 | 1.948694 | 0.96251 |
| $000010010001$ | 4 | 6.1% | 646 | 1.959543 | 0.97052 |
| $000010101001$ | 4 | 0.9% | 1,098 | 1.997687 | 0.99833 |
| $000011011011$ | 4 | 16.6% | 483 | 1.962926 | 0.97301 |
| $000011111111$ | 8 | 50.5% | 71 | 1.845414 | 0.88394 |
| $000100111101$ | 4 | 4.8% | 632 | 1.986111 | 0.98995 |
| $000101011111$ | 5 | 2.2% | 621 | 1.987675 | 0.99108 |
| $000101101011$ | 3 | 3.3% | 769 | 1.992793 | 0.99479 |
| $000111001101$ | 3 | 2.1% | 808 | 1.993721 | 0.99546 |
| $001001101111$ | 4 | 11.8% | 281 | 1.979638 | 0.98524 |
| $001011011111$ | 5 | 7.8% | 502 | 1.984793 | 0.98899 |
| $001011111011$ | 5 | 29.1% | 370 | 1.966986 | 0.97599 |
| $001100111111$ | 6 | 17.0% | 569 | 1.978627 | 0.98450 |
| $001110111101$ | 4 | 1.5% | 1,034 | 1.997361 | 0.99810 |
| $001111111101$ | 8 | 37.7% | 173 | 1.949889 | 0.96339 |
| $010101010111$ | 3 | 1.7% | 523 | 1.982105 | 0.98703 |
| $010111111011$ | 6 | 22.3% | 376 | 1.971918 | 0.97960 |
| $011101111111$ | 7 | 37.4% | 362 | 1.980222 | 0.98566 |

- **Short runs.** Sixteen blocks have no run of more than four equal values: $0111$, $00011101$, $00111101$,
  $00001001101$, $00001101011$, $00101101111$, $01010101011$, $000010010001$, $000010101001$, $000011011011$,
  $000100111101$, $000101101011$, $000111001101$, $001001101111$, $001110111101$ and $010101010111$. Every block other
  than the constant ones that the game excludes up to period 20 has a run of at least five ([the game
  blocks](game-blocks.md), [period 19 and 20](game-blocks-20.md)).
- **White runs.** For 29 of the 49 blocks the all-white sequence steers at some width from 4 to 16: a run of white
  cells in one column forces the lock, the shortest being 27 cells in column 8 for $000011111111$. Lean checks the 22
  whose shortest run comes at a width of at most 13 ([LockWhite](../../Rule30Open/Columns/LockWhite.md)).
- **Locks are always reachable.** At width 13 the blocks of period at most 12 with any locked node are exactly the 72
  steerable ones; no block of period 2, 3, 5, 6, 7 or 9 has a locked node up to width 18 ([window
  locks](../../negative-results/columns/window-locks.md)).
- **Period four.** Of the three primitive words of period four only $0111$ is steerable at width 13;
  [LockWord](../../Rule30Open/Columns/LockWord.md) steers $0011$ at width 14 and $0001$ at width 16 into the kit's
  family.
- **Against the simulation.** [The locking finding](period-four-locking.md) drives 31 right halves, the empty one and 30
  random ones of 64 cells, for 12,000 steps with each block, and 109 blocks of period 4 to 12 lock from every start.
  Every steerable block is among them except $00000110001$, which locks from none. It has the smallest share of locked
  nodes and the growth rate nearest 2: a fair coin beyond the window would stay out of the lock with a chance that falls
  by a factor of 0.999991 per step, about $e$ every 110,000 steps, far beyond the simulation. The other 38 blocks that
  lock from every start are not steerable at width 13, as $0001$ and $0011$ are not.
- **At 16 cells, periods 10 to 15.** The census of locked windows of 16 cells ([backgrounds periodic in
  time](space-time-backgrounds.md)) gives 478 blocks of periods 10 to 15 with a locked node: 12, 30, 41, 89, 109 and
  197. For 475 every node of the game of 16 cells can be steered into a locked node: all of periods 10, 11, 12 and 14,
  88 of the 89 of period 13 and 195 of the 197 of period 15. The other three, $0000010111001$, $000001010110101$ and
  $001001111010111$, are those whose traps [MissedTraps](../../Rule30Open/Columns/MissedTraps.md) refutes: from their
  white window no locked node can be reached, at 16, 17 or 18 cells. So at 16 cells, unlike at 13 up to period 12, a
  block can have locks that most windows never reach. The commands are under Reproduce.

## What it means

Once the center column of the single cell repeats one of the 49 blocks, column 14 must keep the window out of the
locked nodes forever. The words of length $n$ that column 14 can then read, after the time the center starts repeating,
number at most a constant times the growth rate to the $n$th power, so column 14 has topological entropy at most the
logarithm in the table: from 0.88 bits per step for $000000001011$ and $000011111111$ to 0.99999 for
$00000110001$. In particular column 14 never reads the block's sequence after that time. So any of these blocks is
excluded if column 14 reads its sequence at arbitrarily late times, which holds if column 14 contains every finite word
at arbitrarily late times, a statement of the same kind as Problem 2 and open. The bounds are close to 1, so the
constraint is mild: most of the freedom of column 14 survives. The growth rates are twice the spectral radius of one
step of the fair coin on every phase, in floating point (`coin_lock.period_rate`): a power iteration of the step plus
the identity, whose vector then bounds the radius from above by the largest ratio of its image to itself (Collatz and
Wielandt), so each entropy in the table is an upper bound. A power iteration of the step alone can oscillate between
eigenvalues of one modulus, as it does for $0000000001$. The Lean modules prove only the sequences.

## Reproduce

```bash
python -m computations.locks --profile --workers 3
```

The survey of periods 4, 8, 10, 11 and 12 takes about 3 minutes with three processes, and the profile about 2 more;
the comparison with the simulation uses the output of `python -m computations.right_half 12000 30 --min-period 4
--max-period 12` ([the locking finding](period-four-locking.md#reproduce));
`--periods 2,3,5,6,7,9` gives the periods with no steerable block. `--lean` prints the entries of the Lean modules.
At 16 cells:

```bash
python -m computations.locks --periods 10,11,12,13,14,15 --width 16 --workers 4
python -m computations.locks --periods 10,11,12,13,14,15 --census 16 --workers 4
python -m computations.locks --reach 0000010111001,000001010110101,001001111010111 --width 18
```

The first two take several hours each; the last shows that the white window of each of the three reaches no lock at 18
cells.
