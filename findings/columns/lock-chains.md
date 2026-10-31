---
title: Locks carried leftward from a few seeds give every locked window of 13 cells up to period 12, both of the kit's traps, and locked windows for a block of every period from 2 to 9
category: columns
problems: [1]
status: computed
formalization: partial
evidence: [computations/lock_chain.py, computations/locks.py, computations/absorption.py, computations/period_three.py]
---

# Locks carried leftward from a few seeds give every locked window of 13 cells up to period 12, both of the kit's traps, and locked windows for a block of every period from 2 to 9

Let column $m$ of a row repeat a block $s$, and let a locked window of $s$ fix column $m + 1$ at the white phases of
$s$. Then column $m - 1$ repeats a block that $s$ and those values determine, since by the rule
$c_{j-1}(\varphi) = c_j(\varphi + 1) \oplus (c_j(\varphi) \lor c_{j+1}(\varphi))$, and so does every column further
left. Call these blocks the chain of the lock. The block at distance $d$ in the chain has a locked window $d$ cells
wider than that of $s$: the $d$ columns of the chain, then the window of $s$. Its phase is counted modulo the period of
$s$, which a shorter period of the block divides. A locked window is a trap in the sense of the kit: a row that brings
a column repeating the block and the cells right of it into the window contradicts Jen's theorem on adjacent columns.

Read off [the finite game](../../Rule30Open/Columns/FiniteGame.md) and the kit's tables, the computation finds:

- every one of the 72 blocks of period at most 12 with a locked window of 13 cells is in the chain of one of seven
  seeds, and the three families of [window locks](../../negative-results/columns/window-locks.md) are one chain, that
  of $0\,1^{P-1}$, whose block of period 9 does not lock;
- the kit's two traps for words of the open periods are chains: its wall for period four is the lock of $0\,1^7$
  carried 8 columns, and its trap for $001$ is the lock of a block of period 21 with twelve 1s in a row carried 38
  columns;
- chains of seeds of period 12 to 20 give locked windows to blocks of period 5, 6, 7 and 9, which no window of up to
  20 cells has, and a second one to $001$; six of these locks are traps in Lean.

## Result

A window of a block is locked, as in [window locks](../../negative-results/columns/window-locks.md), when along every
continuation, whatever the cell beyond the window does, the column left of the repeating one reads one value at each
phase. A bottom component of a block's game is a strongly connected set of locked nodes that no move leaves.

1. **Seven seeds.** In each bottom component of the 72 blocks with a locked window of 13 cells, columns $1, \dots, d$
   are functions of the phase for some $d \ge 0$, and the chain of one of seven seeds holds the block and, $d$ columns
   nearer the seed, the block of column $d$. A seed is a block with a bottom component in which column 1 is not a
   function of the phase. The seven are:

   | seed | period | longest run of 1s | lock value at its white phases | blocks in its chain | distances |
   |---|---|---|---|---|---|
   | $0\,1^7$ | 8 | 7 | white | 8, every block of period 8 with a locked window | 0 to 7 |
   | $0\,1^9$ | 10 | 9 | white | 9, every block of period 10 with a locked window | 0 to 8 |
   | $0\,1^{10}$ | 11 | 10 | white | 11 | 0 to 10 |
   | $0\,1\,0\,1^8$ | 11 | 8 | white, white | 11 | 0 to 10 |
   | $0\,1^{11}$ | 12 | 11 | white | 15 | 0 to 14 |
   | $0\,1\,0\,1^9$ | 12 | 9 | white, white | 9 | 0 to 8 |
   | $0^7\,1\,0\,1^3$ | 12 | 3 | $0\,1\,1\,1\,1\,1\,1\,0$ | 8 | 0 to 7 |

   The 22 blocks of period 11 and 32 of period 12 split as the table shows. With the phase counted modulo 4, $0111$ is
   a seed of its own; with the phase counted modulo 8 it is the chain of $0\,1^7$ at distance 8 (item 4).
2. **The three families are one chain.** For every period $P$ from 8 to 40, the chain of $0\,1^{P-1}$, white at its
   white phase, reads at distances 0 to 7, up to rotation, $0\,1^{P-1}$, $0^{P-2}\,1\,1$, $0\,0\,1^{P-2}$,
   $0^{P-1}\,1$, $0\,0\,1^{P-4}\,0\,1$, $0^{P-5}\,1\,1\,1\,0\,1$, $0\,0\,0\,1^{P-3}$ and $0^{P-3}\,1\,0\,1$. The
   families $0^k\,1\,1\,1\,0\,1$, $0\,0\,1^k\,0\,1$ and $0^k\,1\,0\,1$ of window locks are its columns at distances 5,
   4 and 7. In every bottom component of their members with a locked window of 13 cells, at periods 8 and 10 to 17,
   columns 1 to 5, 1 to 4 and 1 to 7 are functions of the phase, the last of them repeats $0\,1^{P-1}$, and the chain
   from it gives the block; from period 15 the first two families have two more such columns, so their seed sits two
   columns further right and its chain passes through $0\,1^{P-1}$. Their members of period 9 are the chain of
   $0\,1^8$, so their three gaps at period 9 are one: $0\,1^8$ has no locked window of up to 20 cells, by the census
   of window locks.
3. **Why $0\,1^8$ does not lock.** A long run of 1s leaves the window beside the column in the wall, cells
   $2, 4, 6, \dots$ black. From there, over every continuation of a window of 11 cells, the white phase of
   $0\,1^{P-1}$ finds cell 1 at its following returns as follows:

   | $P$ | 4 | 5 | 6 | 7 | 8 | 9 | 10 to 14 |
   |---|---|---|---|---|---|---|---|
   | cell 1, periods 1 to 12 | white for 8, then both | black, white, black, white, black, then both | white for 3, then both | black, white, white, then both | white | white, black, then both | white |

   At period 9 the disturbance that the white phase sends into the wall meets the next white phase so that cell 1 is
   black one period later, for every continuation; an exact run from the wall does the same. Eight 1s are also one short
   of the nine after which [WallSets](../../Rule30Open/Columns/WallSets.md) knows the first cell from any window. At
   period 8 and from period 10 the white phase finds cell 1 white every time, and $0\,1^{P-1}$ has a locked window of 5
   cells; at periods 5, 6, 7 and 9 it has none up to 13 cells.
4. **The kit's wall is the lock of $0\,1^7$.** From distance 8 on, the chain of $0\,1^7$ is the kit's ether read
   leftward from a $B_3$ column: $0111$, $0011$, $0011$, $0001$, $0001$, $0011$, $01$, that is
   $B_3 B_2 B_1\, c\, c\, B_5 B_4$, with spatial period 7. The two bottom components of the game of $0111$ with the
   phase counted modulo 8, the block $01110111$, at width 13 are each exactly the kit's 109 wall states
   ([`Rule30Ether`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Ether.lean),
   `wallStates`), with the ether phase $p$ read as phase $p + 2$ of $0111$. So in every wall state, cells 1 to 8 right
   of the $B_3$ column are fixed by the phase modulo 8 and are the chain at distances 7 down to 0; cell 8 repeats
   $0\,1^7$; cells 9 to 13 lie in a locked window of $0\,1^7$ of 5 cells, the strip width of the kit's certificate
   `not_eventually_01111111`. Entering the kit's ether-and-wall family makes a column 8 cells beyond the last ether
   column repeat $0\,1^7$ from then on.
5. **The widths of the period-four locks.** With the phase counted modulo 8, the least width at which $0111$, $0011$,
   $0001$ and $01$ have a locked window is 13, 14, 16 and 19, each 5 more than the first distance at which the word
   appears in the chain of $0\,1^7$: 8, 9, 11 and 14. This matches the census of window locks: at width 13 only $0111$
   of the three words of period 4 has a locked window, at width 16 all three, and $01$ with the phase modulo 4 has one
   from width 19.
6. **The kit's trap for $001$ is a chain.** The kit's trap `t001`
   ([`Rule30EtherThreeTrap`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30EtherThreeTrap.lean))
   is 815 states of 47 columns with labels modulo 21. Its columns 1 to 38 are functions of the label, and column 38
   repeats a rotation of $0^5\,1\,0\,1^{12}\,0\,1$. Column 39 has one value at each white label of column 38, and the
   chain from column 38 with those values gives columns 37 down to 1 and then the center, $001$. The block of column 38
   has a locked window from 9 cells, the trap's last 9 columns.
7. **Locked windows for a block of every period from 2 to 9.** A chain can hold a column whose least period is a
   proper divisor of the seed's; that block then has a locked window with the phase counted modulo the seed's period.
   The scan took as seeds every block of period 10, 12, 14 and 15 with a locked window of 5 cells and every block of
   period 16, 18, 20 and 21 with one of 9 cells, and followed each chain to distance 3,000. At period 21 it finds the
   kit's `t001` again, $001$ at distance 38 of $0^5\,1\,0\,1^{12}\,0\,1$ (item 6). The shortest lock found for each
   block of period at most 9, each checked directly by the rule on whole windows:

   | block | period | seed | phase modulo | distance | width | states |
   |---|---|---|---|---|---|---|
   | $01$ | 2 | $0\,1^7$ | 8 | 14 | 19 | 109 |
   | $001$ | 3 | $0^4\,1\,0\,1^9$ | 15 | 47 | 52 | 153 |
   | $01111$ | 5 | $0^{10}\,1^{10}$ | 20 | 98 | 107 | 1,076 |
   | $001011$ | 6 | $0^3\,1^9$ | 12 | 24 | 29 | 116 |
   | $0011101$ | 7 | $0^4\,1^{10}$ | 14 | 30 | 35 | 126 |
   | $0000011$ | 7 | $0^3\,1^{11}$ | 14 | 38 | 43 | 130 |
   | $001011101$ | 9 | $0^5\,1\,1\,0\,0\,1^9$ | 18 | 21 | 30 | 1,410 |
   | $001011111$ | 9 | $0^3\,1\,1\,0\,0\,1\,0\,1^9$ | 18 | 38 | 47 | 1,692 |
   | $010110111$ | 9 | $0^3\,1\,0\,1\,1\,0\,1^{10}$ | 18 | 62 | 71 | 1,782 |
   | $000010001$ | 9 | $0^4\,1\,0\,1\,0\,1^{10}$ | 18 | 135 | 144 | 1,389 |
   | $000100101$ | 9 | $0^6\,1^9\,0\,1\,1$ | 18 | 162 | 171 | 1,384 |

   The first is the kit's family for $01$ (item 4). The others are new: the census of window locks found none for these
   blocks because it stopped at 16 and 18 cells and counted the phase modulo the period or a small multiple of it. Every
   seed but $0\,1^7$ has a run of at least nine 1s. The scan found columns of a shorter period of periods 2, 3, 5, 6, 7,
   8, 9 and 10, none of period 4, so no second wall for the ether of period four, and none holding $011$. Seeds with a
   run of at least nine 1s and at most 12 other cells, of periods 16 to 40 with a locked window of 5 cells, give no
   column of period 4 either, and 44 of them give the alternating word $01$, at distances 152 to 1,558
   (`--short 16,20,24,28,32,36,40 --width 5 --rest 12`). With these and the seeds of periods 15 to 24 with at most 15
   other cells and a locked window of 9 cells, seven seeds, of periods 15 and 21, reach $001$, which has four traps
   pairwise apart ([Traps001](../../Rule30Open/Columns/Traps001.md), `--scan001`), while the seeds of periods 36 to 48
   give no column of a shorter period within 3,000 columns, and those of periods 27 to 33 with a locked window of 9
   cells none of period 3 (`--scan001-wider`); the locks for a block of period 9 here count the phase modulo 18, and
   item 10 gives the wall of period 9 itself. [WordTraps](../../Rule30Open/Columns/WordTraps.md) checks in Lean the
   traps for $01$, $001$, $01111$, $001011$, $0011101$ and $001011101$.
8. **The kit's strip certificates.** The kit's strip-certificate table has 15 words of length 8 to 12 and its two rank
   certificates are for $0^6\,1\,1$ and $0^9\,1\,0\,1$; all 17 are in these chains, at distances 0 to 7: the distances
   0, 1, 2, 3 and 6 of the chains of $0\,1^{P-1}$, the seed $0\,1\,0\,1^{P-3}$, and $0^9\,1\,0\,1$ at distance 7 of the
   chain of $0\,1^{11}$.
9. **Where the chains go.** A chain repeats in the distance once two adjacent columns repeat. The chain of $0\,1^7$
   does so from distance 8 with period 7, every column of period 4 or 2: the ether. The other seeds' chains do so with
   long spatial periods (155 for $0\,1^9$, 275 for $0\,1^{10}$, 143 for $0\,1\,0\,1^8$, 138 for $0\,1^{11}$ and for
   $0^7\,1\,0\,1^3$, 60 for $0\,1\,0\,1^9$), mixing columns of the seed's period with columns of a divisor of it.

10. **A wall of period 9.** At 43 cells, with the phase counted modulo 9, the block $001011111$ is a seed. The closure
   of the window of a right half that it drives, at step 12,000, under both values of the cell beyond, is a lock of 233
   states with no column fixed by the phase (`natural_trap`); the half enters it at step 6,084. Its chain, from the
   lock's values at its white phases, white, black and white, holds 21 blocks of period 9 within distance 21, and from
   distance 10 repeats with spatial period 135 in a background of 13 blocks of period 9, the one that the chain of
   $0\,1^8$ enters from distance 8. So period 9 has an ether and a wall, as period four has, the wall 43 cells wide
   where the census of window locks stopped at 18. Run for 20,000 steps from 31 starts, six words of period 9 lock
   column 1 from one start each, and five of them, at distances 0, 1, 2, 5 and 16 of this chain, are then inside its
   traps (`natural_scan`). The sixth, $001010011$, locks with period 27 inside a second wall: the closure of its window
   is a trap from 41 cells on, with the phase counted modulo 27 and 5,710 states, and its chain holds columns of period
   27 only, periodic in the distance from distance 7,105 with spatial period 15,663, so no small background. Of the
   right halves with support in cells 1 to 8, from every phase, 247 of 2,304 enter the trap of $001011111$ within
   50,000 steps ([trap entry](../../negative-results/columns/trap-entry.md)).
   [NineTraps](../../Rule30Open/Columns/NineTraps.md) checks all 22 traps in Lean. Of the
   words of period 5, 6 and 7 only $01111$ locks column 1, from 2 of the 31 starts, and both locks break near step
   20,500, so neither half is in a trap.

## What it means

The locks that the finite game finds are a few seeds, each a lock with no column fixed by the phase, carried leftward
through columns that the rule determines, and both of the kit's traps for words of the open periods are built the same
way, from seeds with a run of at least seven 1s. So the question of [window
locks](../../negative-results/columns/window-locks.md), why no window locks at periods 2, 3, 5, 6, 7 and 9, is a
question about seeds; for the three families it is the single fact that $0\,1^8$ does not lock, and item 3 shows how it
fails. The gap is one of width: with wider windows and the phase counted modulo a multiple of the period, a block of
every period from 2 to 9 locks (item 7), and period 9 has a wall of its own at 43 cells that driven right halves
enter (item 10).

Each lock of item 7 is a trap in the kit's sense, so the route the kit takes for period three and four, a trap and the
statement that every finite right half enters it, now reaches one block of each period 5, 6, 7 and 9, with a second
trap for $001$ and one for $01$; [WordTraps](../../Rule30Open/Columns/WordTraps.md) proves the reductions in Lean.
Entry stays as hard as the kit's `Absorption`, and each trap reduces one block, not its period: most blocks of these
periods have no trap found. The kit has no trap for $011$, and none of these chains holds it. For least period four,
the kit proves that the pure ether lies in no trap of width at most 20
([`Rule30EtherTrapWidth20`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30EtherTrapWidth20.lean));
in the terms here, the ether has one wall because one seed's chain, that of $0\,1^7$, enters it, and the scan found no
other seed whose chain holds a word of period 4. This is a picture of where the known traps come from, not a proof that
there are no others.

## Formalization

[WordTraps](../../Rule30Open/Columns/WordTraps.md) proves six locks of item 7 in Lean as traps, by a check the kernel
evaluates on tables that `lean_trap` writes, so the computation that found them is not trusted. Still wanted: the
reading of the kit's wall in item 4, that in each wall state cells 1 to 8 are the chain columns at the state's phase
modulo 8 and the wall's moves keep that phase, which are finite checks as well.

## Reproduce

```bash
python -m computations.lock_chain --classify 4,8,10,11,12 --width 13 --workers 3   # items 1 and 8, about 2 min
python -m computations.lock_chain --chain 8,9,10,11,12,13 --depth 12   # item 2, 15 s
python -m computations.lock_chain --wall 4,5,6,7,8,9,10,11,12,13,14 --width 11   # item 3, 1 s
python -m computations.lock_chain --ether   # items 4 and 5, about 1 min
python -m computations.lock_chain --t001 --verify   # items 6 and 7, about 1 min
python -m computations.lock_chain --short 10,12,14,15 --width 5 --depth 3000 --workers 4   # item 7, about 3 min
python -m computations.lock_chain --short 16,18,20,21 --width 9 --depth 3000 --workers 4   # item 7, about 40 min
python -m computations.lock_chain --natural 2,3,5,6,7,9 --steps 20000   # item 10, about 5 min
python -m computations.lock_chain --nine --steps 20000   # item 10, entry into each trap of period 9, about 5 min
```

`tests/test_computations.py::test_lock_chain` checks `left_column` against a step of the rule, the chain of
$0\,1^9$ against the bottom components of the three families at period 10, the eight blocks of period 8, the ether,
the wall and the trap `t001` against the kit's tables read from its source, the wall returns against an exact run
from the wall, and `is_lock` against `locks.lock_info` and on the locks of $001$ and $001011$. The periods 8 to 40 of
item 2, the spatial periods of item 9 and the kit words of item 8 come from `chain`, `chain_cycle` and
`game.KIT_WORDS` in the same module.
