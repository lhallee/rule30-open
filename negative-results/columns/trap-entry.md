---
title: Right halves driven by blocks of period 5, 6 and 7 almost never enter a trap
category: columns
problems: [1]
status: negative
kind: no-signal
evidence: [computations/lock_chain.py, computations/right_half.py]
---

# Right halves driven by blocks of period 5, 6 and 7 almost never enter a trap

**Question.** [WordTraps](../../Rule30Open/Columns/WordTraps.md) proves traps in Lean for $01111$, $001011$ and
$0011101$, the first for blocks of period 5, 6 and 7, and one for $001011101$ of period 9 with the phase counted modulo
18: once a column repeating the block has one of the trap's windows beside it, Jen's theorem on adjacent columns is
contradicted. Each reduces its block to entry, the statement that every finitely supported right half driven by the
block enters the trap, as the kit reduces $001$ to entry into `t001` and the words of period four to entry into its
ether-and-wall family. For those, computation supports entry: every right half of up to 20 cells enters the period-four
family within 1,959 steps ([the absorption census](../../findings/columns/absorption-census.md)), and every half of up
to ten cells enters `t001`, a median of about 16,000 steps in ([the census for
001](../../findings/columns/t001-census.md)). Some small halves enter the two walls of period 9 of
[NineTraps](../../Rule30Open/Columns/NineTraps.md). Do right halves driven by the new blocks enter their traps, or any
trap?

**What was done.** Three tests, all in [computations/lock_chain.py](../../computations/lock_chain.py).

- *Entry into the Lean traps* (`entry_steps`). Every right half with support in cells 1 to 8, driven by the block from
  each of its phases, is stepped for 50,000 steps, and the first step at which its first cells are a state of the trap
  at the block's phase is recorded. The trap is closed, so a half that enters stays.
- *Any trap* (`natural_scan`). The empty right half and 30 random halves of 64 cells (`right_half.random_starts`) are
  driven by every primitive word of period 2, 3, 5, 6, 7 and 9 for 20,000 steps. A half inside any trap has column 1
  periodic at the word's white times, so the scan first asks whether it is, over the second half of the run
  (`right_half.locked_period`). For each half that passes, it closes the true window at steps 12,000, 16,000
  and 19,999 under both values of the cell beyond (`closure`), at each width from 16 to 64 and with the phase counted
  modulo the lock's period or twice it, and returns the least width at which the closure has at most 100,000 states and
  fixes column 1 at the white phases (`natural_trap`). A trap at one width gives one at every larger width, the windows
  that extend its states, so the least width is the one to search for; at larger widths the closure grows. This is how
  the kit built `t001`, and the scan rebuilds it: for $001$, six of the 31 halves lock, and at step 12,000 each is
  inside `t001` itself, 815 states of 47 cells modulo 21 (`test_natural_trap` checks this for the empty half).
- *A coin beyond the window* (`coin_entry`). The small halves of the first test are run by the rule for 200 steps;
  from then on only their first cells, as many as the trap is wide, are kept, and the cell beyond them is a fair coin
  flipped at every step, for 50,000 steps more. This asks whether entry is rare because a trap is hard to reach from
  the window whatever lies beyond, or because the rule's own right half avoids it. Every trap but `trap01111`, which
  is wider than the 63 cells the test handles, is run this way.

**Outcome.**

*Entry into the Lean traps*, over the right halves with support in cells 1 to 8, from every phase:

| trap | block | period, phase modulo | halves and phases | entered by step 50,000 | when | with a coin beyond, from step 200 |
|---|---|---|---|---|---|---|
| `trap01` | $01$ | 2, 8 | 512 | 15 | all by step 10 | 15, all inside at step 200 |
| `trap001fifteen` | $001$ | 3, 15 | 768 | 0 | | 0 |
| `trap01111` | $01111$ | 5, 20 | 1,280 | 0 | | not run |
| `trap001011` | $001011$ | 6, 12 | 1,536 | 10 | all by step 20 | 10, all inside at step 200 |
| `trap0011101` | $0011101$ | 7, 14 | 1,792 | 10 | steps 8,856 to 8,859 | 6, median 34,972 |
| `trap001011101` | $001011101$ | 9, 18 | 2,304 | 16 | steps 42,751 to 46,470 | 30, median 28,710 |
| `trap001011111` | $001011111$ | 9, 9 | 2,304 | 247 | median 17,403, latest 49,425 | 187, median 22,657 |
| `trap001010011` | $001010011$ | 9, 27 | 2,304 | 167 | median 33,653, latest 49,797 | 147, median 26,691 |

With a coin in place of the cells beyond the window, entry is about as rare, or as common, as with the rule's own right
half: the traps of periods 2, 3, 6 and 7 are entered only by the halves already inside, or by a few, and the walls of
period 9 by a similar share of the halves, within a factor of two. So the rarity of entry at periods 5, 6 and 7 is a
property of the traps found there, which are hard to reach from the windows that the rule makes beside the column
whatever arrives from the right, and not a sign that the rule's right half avoids them.

The entries by step 20 are halves that start next to the trap. The ten into the trap of $0011101$ come from four phases
and distinct halves but land within four steps of each other, as one late event would. The white right half, which the
census includes, enters none of these traps within 50,000 steps. Run for 1,000,000 steps it enters both walls of period
9 from most phases, but late: `trap001011111` at step 119,947 from phase 2, and so from phases 0 and 1, where the center
reads white first, one and two steps later, and at step 201,129 from phase 8, but not from phases 3 to 7, whose runs
agree on columns 1 to 2,000 from step 2,100 on, so that they are one run (`white_runs`); `trap001010011` at steps
91,086, 169,098 and 659,740 from phases 7, 2 and 4, and so from every phase but 8. Small halves go on entering both
walls at a steady rate over longer runs: of 100 pairs of a half and a phase drawn from the census, 66 enter the first by
step 500,000 and 49 the second (`--sample`).

*Any trap.* Column 1 locks for none of the 31 halves driven by any word of period 2, 5, 6 or 7, nor by $011$, except
$01111$, for 2 halves, whose locks break near step 20,500, so that neither half is in a trap. For $001$ it locks for 6,
each inside `t001`. At period 9 six words lock for one half each, and each half is then inside a trap: five inside the
traps of the wall of [NineTraps](../../Rule30Open/Columns/NineTraps.md), and the half driven by $001010011$ inside a
second wall, of 41 cells with the phase counted modulo 27.

*Any trap, 301 halves.* With the empty half and 300 random ones the picture holds. Under the words of period 6 and 7,
$011$, and the words of period 5 but $01111$, column 1 locks for none of the 301 halves. Under $01111$ it locks for 37,
and every one of these locks breaks again between steps 20,000 and 60,000, so that none of these halves is in a trap.
Under $01$ it locks for 12, each inside a trap: 6 inside the kit's family, 109 states of 19 cells with the phase
modulo 4, and 6 inside a second trap, `trap01fourteen`, 225 states of 31 cells modulo 14, which is the lock of 6 cells
of the block $0^4\,1\,0\,1^8$ of period 14 carried 25 columns (`test_period_two_fourteen`). The kit's open pull
request #39 states that for the white right half the black values of the gate, column 1 at the white times, recur and
never come two gate steps apart; in this trap two do, so if that holds the white half never enters it, and by
computation it stays out for 200,000 steps from both phases. Under $001$ column 1 locks for 107 of the 301 halves, each
inside `t001`. At period 9 it locks for 67 of the 16,856 pairs of a word and a half, under 12 words, and every one of
these halves is inside a trap; no word outside the 22 that [NineTraps](../../Rule30Open/Columns/NineTraps.md) covers
locks for any half:

| word | halves that lock, of 301 | the trap they are in | in the chain of the first wall |
|---|---|---|---|
| $001011111$ | 5 | 43 cells, phase modulo 9, 233 states | distance 0 |
| $000010011$ | 10 | 44 cells, modulo 9, 233 states | distance 1 |
| $010101111$ | 8 | 45 cells, modulo 9, 233 states | distance 2 |
| $000011111$ | 9 | 46 cells, modulo 9, 233 states | distance 3 |
| $000001011$ | 5 | 47 cells, modulo 9, 233 states | distance 4 |
| $010111011$ | 5 | 48 cells, modulo 9, 233 states | distance 5 |
| $001101011$ | 5 | 49 cells, modulo 9, 233 states | distance 6 |
| $001011011$ | 1 | 50 cells, modulo 9, 233 states | distance 7 |
| $001010101$ | 4 | 52 cells, modulo 9, 233 states | distance 9 |
| $000110011$ | 4 | 39 cells, modulo 27, 865 states | distance 11, a trap of 54 cells |
| $000101011$ | 8 | 59 cells, modulo 9, 233 states | distance 16 |
| $001010011$ | 3 | 41 cells, modulo 27, 5,710 states: the second wall | no |

So every block between the first wall and its background locks for some halves, but only 3 of the 13 blocks of the
background do. The halves under $000110011$ are not in the first wall's trap of 54 cells but in a narrower one, the
lock of a block of period 27 with thirteen 1s in a row carried 31 columns, like the second wall a lock with the phase
counted modulo 27.

**What it means.** The traps of [lock chains](../../findings/columns/lock-chains.md) show that what keeps windows of up
to 18 cells from locking at periods 5, 6 and 7 is not the absence of a trap: wider ones exist for a block of each
period. The obstruction is dynamical. Driven by these blocks, the right half next to the center almost never settles:
column 1 repeats at the white times for none of the 301 halves under the words of period 6 and 7, and under $01111$ only
for a while, and the small halves enter the Lean traps only from next to them or in one late event, so for these blocks
the reduction to entry has almost no computational support; its hypothesis may well be false. Period 9 shows that this
is not a matter of the period alone: there two walls exist that about one small half in nine and one in fourteen enter
within 50,000 steps, with entries still coming at the end, as under $001$. The runs cover only small halves and 50,000
steps: entry later, or by larger halves, is not excluded, and `t001` shows that entry can take $10^5$ steps.

**Reproduce.**

```bash
python -m computations.lock_chain --entry trap01,trap001fifteen,trap01111,trap001011,trap0011101,trap001011101 --cells 8 --steps 50000
python -m computations.lock_chain --entry trap001011111,trap001010011 --cells 8 --steps 50000
python -m computations.lock_chain --natural 2,3,5,6,7,9 --steps 20000
python -m computations.lock_chain --natural 2,3,5,6,7,9 --steps 20000 --starts 300 --workers 3
python -m computations.lock_chain --entry trap01fourteen --cells 0 --steps 200000
python -m computations.lock_chain --entry trap001011111,trap001010011 --cells 0 --steps 1000000
python -m computations.lock_chain --runs 001011111,001010011 --steps 2100 --cells 2000
python -m computations.lock_chain --entry trap001011111,trap001010011 --cells 8 --steps 500000 --sample 100
python -m computations.lock_chain --coin trap01,trap001fifteen,trap001011,trap0011101,trap001011101,trap001011111,trap001010011 --cells 8 --steps 50000
```

The first takes about 40 minutes with one process per trap, the second about 15 per trap, the third about 3, the fourth
about 50 with three processes, most of it for $001$, the fifth under a minute, the sixth about 18, the seventh a few
seconds, the eighth about 15 per trap and the ninth about 25.
