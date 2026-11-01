---
title: Beside a center that repeats a block, column 1 falls into a set of words of low entropy, from every state for 15 blocks of period 3 to 7
category: columns
problems: [1]
status: computed
formalization: partial
evidence: [computations/gap_traps.py]
---

# Beside a center that repeats a block, column 1 falls into a set of words of low entropy, from every state for 15 blocks of period 3 to 7

Let the center column repeat a block $b$ from some step on, and read column 1 at the white steps of $b$, the steps at
which the center is white. These readings are what the right half tells the left half: at a white step the next center
cell is column $-1$ xor column 1, so column $-1$ at a white step is the reading xor the next cell of the block (and
at a black step it is the complement of the next cell of the block). Masked Jen needs the readings eventually
periodic, and for most blocks they never are. They are, however, constrained:

- For **15 blocks of period 3 to 7**, among them $001$, every right half, finite or not, has readings that avoid a fixed
  finite list of words from step 12 to 63 on (by block), whatever its cells beyond column 14 hold. The constrained
  readings carry 0.135 to 0.586 bits per reading in place of 1.
- For **8 more blocks**, among them $011$, every right half of up to 10 cells enters a closed set of windows on which
  the readings avoid such a list, within 37 to 792 steps; for $011$ every right half of up to 16 cells does, within 104
  steps. For these the entry is not forced: some inputs from beyond column 14 keep a window out forever. A shorter
  list is forced for seven of them, and for $011$ forbidding two adjacent white readings is forced up to readings that
  stay white.

Each block of the first kind therefore reduces, with no hypothesis on the right half, to a statement about the left
half alone with constrained free bits: no finite left half keeps column $-1$ equal to the block's pattern with its free
bits in the constrained set. That is a weaker statement than the kit's left-only reductions (`C3s001` for $001$, `C3w`
for $011$ and the kit's `C3` for period four), which leave the free bits arbitrary.

## The construction

A state is a phase of the block, a window of columns 1 to $W$, and the last $L - 1$ readings. One step of the rule
moves the window with the center known and column $W + 1$ unknown, so it has two successors. For a list of forbidden
words of length at most $L$:

1. **The trap** (`greatest_trap`): the greatest set of states that one step keeps, for both values of column $W + 1$,
   without a reading completing a forbidden word. Once the true state of a right half (its window and its true last
   readings) is in it, its readings avoid the words forever, whatever the cells beyond column $W$ do.
2. **Forced entry** (`forced_layers`): the states from which every sequence of values of column $W + 1$ leads into the
   trap, and how many steps the slowest sequence takes. When this is every state, every right half enters within that
   many steps, finite or infinite, from any start.
3. **The words** (`forbidden_words`): the minimal words of at most 8 readings that no sampled driven half shows after
   a transient (every half of up to 6 cells and 40 random halves of 40 cells, from every phase, 6,000 steps).
4. **The entropy** (`word_entropy`): the topological entropy of the sequences that avoid the words, from the graph on
   the last $L - 1$ readings.

## Results at width 14

Every primitive block of period 2 to 7 with at least one 0 and one 1, 39 in all, was tried with its learned words.
The trap is empty for 15 of them: $01$, $0001$, $0111$, $01111$, $001011$, $011111$ and nine of period 7. For those the
sampled halves settle into different closed sets (locks, the kit's ether family for $01$ and $0001$, several traps of
the block), and one list of words does not fit them all; [the period-two census](../period-two/gate-census.md) handles
$01$ that way. For $0011$ every reading pattern but one periodic one is forbidden and about 58% of the halves enter.
The other 23 blocks:

| block | words (longest) | entropy | entry forced within | otherwise: halves of up to 10 cells enter by |
|---|---:|---:|---:|---:|
| $001$ | 7 (8) | 0.356 | 46 steps |  |
| $011$ | 4 (6) | 0.442 | no | 91 |
| $00001$ | 16 (8) | 0.421 | 16 steps |  |
| $00011$ | 6 (8) | 0.335 | 19 steps |  |
| $00101$ | 15 (8) | 0.586 | 12 steps |  |
| $00111$ | 8 (8) | 0.347 | no | 57 |
| $01011$ | 10 (8) | 0.581 | no | 37 |
| $000001$ | 23 (8) | 0.278 | no | 47 |
| $000011$ | 6 (8) | 0.357 | 14 steps |  |
| $000101$ | 21 (8) | 0.471 | 19 steps |  |
| $000111$ | 14 (8) | 0.448 | 29 steps |  |
| $001101$ | 15 (8) | 0.518 | 25 steps |  |
| $001111$ | 5 (7) | 0.406 | no | 155 |
| $010111$ | 6 (8) | 0.449 | no | 155 |
| $0000001$ | 12 (8) | 0.135 | 38 steps |  |
| $0000011$ | 7 (8) | 0.301 | 24 steps |  |
| $0000101$ | 22 (8) | 0.492 | 26 steps |  |
| $0001001$ | 21 (8) | 0.309 | 63 steps |  |
| $0001011$ | 15 (8) | 0.346 | 39 steps |  |
| $0001111$ | 5 (8) | 0.415 | 26 steps |  |
| $0011011$ | 5 (8) | 0.399 | no | 792 |
| $0011111$ | 5 (8) | 0.432 | no | 169 |
| $0110111$ | 14 (8) | 0.559 | 30 steps |  |

"Entry forced" is a statement about every state of width 14, so about every right half, finite or not. The census
column is about right halves of up to 10 cells, all phases, within 4,000 steps.

For the eight blocks without forced entry, a shorter list taken from the learned words is forced (`escape_readings`
and `forced_layers`, by `--words ... --forced`):

| block | forced words | entropy | within |
|---|---|---:|---:|
| $00111$ | $111$, $0000$, $1011$ | 0.694 | 22 steps |
| $01011$ | $111$, $1011$, $1100$ | 0.743 | 13 steps |
| $000001$ | $1010$ | 0.913 | 4 steps |
| $001111$ | $00$, $0110$ | 0.597 | 18 steps |
| $010111$ | $11$ | 0.694 | 4 steps |
| $0011011$ | $00$ | 0.694 | 32 steps |
| $011$ | $00$, unless every later reading is white | 0.694 | (below) |

For $011$ the list $00$ is not entered from 28 of the 98,304 states of width 14, and every input sequence that keeps a
state out reads white at every later white step, so its readings are eventually constant, which masked Jen excludes.
For $011$ one word is forced with no exception: read at its white step, column 1 never has a run of exactly four 1s
($011110$, forced at width 7 within 15 steps, entropy 0.976; `reading_certificates.py --block 011 --phases 0 --width 7
--words 011110`), a weak companion to the conditional list $00$. For $0011111$ none of the lists tried ($11$; $11, 1001$; all five learned words) is forced, and the paths that stay out
read both colors. So 22 of the 23 blocks have a set of words of entropy below 1 that every right half falls into, or
that only halves with constant readings escape.

## Two examples

- **$001$.** Write the white steps as $a_i, b_i$ (the center reads $0, 0, 1$). The kit proves that column 1 is
  eventually white at every $a_i$ (`Rule30EtherThreeSkeleton.skeleton_001`) and reports that its strip certificates
  force nothing more up to width 13. On the words of the readings more is forced: at width 14 the seven learned words
  are avoided from every state after at most 46 steps, and with $a_i$ white this says that the readings $b_i$ have no
  run of 1s of length 1 and no run of 0s of length 1 or 2 (the words $00100$, $10001$ and $1000001$ read at the
  $b_i$). Already at width 13 the four words $11$, $1001$, $00100$ and $10001$ are avoided from every state after at
  most 30 steps, which excludes the runs of length 1 (`--block 001 --width 13 --words 11 1001 00100 10001 --forced`).
  Sampled halves show more: runs of 1s of length 2 or 4 and runs of 0s of length 3 to 5,
  which is not forced. With the kit's `col_m1_001_skeleton`, column $-1$ is eventually (white, the complement of $b_i$,
  black), so `C3s001` only has to rule out free bits whose runs of 0s have length at least 2 and runs of 1s at least
  3.
- **$011$.** The center reads $0, 1, 1$, one white step per period. The readings never have two zeros 1, 2, 4 or 5
  apart in the trap (the words $00$, $010$, $01110$, $011110$, entropy 0.442 bits), and sampled halves show zero gaps of
  3, 6 to 10 and 12 to 15 only, a stricter list that is not tested here. [The word
  011](../../negative-results/columns/period-three-011.md) found no periodic trap for $011$; this is a trap of another
  kind, on words, which every half of up to 16 cells enters within 104 steps. Entry is not forced at width 14 or 16: an
  input from beyond the window can hold the readings to blocks $01$ and $011$, which have zeros 2 apart.

## What it means

For many blocks the right half's channel into the center is narrow but never shut: the readings keep a positive
entropy, which is why no lock and no periodic trap appears for them, and why masked Jen alone cannot finish. The
reduction moves the whole difficulty to the left half, as the kit's left-only statements do, with less to rule out. A
left statement with constrained free bits is still of the kind of the problem (a finite left half has to fail to
produce a sequence from an uncountable set of positive entropy), so this narrows the problem and does not close it.
The forced cases are finite computations of a few million states each and can be checked by a kernel. For $001$ the
kernel checks one: [ThreeRuns](../../Rule30Open/Columns/ThreeRuns.md) proves that column 1 at the second white step
avoids $010$, $101$ and $1001$ from the 14th reading on, for every right half. For $00001$ the kernel checks another:
[Runs00001](../../Rule30Open/Columns/Runs00001.md) proves that column 1 at the first white step avoids $11$ and $1001$
from reading 5 on (readings counted from 0), for every right half. Each further block is one entry of
`computations/reading_modules.py`, which writes the module from the certificate of
`computations/reading_certificates.py`. [ReadingWords](../../Rule30Open/Columns/ReadingWords.md) kernel-checks a list read at one white step for
15 more blocks of period 5 to 7 (entropy 0.465 to 0.831). None of these lists excludes a block: each keeps positive
entropy, so masked Jen does not apply. [ConstrainedLeft001](../../Rule30Open/Columns/ConstrainedLeft001.md)
reduces $001$ in Lean to the left statement with those free bits, and [the constrained left
halves](../../negative-results/columns/constrained-left-halves.md) shows why no finite left game closes it: halves with
periodic free bits are eventually periodic in space and dense among the solutions.

## Reproduce

```bash
python -m computations.gap_traps --survey 7 --width 14 --cells 10   # the 39 blocks, about 10 min
python -m computations.gap_traps --block 001 --width 14 --forced   # forced within 46 steps
python -m computations.gap_traps --block 001 --width 13 --words 11 1001 00100 10001 --forced   # within 30 steps
python -m computations.gap_traps --block 011 --width 16 --words 00 010 01110 011110 --cells 16   # every half enters
python -m computations.gap_traps --block 011 --width 14 --words 00 --forced   # escaping paths read only white
python -m computations.gap_traps --block 00111 --width 14 --words 111 0000 1011 --forced   # forced within 22 steps
```

The forced column of the table comes from `--block <b> --width 14 --forced` for each block, a few seconds to about a
minute each. `tests/test_gap_traps.py` checks the window step against a cell-by-cell step, the trap and the forced
states against naive fixed points on states of width 6, the learned words of $011$ and a direct run of a random half,
and the entropy against the golden-mean shift and against counts of words.
