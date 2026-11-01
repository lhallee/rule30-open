---
title: Reading lists of entropy 0 fail at up to 16 cells for every block of period 3 to 9 that the game does not exclude, and for 720 of 744 up to period 12
category: columns
problems: [1]
status: negative
kind: barrier
evidence: [computations/zero_entropy.py, computations/game.py]
---

# Reading lists of entropy 0 fail at up to 16 cells for every block of period 3 to 9 that the game does not exclude, and for 720 of 744 up to period 12

**Idea.** Let the center repeat a block $b$ and read column 1 at every white step of $b$ (the readings of
[reading constraints](../../findings/columns/reading-constraints.md)). If a list of forbidden words is forced (every
right half, finite or not, avoids it from some step on) and the shift of finite type it defines has entropy 0, then
every reading sequence is eventually periodic: in a shift of finite type of entropy 0 every strongly connected component
of the de Bruijn graph is one cycle, so a sequence passes through finitely many components and ends on one cycle. With
the center eventually periodic, masked Jen ([AdjacentColumns](../../Rule30Open/Columns/AdjacentColumns.md), the kit's
`Rule30MaskedJen`) then excludes $b$ for every right half. The lists known so far have entropy 0.116 to 0.65 bits per
reading. The search here asked for lists of entropy exactly 0, in particular for a block of period 3, 5, 6, 7 or 9.

**Outcome.** Such a list exists at a width $W$ only where [the finite game](../../Rule30Open/Columns/FiniteGame.md),
with cyclic classes in place of phases, already excludes the block at $W$; at widths up to 16 and 18 that test closes
24 of the 744 primitive blocks of period 3 to 12 with both colors: of periods 3 to 9 only the three of period 8 that
the game itself excludes ($00000001$, $00000011$ and $01111111$).

- **A forced list at width $W$ is bounded below by the window graph.** The graph of windows of columns 1 to $W$ with a
  free column $W + 1$ (the game's graph) has, in each strongly connected component $C$ with a move inside it, the
  closed walks a play can repeat forever. If a list is forced at width $W$, a play that repeats closed walks of $C$
  enters the list's good set and then reads only allowed words, so the list's shift contains the readings of every
  concatenation of closed walks of $C$ through one node. If such walks read words $u_1, \dots, u_m$ that form a code
  (every concatenation factors one way; the Sardinas and Patterson test), every list forced at width $W$ has entropy at
  least $\log_2 x$ with $\sum_i x^{-|u_i|} = 1$, in bits per reading. This holds for lists tagged by the read position
  and for the variant in which the readings at some phases are a fixed periodic sequence: both are lists of tagged
  words.
- **Entropy 0 is the cyclic-class test.** The readings of all closed walks through one node of $C$ are powers of a
  single word exactly when the reading is a function of the cyclic class of $C$ (its level modulo the gcd of its cycle
  lengths, `game.component_periods`): every closed walk through the node is, in the free group, a product of the walks
  that go out along a shortest-path tree, take one move and return along another, and the readings of those are
  compared with powers of one word. So a list of entropy 0 forced at width $W$ needs the class test to pass at $W$, and
  where it passes every play is eventually periodic in its readings, so masked Jen excludes the block with no list at
  all. Dropping column $W + 1$ maps closed walks at width $W + 1$ to closed walks at width $W$ with the same readings,
  so a code at width 16 bounds every list forced at a width up to 16.
- **At widths 16 and 18 the class test closes 24 blocks.** They are the 22 that the game excludes (3 of period 8, 3 of
  10, 7 of 11, 9 of 12), $0^9 1$, which the kit excludes as a padded word, and $000000001011$, which nothing else
  excludes: [the game with cyclic classes](../../findings/columns/class-game.md). For each of the other 720 the
  largest component whose readings mix in a class gives a code of closed walks, each walk replayed cell by cell
  (`naive_walk`) to return to its start with the stated readings, and its first word has 4 to 81 readings:

| period | blocks | closed by the game | closed by classes only | open, with a code at width 16 | bound, least | upper median | largest |
|---|---:|---:|---:|---:|---:|---:|---:|
| 3 | 2 | 0 | 0 | 2 | 0.037 | 0.071 | 0.071 |
| 4 | 3 | 0 | 0 | 3 | 0.050 | 0.051 | 0.072 |
| 5 | 6 | 0 | 0 | 6 | 0.032 | 0.063 | 0.212 |
| 6 | 9 | 0 | 0 | 9 | 0.024 | 0.052 | 0.177 |
| 7 | 18 | 0 | 0 | 18 | 0.021 | 0.061 | 0.252 |
| 8 | 30 | 3 | 0 | 27 | 0.023 | 0.051 | 0.087 |
| 9 | 56 | 0 | 0 | 56 | 0.014 | 0.050 | 0.334 |
| 10 | 99 | 3 | 1 | 95 | 0.021 | 0.051 | 0.158 |
| 11 | 186 | 7 | 0 | 179 | 0.021 | 0.047 | 0.179 |
| 12 | 335 | 9 | 1 | 325 | 0.018 | 0.049 | 0.162 |

  The bound is in bits per reading for every list forced at a width up to 16. It is small because the walks of the
  code are long, not because the readings are close to periodic. At width 18 the class test closes the same 24 blocks.
- **The search finds positive entropy everywhere.** For the 35 blocks of period 3, 5, 6 and 7, the minimal words of up
  to 10 readings that sampled halves avoid (every half of up to 6 cells and 24 random halves of 40 cells, from every
  phase, 3,000 steps), tagged by their read position, were added greedily in two to four orders, and for pools of at
  most 8 to 12 words in every subset, while entry stays forced within 4 million states (the first four blocks) or 1.5
  million. No forced list has entropy 0. The least entropy this search reached, above the bound in every row (lists
  found elsewhere can be lower: [reading constraints](../../findings/columns/reading-constraints.md) has 0.135 for
  $0000001$):

| block | width | words | least forced entropy | entry within | bound at width 16 | sampled growth |
|---|---:|---:|---:|---:|---:|---:|
| $001$ | 14 | 4 | 0.306 | 46 steps | 0.037 | 0.137 |
| $011$ | 15 | 1 | 0.976 | 15 steps | 0.071 | 0.328 |
| $00001$ | 11 | 12 | 0.291 | 16 steps | 0.051 | 0.202 |
| $00011$ | 16 | 3 | 0.231 | 10 steps | 0.044 | 0.216 |
| $00101$ | 9 | 21 | 0.366 | 15 steps | 0.032 | 0.232 |
| $00111$ | 13 | 5 | 0.406 | 24 steps | 0.097 | 0.276 |
| $01011$ | 9 | 12 | 0.494 | 25 steps | 0.063 | 0.291 |
| $01111$ | 12 | 6 | 0.870 | 39 steps | 0.212 | 0.325 |
| $000001$ | 9 | 14 | 0.308 | 17 steps | 0.024 | 0.158 |
| $000011$ | 9 | 4 | 0.203 | 12 steps | 0.031 | 0.183 |
| $000101$ | 9 | 17 | 0.351 | 19 steps | 0.047 | 0.229 |
| $000111$ | 9 | 11 | 0.387 | 31 steps | 0.035 | 0.265 |
| $001011$ | 8 | 6 | 0.397 | 18 steps | 0.054 | 0.151 |
| $001101$ | 8 | 13 | 0.413 | 25 steps | 0.052 | 0.255 |
| $001111$ | 11 | 2 | 0.450 | 21 steps | 0.083 | 0.278 |
| $010111$ | 11 | 2 | 0.977 | 22 steps | 0.077 | 0.331 |
| $011111$ | 15 | 2 | 0.551 | 15 steps | 0.177 | 0.410 |
| $0000001$ | 16 | 5 | 0.264 | 33 steps | 0.041 | 0.107 |
| $0000011$ | 12 | 5 | 0.139 | 13 steps | 0.021 | 0.158 |
| $0000101$ | 8 | 21 | 0.310 | 15 steps | 0.045 | 0.210 |
| $0000111$ | 9 | 10 | 0.361 | 21 steps | 0.061 | 0.206 |
| $0001001$ | 11 | 13 | 0.360 | 34 steps | 0.038 | 0.153 |
| $0001011$ | 8 | 8 | 0.364 | 25 steps | 0.037 | 0.150 |
| $0001101$ | 9 | 17 | 0.406 | 22 steps | 0.034 | 0.243 |
| $0001111$ | 16 | 2 | 0.322 | 16 steps | 0.085 | 0.232 |
| $0010011$ | 9 | 11 | 0.484 | 17 steps | 0.050 | 0.235 |
| $0010101$ | 8 | 25 | 0.378 | 19 steps | 0.067 | 0.240 |
| $0010111$ | 8 | 6 | 0.416 | 22 steps | 0.080 | 0.266 |
| $0011011$ | 12 | 3 | 0.500 | 32 steps | 0.071 | 0.198 |
| $0011101$ | 9 | 12 | 0.450 | 27 steps | 0.048 | 0.265 |
| $0011111$ | 13 | 1 | 0.977 | 24 steps | 0.077 | 0.331 |
| $0101011$ | 11 | 12 | 0.446 | 39 steps | 0.042 | 0.203 |
| $0101111$ | 8 | 7 | 0.445 | 33 steps | 0.076 | 0.234 |
| $0110111$ | 10 | 13 | 0.519 | 35 steps | 0.098 | 0.301 |
| $0111111$ | 13 | 2 | 0.913 | 29 steps | 0.252 | 0.390 |

  "Entry within" is the largest rank: every state of that width enters the good set within that many steps. "Sampled
  growth" is a heuristic, not a bound: $\log_2$ of the ratio of the numbers of distinct reading words of lengths 20 and
  12 in the samples, over 8. The lists of least entropy fix the reading at some read positions (words such as $1@0$ or
  $0@1$, a white or black reading at one white phase) and constrain the others; the gap between the least forced
  entropy and the bound is what a wider window or a longer word could still remove, and the bound says that within 16
  cells it cannot reach 0.

**Where it stops.** In each open block the free column $W + 1$ reaches column 1 inside a large component of the window
graph and keeps two closed walks through one window whose readings do not commute; any list forced at that width keeps
all their concatenations. A wider window helps only if the cells beyond column $W$ stop the free column from reaching
column 1, which is the entry question of [the certificate finding](../../findings/columns/period-four-certificate.md),
not a property of the window. This is the same obstruction that [Jen's theorem on farther
columns](jen-farther-columns.md) found for the classes at widths 6 and 10: at widths 16 and 18 the classes add one block
of period 12 and none of period 3 to 9. The positive-entropy lists of [reading
constraints](../../findings/columns/reading-constraints.md) remain the strongest statements of this kind for these
blocks: they narrow the left half and do not exclude the block.

## Reproduce

```bash
python -m computations.zero_entropy --survey 3 12 --width 16 --workers 2   # the 744 blocks with codes, about 35 min
python -m computations.zero_entropy --survey 3 12 --width 18 --walks 0 --workers 2   # the classes alone, about 12 min
python -m computations.zero_entropy --block 001 --width 16                  # one block: components and the code
python -m computations.zero_entropy --search 001 011 00001 00011 --budget 4000000 --width 16
python -m computations.zero_entropy --search 00101 ... 0111111 --budget 1500000 --orders 2 --exhaustive 8 --width 16
```

The last line takes the other 31 blocks of period 5 to 7 (`game.necklaces`); the searches take about 20 and 30 minutes
on a loaded machine. `tests/test_zero_entropy.py` checks the exact zero test and the entropy against dense eigenvalues
on random tagged lists, the forced test against a naive fixed point on sets of states and against
`reading_certificates`, the component counts against `game.bad_pairs`, `game.component_periods` and a plain-Python
rebuild of the graph (`naive_classes`), the code test against brute-force factorizations, and a code at width 12 for
$001$ against a list forced there.
