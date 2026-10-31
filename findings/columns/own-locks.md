---
title: Locked windows of 20 or 22 cells give traps that pass both tests to 14 blocks whose other traps all fail
category: columns
problems: [1]
status: computed
formalization: wanted
evidence: [computations/lock_chain.py, computations/locks.py]
---

# Locked windows of 20 or 22 cells give traps that pass both tests to 14 blocks whose other traps all fail

Every trap that the trap modules give some blocks fails a test that entry needs, so their reductions are empty ([what
failed](../../negative-results/columns/missed-traps.md)). For some of these blocks the block's own game of 20 cells
has locked windows, from which column 1 keeps one value at each white phase whatever the cells beyond do, and every
window can reach one. The bottom components of the locked windows, the strongly connected sets of them that no move
leaves, are traps, and for 14 blocks of periods 11 and 13 they pass both tests: the test of reach in the game of 22
cells and the test of halves apart.

## Method

`own_census` in [computations/lock_chain.py](../../computations/lock_chain.py) finds the locked windows of each block
whose traps all fail (`coverage.refuted_blocks`) with `locks.mixed_nodes`, at 20 cells and with the phase counted modulo
the period, and the share of nodes that can reach one. `own_components` keeps the bottom components among the locked
nodes and `own_tables` writes each as a trap. `own_check` takes them at 20 cells, and at 22 cells when those of 20
cells miss some node of the game of 22 cells or a half of the natural scan is inside a natural trap apart from all of
them. `census_apart` compares the traps with every other trap of the block in the trap modules (`apart_closed`).

## Result

Of the 83 blocks of periods 10 to 13 whose traps all fail, 18 have locked windows of 20 cells, 3 of period 11, 1 of 12
and 14 of 13; for 3 of them only 0.26% to 0.98% of the nodes can reach one. Of the other 15, the traps pass both tests
for these 14 (`WIDE_CENSUS`):

| Block | Period | Traps that fail, from | Cells | States of the traps |
|---|---:|---|---:|---|
| $00000110001$ | 11 | ElevenTraps | 20 | 1,402 |
| $00100111011$ | 11 | ElevenTraps | 20 | 138 |
| $00101101111$ | 11 | ElevenTraps, NaturalTrapsWalls | 22 | 28,594, 138, 188 |
| $0000101011001$ | 13 | ThirteenTraps | 20 | 542, 577 |
| $0000110011101$ | 13 | ThirteenTraps | 22 | 344, 369 |
| $0001001110111$ | 13 | ThirteenTraps | 22 | 48,020, 1,196, 542, 577, 423 |
| $0001010001011$ | 13 | ThirteenTraps | 20 | 119 |
| $0001010100101$ | 13 | CensusTraps13 | 20 | 213, 215 |
| $0001011100111$ | 13 | ThirteenTraps | 20 | 933, 850 |
| $0001110010011$ | 13 | ThirteenTraps | 22 | 3,951, 219, 213 |
| $0001111110011$ | 13 | NaturalTrapsLong | 20 | 6,669, 3,336 |
| $0010011010111$ | 13 | NaturalTrapsLong | 20 | 1,819, 266 |
| $0010111101101$ | 13 | ThirteenTraps | 20 | 369, 344 |
| $0101011111111$ | 13 | CensusTraps13, NaturalTrapsLongLarge | 22 | 816, 137 |

The fifteenth, $0010011110101$, has one trap of 142 states at 20 cells, which 99.992% of the game of 22 cells can
reach; its traps of 22 cells are not computed. Where a block has several traps they are disjoint closed sets of one
game, so entry into any one alone is false and the hypothesis is entry into one of them.

**A carried trap apart from them.** For three of the first five blocks compared, the carried trap of the block's wall
module is apart from its own traps, and they from it: no window of one, cut to the narrower width, is a window of the
other at the same phase (`CENSUS_APART`): `el0_27` of 43 cells for $00000110001$, `el0_14` of 30 cells for
$00100111011$ and `th0_7` of 23 cells for $0001010001011$. So entry into the own traps alone is false for these, and
each block comes down to entry into one of its own traps or the carried trap, which passes the test of reach since the
own traps do. For $0000101011001$ and $0001010100101$ the other trap shares windows with one of the own traps. The
other nine blocks are not compared yet.

## What it means

The blocks count as reduced only once their traps are checked in Lean. `lean_wide_census` writes the declarations of a
module `Rule30Open.Columns.WideCensus`: each own trap with its kernel check, for a block of `CENSUS_APART` the
refutation of entry into the own traps by `not_absorption_some_fwd` of [Traps001](../../Rule30Open/Columns/Traps001.md),
and the reduction of the block to entry into one of its own traps and the apart ones by `absorption_some_excludes` of
[TrapPairs](../../Rule30Open/Columns/TrapPairs.md). With all 14 in Lean, the coverage at period 11 would rise from 53 to
56 of 186, with the two blocks reached by steering alone among them, and at period 13 from 176 to 187 of 630 ([the
coverage](coverage.md)). As for every block reduced to entry into a trap, the hypothesis that no further trap can
refute is entry into some trap of the block.

## Reproduce

```bash
python -m computations.lock_chain --own-census 20 --workers 2
```

```bash
python -m computations.lock_chain --census-apart
```

```bash
python -m computations.lock_chain --lean-wide-census
```

The census of the blocks whose traps all fail takes about four hours with two processes, most of it in the checks at
22 cells; the comparison builds every trap of the trap modules and takes about an hour; `test_own_locks` checks the
traps of $00100111011$ and its carried trap `el0_14` in two minutes.
