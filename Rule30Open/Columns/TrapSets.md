---
title: Entry into one of several traps for 29 blocks whose sampled halves stay apart from their single traps
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.TrapSets
headline: [set0001101101011_excludes, set0000010101101_excludes, set000111111011101_excludes]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/lock_chain.py]
---

# Entry into one of several traps for 29 blocks whose sampled halves stay apart from their single traps

Entry into a trap needs more than the test of reach of [MissedTraps](MissedTraps.md). A half of the natural scan of the
block, a right half driven by the block from the white half or a random start of 64 cells, can be inside a closed set
of windows apart from the trap at step 12,000, and then it never enters. Run over every trap of the trap modules that
passes the test of reach, 1,272 traps and pairs of 1,265 blocks, with the scan closing windows of 16 to 64 cells
(`halves_apart`), this second test refutes 29: 2 of [ElevenTraps](ElevenTraps.md), 1 of [TwelveTraps](TwelveTraps.md),
6 of [ThirteenTraps](ThirteenTraps.md), 2 of [FourteenTraps](FourteenTraps.md), 1 of
[NaturalTrapsLong](NaturalTrapsLong.md), 1 each of [CensusTraps13](CensusTraps13.md) and
[CensusTraps14](CensusTraps14.md), 14 of [CensusTraps15](CensusTraps15.md), and the pair of $0001101101011$ in
[TrapPairs](TrapPairs.md) ([what failed](../../negative-results/columns/missed-traps.md)). For each of the 29 blocks
the block's traps and the natural traps its halves are inside together pass the test of reach at 20 cells, and this
module reduces the block to entry into one of them.

## Statement

1. **The natural traps** (`sets<block>_<k>`, `sets<block>_<k>_check`). 32 labelled traps `WTrap` of 21 to 42 cells,
   103 to 718 states, with labels modulo the period, or twice the period for $0001011110111$, each passing the check of
   [WordTraps](WordTraps.md).
2. **The sets** (`set<block>`). For each of 29 blocks, 2 of period 11, 1 of period 12, 8 of period 13, 4 of period 14
   and 14 of period 15: the block's traps in the trap modules, by name, and one or two natural traps.
3. **The reductions** (`set<block>_excludes`). If every finitely supported right half driven by the block enters one
   of the traps of its set (`WTrap.AbsorptionSome` of [TrapPairs](TrapPairs.md)), the center column does not eventually
   repeat the block.

## Argument

Each natural trap is the closure, under both values of the cell beyond, of the window of one half of the scan at step
12,000, at the least width from 16 whose closure fixes column 1 at the white phases (`natural_tables` in
[computations/lock_chain.py](../../computations/lock_chain.py)). The kernel checks each trap of each set, so the closure
is not trusted, and `absorption_some_excludes` of [TrapPairs](TrapPairs.md) gives each reduction. A natural trap that
is the state set of one of the block's traps is left out (`TRAP_SETS`).

## What it covers

For 18 of the 29 blocks no half of the scan that the scan finds in a trap is in the module's trap: for $000111111011101$
all 31 halves are inside one natural trap of 27 cells, for $000000110011101$ 30 inside one of 28 cells and one inside
one of 42, and for $0000010101101$ all 13 that lock inside one of 23. The modules' traps there came from walls carried
along a background's columns, or from the census of locked windows of 16 cells, and the halves settle into wider closed
sets instead. Nine of the natural traps of period 15 have 193 states, at widths 27 to 39, and three have 652, at 37 to
42. They are two walls of period 15 wider than the 16 cells the census sees, each carried along its background's
columns: the nine blocks are those of the chain of the narrowest, the trap of 27 cells of $000111111011101$, at the
distances 0 to 12 that their widths give, and the three those of the chain of the trap of 37 cells of $000001101011101$,
at distances 0, 1 and 5 (`trap_chain`). Both walls belong to the background of 2,145 cells, and
[FifteenWalls](FifteenWalls.md) carries them to blocks that nothing else reaches. The 29 blocks stay among those reduced
to entry into traps that pass both tests, so the counts of [the coverage table](../../findings/columns/coverage.md) do
not change. Passing the tests is necessary for entry, not sufficient: entry into one of the traps of a set, for every
finite right half, stays open.

## Relation to the kit

The kit's `Absorption` for the words of period four asks entry into one member of an infinite family, after its single
certificates fail (`Rule30Ether.never_enters_S0001` and the two after it). The sets here are finite families of the
same kind, found from where sampled halves settle.

## Lean

`Rule30Open.Columns.TrapSets`: the natural traps `sets<block>_<k>` with their checks, and for each block the list
`set<block>` and `set<block>_excludes`. The tables come from `python -m computations.lock_chain --lean-trap-sets`.

## Reproduce

```bash
python -m computations.lock_chain --lean-trap-sets
```

The natural traps, rebuilt from the scans' starts, in about two minutes; `test_trap_sets` checks one set's traps and
the reach of their union.
