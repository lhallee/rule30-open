---
title: The game with cyclic classes at 16 cells excludes 000000001011, a block of period 12 nothing else excludes
category: columns
problems: [1]
status: computed
formalization: wanted
evidence: [computations/zero_entropy.py, computations/game.py, computations/bit_game.py]
---

# The game with cyclic classes at 16 cells excludes 000000001011, a block of period 12 nothing else excludes

No column of a row with a leftmost 1, the center column of the single cell among them, eventually repeats
$000000001011$ ($0^8 1011$), in any rotation. Neither the finite game at any width up to 18, nor the kit, nor any other
exclusion of this repository reaches this block. The proof is a finite computation at 16 cells; it is not yet in Lean.

## The argument

Let column $k$ repeat the block $b$ from some time on. [The finite game](../../Rule30Open/Columns/FiniteGame.md)
follows the cells $k + 1, \dots, k + 16$ with cell $k + 17$ free: a node is a phase of $b$ and the 16 cells, and every
real row is one play. A play ends inside one strongly connected component that has a move inside it. If $d$ is the gcd
of the lengths of that component's cycles, its nodes fall into $d$ cyclic classes, and every move inside it goes from
one class to the next; so a play that stays in it visits the classes in turn, with period $d$. The column left of $k$
at time $t$ is $c_{t+1} \oplus (c_t \lor x_t)$, with $c$ the repeating column and $x$ the cell right of it. If in
every component that can hold a play this is a function of the class, the column left of $k$ is eventually periodic,
and [the adjacent-column theorem](../../Rule30Open/Columns/AdjacentColumns.md) excludes two adjacent eventually periodic
columns. The game asks for a function of the phase, which is the case $d = P$; the class asks less when $d > P$
(`game.component_periods`, [Jen's theorem on farther columns](../../negative-results/columns/jen-farther-columns.md)).

For $b = 000000001011$ at 16 cells, with 786,432 nodes, the components that can hold a play are three:

| nodes | cyclic period | left column a function of the phase | of the class |
|---:|---:|---|---|
| 7,312 | 12 | yes | yes |
| 532 | 36 | no | yes |
| 22 | 12 | yes | yes |

The component of 532 nodes keeps the game from closing: at one phase the left column takes both values there. Its
cycles all have lengths divisible by 36, three periods of the block, and on each of its 36 classes the left column has
one value, so a play that stays in it gives the left column period 36. At 15 cells the class test fails (a component of
452 nodes and cyclic period 12 mixes), so 16 is the least width. Of the 744 primitive blocks of period 3 to 12, the
class test at 16 or 18 cells closes the 22 that the game excludes, this block, and $0^9 1$ (at 12 cells, a component of
86 nodes and cyclic period 20), which the kit already excludes as a padded word; it closes no other
([zero-entropy readings](../../negative-results/columns/zero-entropy-readings.md), which also shows why: the class test
is exactly what a list of reading words of entropy 0 needs).

## Checks

- **Three computations of the components.** `zero_entropy.analyze` (scipy, levels by a breadth-first search from a
  root of each component), `game.component_periods` (the repository's own, from `game.game_graph`) and
  `zero_entropy.naive_classes` (the graph rebuilt cell by cell in plain Python, Tarjan's algorithm, levels by a search)
  give the same three components, the same cyclic periods and the same answers.
- **The block read three times.** The game on $b^3$, a block of period 36, is the game on $b$ with the phase counted
  modulo 36, and its components are the lifts of those of $b$; on it the class test is the game's own test.
  `bit_game.criterion` passes on $b^3$ at width 16, with the set reached after 106 images and one round of refinement,
  and `bit_game.phase_rounds` passes at every one of the 36 phases with at most two rounds and closures of at most 114
  steps.
- **Real right halves.** 164 right halves (every half of up to 6 cells and 100 random halves of 40 cells), driven cell
  by cell beside the center repeating $b$ for 4,000 steps, all read column 1 with period 12 at the end
  (`zero_entropy.driven_period`): they settle in the large component, where the game's phase test already holds.

## Not excluded elsewhere

The finite game does not exclude $b$ at any width up to 18 (at every width from 3 to 18 some component that can hold a
play mixes at a phase). The kit's padded words $0^q 1$, $0^r 11$ and $0^q 10111$ and its strip certificates do not
include it (`game.kit_blocks`; the kit's table has $0^9 1011$, of period 13). Its runs of 1s are short, so the long-runs
and wall families do not apply, and [limit windows](limit-windows.md) add no block to the game's list up to period 21.
[LockBlocks12](../../Rule30Open/Columns/LockBlocks12.md) and [LockWhite](../../Rule30Open/Columns/LockWhite.md) reduce
it to entry into a lock (column 14 never reads an 81-value steering sequence, or column 13 is never white for 36 steps),
and [NaturalTraps](../../Rule30Open/Columns/NaturalTraps.md) has a kernel-checked trap for it (`nat000000001011`, 16
cells, 7,312 states), also conditional on entry.

The method is not new: it is the repository's finite game applied to $b^3$, the block read three times, which the
surveys of the game skip because they run over primitive blocks only.

## Lean

The kernel route is [BitPhases](../../Rule30Open/Columns/BitPhases.md) on $b^3$: `center_not_phases` applies to
`wordOf 36` of $b^3$, since a center that repeats $b$ repeats $b^3$, and one `phaseCheck` per phase at width 16. It does
not fit this machine: one phase with no images (36 phases of $2^{18}$ bits per table) ran out of memory at 13 GB, and
the 106 images of the block itself at width 16 alone took 29 seconds and 10 GB. A proof needs a lighter check: the
refinement restricted to the set reached (14,476 of the 786,432 nodes of $b$, so 43,428 of $b^3$), whose images a
coarser window can bound, or a certificate of ranks and classes on that set.

## Reproduce

```bash
python -m computations.zero_entropy --block 000000001011 --width 16 --naive   # three components, twice, about 30 s
python -c "from computations import game; print(game.component_periods('000000001011', 16))"   # the repository's own
python -c "from computations import bit_game; print(bit_game.criterion('000000001011' * 3, 16))"   # about 2 min
```
