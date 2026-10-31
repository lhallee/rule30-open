---
title: Traps for blocks of period 2, 3, 5, 6, 7 and 9, by the kit's labelled-trap check for a block of any period
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.WordTraps
headline: [wtrap_column, center_wtrap, absorption_excludes, not_eventually_01_of_absorption, not_eventually_001_of_absorption_fifteen, not_eventually_01111_of_absorption, not_eventually_001011_of_absorption, not_eventually_0011101_of_absorption, not_eventually_001011101_of_absorption]
kit: refines
kit_modules: [Rule30EtherThreeTrap, Rule30EtherThree, Rule30Ether]
evidence: [computations/lock_chain.py]
---

# Traps for blocks of period 2, 3, 5, 6, 7 and 9, by the kit's labelled-trap check for a block of any period

The kit reduces the word $001$ to entry into a trap: a set of states of the 47 cells next to the center, each with a
time label modulo 21, that the rule never leaves, on which the cell beside the center is a function of the label at
the white phases (`t001`). This module writes the kit's check for a block of any period, proves it sound for every
column of every row with a leftmost 1, and checks six traps that the chains of [lock
chains](../../findings/columns/lock-chains.md) produce: for $01111$ of period 5, $001011$ of period 6, $0011101$ of
period 7 and $001011101$ of period 9, the first traps for blocks of these periods, a second one for $001$, and one for
$01$, which is the kit's ether-and-wall family read as a chain. With the kit's traps for $001$ and the words of period
four, every period from 2 to 9 except 8 now has a block that a trap reduces to entry, and at period 8 the kit excludes
$0\,1^7$ outright. No window of up to 18 cells has a lock for any block of period 2, 3, 5, 6, 7 or 9 ([window
locks](../../negative-results/columns/window-locks.md)); these are wider and count the phase modulo a multiple of the
period.

## Statement

A labelled trap `WTrap` for a block $b$ of period $P$ has a width $K$, labels modulo a multiple $m$ of $P$, and states
$i < n$, each a window of $K$ cells, a label and, for each value of the cell beyond the window, the index of the next
state. The check `WTrap.check` asks that the next state of state $i$ under the value $z$ be the window that one step of
the rule gives beside a column reading $b$ at phase $\mathrm{lab}(i) \bmod P$, with label $\mathrm{lab}(i) + 1$
modulo $m$, and that at a white phase the first cell be bit $\mathrm{lab}(i)$ of a fixed number $u$.

1. **Soundness** (`wtrap_column`). In the orbit of a row with a leftmost 1, if column $k$ repeats $b$ from time $T$
   and at some $t_1 \ge T$ the cells $k + 1, \dots, k + K$ are the window of a state $i$ of a checked trap whose label
   agrees with the phase of $b$ at $t_1$ modulo $P$, contradiction. `center_wtrap` is the same for the center column of
   the single cell.
2. **Entry excludes the block** (`absorption_excludes`). If every finitely supported right half driven by $b$, from any
   phase, enters the trap (`WTrap.Absorption`, the kit's `AbsorptionT` for any period), the center column does not
   eventually repeat $b$, for every transient (the kit's `EventuallyWord`).
3. **Six traps**, each with its kernel check:

   | trap | block | period | cells | labels modulo | states |
   |---|---|---|---|---|---|
   | `trap01` | $01$ | 2 | 19 | 8 | 109 |
   | `trap001fifteen` | $001$ | 3 | 52 | 15 | 153 |
   | `trap01111` | $01111$ | 5 | 107 | 20 | 1,076 |
   | `trap001011` | $001011$ | 6 | 29 | 12 | 116 |
   | `trap0011101` | $0011101$ | 7 | 35 | 14 | 126 |
   | `trap001011101` | $001011101$ | 9 | 30 | 18 | 1,410 |

   so `not_eventually_01_of_absorption`, `not_eventually_001_of_absorption_fifteen`,
   `not_eventually_01111_of_absorption`, `not_eventually_001011_of_absorption`,
   `not_eventually_0011101_of_absorption` and `not_eventually_001011101_of_absorption` reduce each block to entry into
   its trap.

## Argument

1. **The trap holds the window** (`wtrap_invariant`). The cells $k + 1, \dots, k + K$ at time $t + 1$ are one step of
   the rule on the same cells at time $t$, with column $k$ on the left and column $k + K + 1$ on the right
   (`codeFrom_succ`). Column $k$ reads $b$ at the phase that the label gives modulo $P$, since $P$ divides $m$
   (`WTrap.phase`), so the check's successor under the true value of column $k + K + 1$ is the next window, one label
   later. By induction the window stays in the trap with the label advancing by one per step.
2. **Two columns repeat.** At the white times of column $k$ the trap fixes column $k + 1$ as bit $\ell$ of $u$, $\ell$
   the label, a function of the time modulo $m$. Column $k - 1$ at time $t$ is column $k$ at time $t + 1$ xor (column
   $k$ or column $k + 1$ at time $t$) (`left_cell`): at a black time the bracket is 1, at a white time it is that bit.
   So column $k - 1$ repeats with period $m$ from $t_1$ on, and column $k$ repeats with period $P$, hence $m$; Jen's
   theorem on adjacent columns ([AdjacentColumns](AdjacentColumns.md)) rules this out.
3. **Entry.** If the center column repeats $b$ from $T$, the right half from $T$ on is the half driven by $b$ from the
   row at $T$ (the kit's `cell_eq_drv`), which is white beyond cell $T$; its entry is entry of the true right half,
   which item 1 rules out, read with a shift that aligns the phases.
4. **The traps.** Each is a chain lock: the locked window of a seed, a block with a long run of 1s, carried left
   through the columns that the rule determines from it, then relabeled so that the block reads its least rotation
   ([lock chains](../../findings/columns/lock-chains.md)). The seeds are $0\,1^7$, $0^4\,1\,0\,1^9$, $0^{10}\,1^{10}$,
   $0^3\,1^9$, $0^4\,1^{10}$ and $0^5\,1\,1\,0\,0\,1^9$, of period 8, 15, 20, 12, 14 and 18, carried 14, 47, 98,
   24, 30 and 21 columns. For $01$ the 19 cells are six columns of the kit's ether and one of its 109 wall states. The
   kernel checks the tables, so how they were found does not matter: `trap01_check` and the five others are
   `decide +kernel` on `WTrap.check`.

## What it covers

Each trap is a contradiction device of the kit's kind: it says nothing about whether a right half driven by the block
enters it, which stays open, as the kit's `AbsorptionT t001` and `Absorption` do for $001$ and the words of period
four. What it adds is the reduction itself for four periods where none was known: a block of period 5, 6, 7 or 9 is
now excluded by a statement of the same kind as the kit's for period three. Entry looks hard in the same way: the traps
are wider than the kit's wall for period four, and under $001$ entry into the kit's trap takes up to $2 \cdot 10^5$
steps ([the census for 001](../../findings/columns/t001-census.md)). Each trap reduces one block of its period, not the
period: the other blocks of period 5, 6, 7 and 9 have no trap found.

**The test of reach.** In the game of 20 cells, two of the seven traps here fail the test of
[MissedTraps](MissedTraps.md), `trap01` for $01$ and `trap001fifteen` for $001$: some node cannot reach a window whose
first cells form a state of the trap, cut to 20 cells when the trap is wider, so a right half whose first 20 cells start
there never enters, and entry into the trap is false ([what failed](../../negative-results/columns/missed-traps.md)).
The block $001$ keeps the kit's `t001`, which passes the test at every width up to 24 ([reach of the kit's
conjectures](../../findings/columns/kit-absorption-reach.md)); for $01$ no trap here passes, so its reduction is empty.
The other five traps pass the test, which entry needs but does not imply.

## Relation to the kit

`WTrap` is the kit's `Rule30EtherThree.PTrap`
([`Rule30EtherThreeTrap`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30EtherThreeTrap.lean))
with the period 3 replaced by the block's length, the same packed tables and the kit's `allBelowT`; its absorption
statement is the kit's `AbsorptionT` with the kit's driven half `Rule30Ether.drv` and strip encoding
`Rule30EtherThree.EncF`. The kit proves soundness for the center column through masked Jen; `wtrap_column` holds for
every column of every row with a leftmost 1, through the adjacent-column form of Jen's theorem. The kit's traps are
`t001` for $001$ and its ether-and-wall family, whose `absorption_excludes` holds for any aligned word: the words of
period four and, through `aligned_0101_3`, $0101$, so the kit already reduces $01$ to entry into its family, and
`trap01` is that reduction with one trap of 19 cells. Its table of strip certificates has no block of period 5, 6, 7 or
9.

## Lean

`Rule30Open.Columns.WordTraps`: `WTrap`, `WTrap.st`, `WTrap.lab`, `WTrap.nxt`, `WTrap.edgeOK`, `WTrap.nodeOK`,
`WTrap.check`, `WTrap.facts`, `WTrap.step`, `WTrap.phase`, `wtrap_invariant`, `wtrap_column`, `center_wtrap`,
`WTrap.Absorption`, `absorption_excludes`, the traps `trap01`, `trap001fifteen`, `trap01111`, `trap001011`,
`trap0011101` and `trap001011101` with their checks, and the six reductions `not_eventually_*_of_absorption*`. The
tables come from `python -m computations.lock_chain --lean`, which prints them from `lean_trap`.
