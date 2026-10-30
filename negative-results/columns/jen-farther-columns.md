---
title: Jen's theorem on farther columns, or on periods longer than the block's, does not strengthen the finite game
category: columns
problems: [1]
status: negative
kind: no-signal
evidence: [computations/game.py]
---

# Jen's theorem on farther columns, or on periods longer than the block's, does not strengthen the finite game

**Idea.** [The finite game](../../Rule30Open/Columns/FiniteGame.md) excludes a repeating block when, in every
component of its graph that can hold a play forever, the column left of the repeating one is a function of the phase;
the adjacent-column theorem then applies. Jen's theorem forbids more: no second column of a row with a leftmost 1 is
eventually periodic at all (the kit's `Rule30FiniteConfigs.jen`). So a component also closes when a farther column is
eventually periodic along every play that stays in it. Three tests show that:

- one of the columns $1, \dots, K$ right of the repeating column is a function of the phase on the component;
- the free cell, column $K + 1$, is a function of the phase on the moves inside the component;
- for some $j$, the moves inside the component, read on the phase and columns $1, \dots, j$, are a function of the
  phase and columns $1, \dots, j$ at the start, so those columns run as a finite deterministic system with a periodic
  input.

For the words of period 4, whose game fails at every width tried, this was meant to close the components that keep
the right half from locking: the plugs of [the certificate finding](../../findings/columns/period-four-certificate.md)
carry a column that repeats the drive word, which Jen's theorem forbids.

**Outcome.** The tests close some components and no block. Over the 747 primitive blocks of period up to 12, at
widths 6 and 10, the extended game excludes exactly the 23 blocks the game excludes. For the three words of period 4
it closes the small open components and leaves one large one at every width:

| word | width 6 | width 8 | width 10 | width 12 |
|---|---|---|---|---|
| $0001$ | 46, 23 | 113, 55 | 318 | 927 |
| $0011$ | 96 | 262 | 737 | 2,084 |
| $0111$ | 114 | 370 | 1,051 | 3,096 |

(sizes of the components that stay open, in nodes; a node is a phase and the cells $1, \dots, K$). At width 12 the game
alone leaves open components of 927, 97, 87, 33 and 12 nodes for $0001$; the farther columns close all but the
largest. In the large component no column, no free cell and no prefix of columns behaves periodically: the free cell
reaches column 1 there, and with a free cell on the right every column can be kept from repeating.

**Periods longer than the block's.** A play that stays in a component also visits its cyclic classes in turn: the
classes modulo the gcd $d$ of the lengths of its cycles, a multiple of the period $P$, since every move advances the
phase by one. So the left column is eventually periodic, with period $d$, along every such play as soon as it is a
function of the class, which the adjacent-column theorem forbids as well; for $d > P$ this asks less than a function of
the phase (`component_periods`). It adds no block either. Over the same 747 blocks at widths 6 and 10 it excludes the
same 23, and at width 10 the components where the left column takes both values in one class have period $P$, 744 of
them, but one, of period $2P$, which sits beside a component of period $P$ that also mixes. Each of the 724 blocks the
game leaves open has a component of period $P$ where both values meet in one class, and there the classes are the
phases.

**What it means.** The failure of the game for period 4 is not a periodic plug that Jen's theorem could exclude from
inside the window. It is a component where the free cell drives the window chaotically, the same obstruction that
keeps the window from forcing entry into the lock
([the certificate finding](../../findings/columns/period-four-certificate.md#attraction-is-open)). A proof of locking
has to use what lies beyond the window, which [the absorption census](../../findings/columns/absorption-census.md)
shows does lead every small right half into the trap.

**Reproduce.** `python -m computations.game --max-period 12 --widths 6,10 --jen`, with `jen_open` in
[computations/game.py](../../computations/game.py), in about 10 s, and the same with `--cyclic` for the cyclic classes,
`component_periods`, in under a minute. The open components of the game alone come from `game_graph` in the same
module.
