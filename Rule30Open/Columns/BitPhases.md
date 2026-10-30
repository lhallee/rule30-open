---
title: The game decided phase by phase in the kernel excludes the 14 blocks of period 17 and 18 that need 13 or 14 cells
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.BitPhases
headline: [phases_column, center_not_phases, phases_not_eventuallyWord, center_not_blocksPhases18,
  not_eventually_blocksPhases18]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/bit_game.py, computations/game.py]
---

# The game decided phase by phase in the kernel excludes the 14 blocks of period 17 and 18 that need 13 or 14 cells

The center column of the single cell does not eventually repeat any of the 14 blocks of `blocksPhases18`, from any time
on and in any rotation (`center_not_blocksPhases18`); `not_eventually_blocksPhases18` says the same in the kit's form
`Rule30StripCertificates.EventuallyWord`. They are the blocks of period 17 and 18 that [the finite game](FiniteGame.md)
excludes only at 13 or 14 cells, and that neither the kit nor [WallSets](WallSets.md) excludes ([the game blocks of
period 17 and 18](../../findings/columns/game-blocks-18.md)). [BitGame](BitGame.md) checks a block in one declaration,
and at these widths the kernel holds 2 to 12 GB for one block, or more. Here each phase of a block is its own
declaration. With [BitPhases19](BitPhases19.md) and [BitPhases20](BitPhases20.md), every one of the 966 blocks of period
at most 20 that the game excludes is excluded in Lean, by the kit or in this repository.

## Statement

1. `phases_column`: in the orbit of a row with a leftmost 1, no column repeats, from any time on and in any rotation, a
   block $b$ each of whose phases $\varphi$ passes `phaseCheck b K D rounds fuel φ` for some number of images $D$,
   rounds and fuel, with $K \ge 1$.
2. `center_not_phases`, `phases_not_eventuallyWord`, `center_not_phases_list`, `phases_list_not_eventually`: the same
   for the center column, in the kit's form `EventuallyWord`, and for each entry of a list of blocks.
3. `center_not_blocksPhases18`, `not_eventually_blocksPhases18`: the center column does not eventually repeat any of
   the 14 blocks below, in any rotation.

## Argument

1. **One phase at a time.** `gameCheck` is a conjunction over the phases: at phase $\varphi$, the nodes of that phase
   that $D$ images of everything reach are split by the value of the column left of the repeating one, and the
   refinement keeps the nodes of each value that reach and are reached by nodes of the other value, until one side is
   empty. The argument of `bitGame_column` uses each phase on its own: if both values recurred at phase $\varphi$, a
   node of each value would be visited again and again after step $T + D$, so both would lie in the set reached and
   survive every round (`refine_sound`). Nothing ties the $D$, the rounds or the fuel of one phase to those of another,
   and `phases_column` is the same argument with one check per phase. 2. **No images.** Every play lies in the set of
   all nodes, so $D = 0$ is allowed: the refinement then starts from every node of the phase, and the nodes that no play
   visits forever leave it in its rounds. Every phase of the 40 blocks here and in the two modules beside it passes with
   $D = 0$ after at most 4 rounds, with closures of at most 140 steps (`phase_rounds` in
   [computations/bit_game.py](../../computations/bit_game.py)). 3. **One declaration per phase.** The kernel keeps every
   table it computes until a declaration is checked, so in one `gameCheck` the tables of all phases add up: at 13 and 14
   cells one block took 2 to 12 GB, and one of period 20 did not fit in 13 GB. Each phase here is its own theorem,
   `w<block>_<φ>`, gathered by a pattern match in `w<block>`, so the kernel holds the tables of one phase at a time. The
   module builds in about four and a half minutes with a peak of about 3.6 GB.

## The blocks

| Block | Width | Phases with rounds | Most rounds |
|---|---|---|---|
| $00000000000101101$ | 13 | 13 | 4 |
| $00000000000111011$ | 14 | 12 | 3 |
| $00000000011011111$ | 13 | 10 | 2 |
| $00000000101110101$ | 13 | 11 | 2 |
| $00000000110110111$ | 13 | 10 | 3 |
| $00000001011111001$ | 14 | 10 | 2 |
| $00000010111101111$ | 13 | 8 | 3 |
| $00111001111111101$ | 13 | 5 | 4 |
| $000000000000000111$ | 14 | 15 | 3 |
| $000000000010000101$ | 13 | 15 | 1 |
| $000000000010010001$ | 14 | 15 | 3 |
| $000001011111111001$ | 14 | 8 | 2 |
| $000010111111110111$ | 14 | 6 | 4 |
| $000101111111111001$ | 13 | 6 | 3 |

Each width is the least at which the game excludes the block; at the other phases one value of the left column is
already missing from the nodes of the phase.

## Relation to the kit

The kit's strip certificates (`Rule30StripCertificates`) are checked against stored tables; the kit has nothing that
decides a block from the block alone, at one phase or all of them. The statement form comes from
`Rule30StripCertificates` and `Rule30StripCertificateTable`, as in [BitGame](BitGame.md).

## Lean

`Rule30Open.Columns.BitPhases`: `BitGame.phaseCheck`, `phases_column`, `center_not_phases`,
`phases_not_eventuallyWord`, `center_not_phases_list`, `phases_list_not_eventually`; for each block one theorem
`w<block>_<φ>` per phase and `w<block>` that gathers them; `blocksPhases18`, `blocksPhases18_phases`,
`blocksPhases18_pos`, `center_not_blocksPhases18` and `not_eventually_blocksPhases18`. The checks come from
`python -m computations.bit_game --phases 17,18`.
