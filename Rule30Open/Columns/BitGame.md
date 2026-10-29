---
title: The finite game, decided in the kernel without a certificate, excludes seven blocks of period 14 to 16 that need 12 to 14 cells
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.BitGame
headline: [bitGame_column, center_not_bitGame, bitGame_not_eventuallyWord, center_not_restBlocks, not_eventually_restBlocks]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable, Rule30ZeroBoundaryLanes]
evidence: [computations/bit_game.py, computations/game.py]
---

# The finite game, decided in the kernel without a certificate, excludes seven blocks of period 14 to 16 that need 12 to 14 cells

[The finite game](FiniteGame.md) excludes a repeating block when every play makes the column left of the repeating one
periodic in the end. [GameBlocks](GameBlocks.md) and [GameBlocksLong](GameBlocksLong.md) check stored certificates node
by node; seven blocks of period at most 16 were left out, because at widths 12 to 14, with 65,536 to 262,144 nodes,
their certificates would add megabytes of hexadecimal. Here the kernel decides the question from the block alone. A set
of nodes is one number with one bit per node, and one step of the game acts on all of them at once through masked
shifts. The seven blocks are excluded this way, so each of the 197 blocks of period at most 16 that the game excludes is
excluded in Lean, here or in the kit.

## Statement

1. `bitGame_column`: in the orbit of a row with a leftmost 1, no column repeats, from any time on and in any rotation,
   a block $b$ for which `gameCheck b K D rounds fuel` holds.
2. `center_not_bitGame`, `bitGame_not_eventuallyWord`: the same for the center column, and in the kit's form
   `Rule30StripCertificates.EventuallyWord`, which composes with its `problem1_iff_no_word`.
3. `center_not_restBlocks`, `not_eventually_restBlocks`: the center column does not eventually repeat $00000001001111$,
   $00000000010001$, $000000000101101$, $000001011111011$, $0000001011111011$, $0000101111111011$ or
   $0001011111111001$, in any rotation.
4. `post_sound`, `pre_sound`: the image and the preimage of a set of nodes, computed with masks and shifts, hold every
   move of its nodes and every node with a move into it, for every block and width.

## Argument

1. **Nodes as bits.** Let column $k$ repeat the block $b$ of length $P$. A node is a phase $\varphi$ and the cells
   $k + 1, \dots, k + K$ as a number $r$: bit $\varphi \cdot 2^{K+2} + r$ of a table. The two index bits above the
   cells hold the column and the free cell during a step, and a set of nodes is stored the same over both.
2. **A step as a product of flips** (`phis_undo`, `undo_move`, `rot_move`). With the column cell $c$ at index bit $K$
   and the free cell $u$ at bit $K + 1$, one step sends $(c, r, u)$ to $(y, r_{K-1}, u)$, $y$ the next cells. Rule 30
   is permutive in its left cell: for $j = 0, \dots, K - 1$ the new cell $y_j$ takes the place of $r_{j-1}$ (of $c$
   for $j = 0$) by flipping that bit when $r_j$ or $r_{j+1}$ ($u$ for $j = K - 1$) is set. So the step is a product of
   $K$ flips of one index bit, a bijection, and the flips in reverse order undo it.
3. **Flips and swaps of tables** (`ds_spec`, `dsFlip_spec`, `dsSwap_spec`). Composing a truth table $T$ with the flip
   of index bit $t$ is a delta swap, $T \oplus x \oplus (x \ll 2^t)$ with $x = ((T \gg 2^t) \oplus T) \land M$, for
   the mask $M$ of the indices with bit $t$ clear and the condition set. The exchange of two adjacent index bits is
   another.
4. **Image and preimage** (`post`, `pre`, `post_sound`, `pre_sound`). The image keeps the nodes whose bit $K$ is the
   column of their phase, applies the $K$ flips, forgets the last cell and the free cell by projections, puts the new
   cells back with $K$ swaps, and moves each block to the next phase. The preimage runs the same backward. Both are
   proved to hold the true image and preimage.
5. **The check** (`gameCheck`). After $D$ images of everything every play lies in the set reached (`play_reach`). At
   each phase, split that set by the value of the column left of $k$, $c' \oplus (c \lor r_0)$. Each round keeps the
   nodes of each value that the other value's nodes reach and that reach them; the forward and backward closures come
   from a search one phase at a time, and the kernel accepts them only if they hold their seed's image (preimage) and
   their own (`fwdOk`, `bwdOk`). The check passes when every phase ends with one side empty.
6. **Why that suffices** (`refine_sound`, `bitGame_column`). If the play showed both values at a phase forever, some
   node of each value would be visited again and again (`pigeonhole`), each reaching the other, and both would survive
   every round; an empty side rules that out. So at each phase the value is constant in the end, column $k - 1$
   repeats with period $P$, and [the adjacent-column theorem](AdjacentColumns.md) excludes two adjacent eventually
   periodic columns.

## The seven blocks

| Block | Width | $D$ | Rounds | Longest closure |
|---|---|---|---|---|
| $00000001001111$ | 13 | 127 | 0 | |
| $00000000010001$ | 14 | 89 | 0 | |
| $000000000101101$ | 14 | 75 | 3 | 106 |
| $000001011111011$ | 14 | 114 | 1 | 99 |
| $0000001011111011$ | 12 | 110 | 0 | |
| $0000101111111011$ | 13 | 142 | 0 | |
| $0001011111111001$ | 14 | 95 | 3 | 87 |

Each width is the least at which the game excludes the block, and $D$ the number of images after which the set reached
stops changing (`python -m computations.bit_game`). For four blocks the column left of $k$ is already a function of the
phase on that set; three need rounds, because the play can pass between components with different values. The module
builds in about 75 seconds with a peak of about 6 GB, most of it in the three blocks with rounds: the kernel keeps every
intermediate table, and a table of 15 or 16 phases at width 14 has a million bits.

## Beyond the seven

The check is the game's criterion computed another way, and it decides every block the game excludes up to period 16 at
the least width the game needs: all 197, with at most 142 images, 3 rounds and closures of at most 106 steps
(`python -m computations.bit_game --max-period 16`, about 20 minutes). So the certificates of
[GameBlocks](GameBlocks.md) and [GameBlocksLong](GameBlocksLong.md) could be replaced by one line each; they stay as
they are, checked in a few seconds. [computations/bit_game.py](../../computations/bit_game.py) holds the same check on
the game graph and the bit tables in Python, and its test compares both with the game.

## Relation to the kit

The kit's strip certificates (`Rule30StripCertificates`) are checked in its kernel against stored tables, as the
certificates here were; the kit has nothing that decides a block without one. The lane patterns come from its
`Rule30ZeroBoundaryLanes.pat`, and the step and the statement form from `Rule30StripCertificates` and
`Rule30StripCertificateTable`.

## Lean

`Rule30Open.Columns.BitGame`, in the namespace `Rule30Open.BitGame` up to `testBit_zero_blk`: the delta swap `ds` and
`ds_spec`; the patterns `rep`, `ip`, `nip`, `full` and the masks
`flipMask`, `swapMask`, `colMask`, `valMask`, `blockSel`; the index maps `flipIdx`, `swapIdx`, `idxFlips`, `idxSwaps`
and their lemmas; `proj`, `canon`, `shiftUp`, `shiftDown`; the step as flips, `phiF`, `phis`, `rotDown`, `phis_undo`,
`rot_move`, `undo_move`; `post`, `pre`, `post_sound`, `pre_sound`; the check `reach`, `bfsF`, `bfsB`, `fwdClose`,
`bwdClose`, `fwdOk`, `bwdOk`, `refine`, `gameCheck`; the play `pos`, `play_step`, `play_reach`, `play_fwd`,
`play_bwd`; `refine_sound`, `pigeonhole`, `common_bound`, `bitGame_column`, `center_not_bitGame`,
`bitGame_not_eventuallyWord`; and `restBlocks` with its seven checks, `center_not_restBlocks` and
`not_eventually_restBlocks`.
