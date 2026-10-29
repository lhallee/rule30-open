---
title: A right half with at most two black cells among its first cells enters the ether-and-wall family
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.SparseRight
headline: [inFamily_of_fast, stateAt_eq, two_absorption, sparse_0001, sparse_0011, sparse_0111, oneCell_0011, oneCell_0111, sparseRight_0001, sparseRight_0011, sparseRight_0111]
kit: refines
kit_modules: [Rule30Ether, Rule30EtherSingleCell, Rule30EtherThreeReach]
evidence: [computations/sparse_halves.py]
---

# A right half with at most two black cells among its first cells enters the ether-and-wall family

The kit reduces least period four for the center column to attraction: every finite right half, driven by the word,
enters its ether-and-wall family (the open `Rule30Ether.Absorption`). The kit proves it for one black cell, anywhere,
under $0001$. Here it is proved for every right half with at most two black cells among its first $G$ cells, whatever
lies beyond, for each of the three words.

## Statement

Drive a right half $x$, cells $1, 2, \dots$ beside the center, with the center repeating a word $w$ of least period four
from phase $\varphi$.

1. **The family off bit masks** (`fastFamily`, `inFamily_of_fast`). Pack the half as a number, bit $i$ for cell
   $i + 1$. If at step $t$ the packed half agrees with the aligned ether on its first $k$ bits and its next 13 bits are
   one of the kit's wall states, with column $k$ a $B_3$, then every half that agrees with it on cells
   $1, \dots, t + k + 13$ is in the family at step $t$.
2. **Four steps at a time** (`stateAt_eq`). Blocks of four steps of the packed half, with the four center values fixed,
   are the kit's driven half `Rule30EtherThree.rowN`.
3. **Two black cells** (`two_absorption`). Suppose every half white on cells $1, \dots, 30$ enters, and for each
   $p_1 \le 30$ the half $\{p_1\}$ enters at a step $t$ and depth $k$, and each half $\{p_1, p_2\}$ with
   $p_1 < p_2 \le t + k + 13$ enters at a step $t'$ and depth $k'$, all with step plus depth plus 13 at most $G$.
   Then every half with at most two black cells among cells $1, \dots, G$ enters.
4. **The three words** (`sparse_0001`, `sparse_0011`, `sparse_0111`). Every right half with at most two black cells
   among cells $1, \dots, G$ enters the family, in every phase, whatever lies beyond $G$, with $G = 778$ for $0001$,
   $1{,}359$ for $0011$ and $623$ for $0111$. One black cell, anywhere, enters under each word (`oneCell_0011`,
   `oneCell_0111`; the kit's `singleCell_absorption` for $0001$).
5. **The exclusion** (`sparseRight_0001`, `sparseRight_0011`, `sparseRight_0111`). No finite configuration with at
   most two black cells among cells $1, \dots, G$ has a center column that repeats the word, whatever its left half and
   its cells beyond $G$.

## Argument

1. The ether check compares the packed half with a 64-bit ether pattern under a mask of $k$ bits, and the wall check
   looks the next 13 bits up in a table of the kit's wall states; both tables are checked once against the kit's
   `ether` and `wallStates` (`etherWords_spec`, `wallTable_spec`). The light cone of [WhiteGap](WhiteGap.md)
   (`drv_cone`) carries the conclusion to every half that agrees on cells $1, \dots, t + k + 13$.
2. Induction on the number of blocks, with the center's period four.
3. A half white on cells $1, \dots, 30$ enters by assumption. Otherwise let $p_1 \le 30$ be its first black cell. If it
   has no other black cell up to $t + k + 13$, it agrees with $\{p_1\}$ there and enters by statement 1. Otherwise let
   $p_2$ be its second black cell. With at most two black cells among cells $1, \dots, G$, it agrees with $\{p_1, p_2\}$
   on cells $1, \dots, G$, and so on cells $1, \dots, t' + k' + 13$, and enters by statement 1.
4. The halves white on cells $1, \dots, 30$ enter by [WhiteGap](WhiteGap.md) (`high_0001`, `high_0011`,
   `high_0111`). The kernel replays the entries of the 360 halves of one cell, 30 positions in 4 phases of 3 words, and
   of the 23,509 halves of two cells that statement 3 needs: one kernel computation per word, phase and first black
   cell (`cell0001_0_1` to `cell0111_3_30`). One cell enters by step 405, two by step 1,344. The certificates are packed
   17 bits an entry and come from [computations/sparse_halves.py](../../computations/sparse_halves.py).
5. Entry puts column 1 in the ether at the white times of the center, which the kit's masked Jen for finite
   configurations forbids beside a center of period four (`no_finite_of_family` of [EmptyRight](EmptyRight.md)).

## What it covers

A finite right half that never enters the family, if one exists, has at least three black cells among cells
$1, \dots, G$ (statement 4), a black cell among cells $7, \dots, B$ and one among cells $1, \dots, 30$
([WhiteGap](WhiteGap.md)). The case split proves more than statement 4: a half whose first two black cells are $p_1$ and
$p_2$ enters whenever its third lies beyond $t' + k' + 13$ for that pair, and the bound $G$ is the largest of these.
Three black cells by the same route would need a kernel check of each triple whose third cell lies below the bound
of its pair: 186,395 halves for $0001$ at phase 0, 476,314 for $0011$ at phase 1 and 32,219 for $0111$ at phase 2,
against 23,509 pairs for all twelve words and phases together.

## Relation to the kit

The kit's `Rule30EtherSingleCell.singleCell_absorption` proves one black cell for $0001$, by a check of the positions
1 to 30 (`small_case`) and its `absorption_high` beyond; statement 4 gives it for all three words and adds the second
cell. The
family, the trap and masked Jen are the kit's
([`Rule30Ether`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Ether.lean)),
and the packed half is the kit's `Rule30EtherThree.rowN`, identified with the driven half by its `rowN_eq_drv`.

## Lean

`Rule30Open.Columns.SparseRight`: `stepK`, `quads`, `stateAt` and `stateAt_eq` for the packed half; `etherWords`,
`wallTable`, `fastFamily` and `inFamily_of_fast` for the family; `entryOK`, `pairsOK`, `cellOK` and their specs for the
certificates; `AtMostTwo`, `first_black`, `all30` and `two_absorption` for the case split; the data
`cells<word>_<phase>` with their kernel checks; `sparse_*`, `oneCell_*`, `SparseRight` and `sparseRight_*`. The
module builds in about 4 minutes with a peak of about 2 GB.
