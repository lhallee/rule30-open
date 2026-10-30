---
title: A right half white past its first fourteen cells enters the ether-and-wall family, whatever lies beyond the gap
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.FourteenCells
headline: [fourteen_absorption, fourteen_0001, fourteen_0011, fourteen_0111, fourteenRight_0001, fourteenRight_0011, fourteenRight_0111, smallFourteen_0001, smallFourteen_0011, smallFourteen_0111]
kit: refines
kit_modules: [Rule30Ether, Rule30EtherSingleCell]
evidence: [computations/small_halves.py]
---

# A right half white past its first fourteen cells enters the ether-and-wall family, whatever lies beyond the gap

The kit reduces least period four for the center column to attraction: every finite right half, driven by the word,
enters its ether-and-wall family (the open `Rule30Ether.Absorption`). [TwelveCells](TwelveCells.md) checks every right
half of at most twelve cells and carries each check along the light cone to every half white past its first twelve
cells. Here the same is done for every right half of at most fourteen cells.

## Statement

Drive a right half $x$, cells $1, 2, \dots$ beside the center, with the center repeating a word $w$ of period four from
phase $\varphi$.

1. **Absorption across a white gap after fourteen cells** (`fourteen_0001`, `fourteen_0011`, `fourteen_0111`). Every
   right half whose cells $15, \dots, G$ are white enters the family, in every phase, whatever its first fourteen cells
   and its cells beyond $G$, with $G = 750$ for $0001$, $1{,}446$ for $0011$ and $560$ for $0111$.
2. **The exclusion** (`fourteenRight_0001`, `fourteenRight_0011`, `fourteenRight_0111`). No finite configuration whose
   cells $15, \dots, G$ are white has a center column that repeats the word, whatever its left half.
3. **Fourteen cells** (`smallFourteen_0001`, `smallFourteen_0011`, `smallFourteen_0111`). In particular no finite
   configuration whose right half has at most fourteen cells has such a center column.

## Argument

The argument of [TwelveCells](TwelveCells.md), with fourteen cells:

1. The kernel checks, for each word and phase, that every right half $r < 2^{14}$ is in the family at a listed step $t$
   and depth $k$, with $t + k + 13 \le G$ (TenCells' `halvesOK`, 128 halves to a check, through
   [SparseRight](SparseRight.md)'s `entryOK`); TwelveCells' `chunks_cover` gathers the 128 chunks of each word and
   phase.
2. Entry at step $t$ and depth $k$ reads only the initial cells $1, \dots, t + k + 13$, so a half white on cells
   $15, \dots, G$ enters with the half $r$ of its first fourteen cells (`fourteen_absorption`).
3. Entry puts column 1 in the ether at the white times of the center, which the kit's masked Jen for finite
   configurations forbids beside a center of period four (WhiteGap's `gapRight_of_absorption`).

The 196,608 entries come from [computations/small_halves.py](../../computations/small_halves.py). The latest entry is at
step 734 for $0001$, 1,432 for $0011$ and 547 for $0111$, and the deepest at depth 17, against 734, 980 and 547 for the
halves of at most twelve cells, so only $0011$ needs a larger $G$. The module runs 1,536 kernel checks and builds in
about 12 minutes with a peak near 600 MB.

## What it covers

For $0001$ and $0111$, with the same $G$ as TwelveCells, statement 1 contains TwelveCells' first statement, since it
allows any cells 13 and 14. For $0011$ it asks for white cells up to a larger $G$, so neither contains the other.
Statement 3 contains TwelveCells' third. [The absorption
census](../../findings/columns/absorption-census.md) shows entry for every half of at most 20 cells by computation;
each two more cells multiply the kernel's work by about four.

## Relation to the kit

The family, the trap, the alignments and masked Jen are the kit's
([`Rule30Ether`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Ether.lean)),
and the packed half is its `Rule30EtherThree.rowN`. The kit proves entry for one black cell under $0001$ and, for
$0001$, for every half white on cells 1 to 30 (`Rule30EtherSingleCell`).

## Lean

`Rule30Open.Columns.FourteenCells`: `fourteen_absorption`, the data `fourteen<word>_<phase>` with their 1,536 kernel
checks and the covers `fourteenCover<word>_<phase>`, `fourteen_*`, `fourteenRight_*` and `smallFourteen_*`.
