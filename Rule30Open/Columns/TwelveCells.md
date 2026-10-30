---
title: A right half white past its first twelve cells enters the ether-and-wall family, whatever lies beyond the gap
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.TwelveCells
headline: [twelve_absorption, twelve_0001, twelve_0011, twelve_0111, twelveRight_0001, twelveRight_0011, twelveRight_0111, smallTwelve_0001, smallTwelve_0011, smallTwelve_0111]
kit: refines
kit_modules: [Rule30Ether, Rule30EtherSingleCell]
evidence: [computations/small_halves.py]
---

# A right half white past its first twelve cells enters the ether-and-wall family, whatever lies beyond the gap

The kit reduces least period four for the center column to attraction: every finite right half, driven by the word,
enters its ether-and-wall family (the open `Rule30Ether.Absorption`). [TenCells](TenCells.md) checks every right half
of at most ten cells and carries each check along the light cone to every half white past its first ten cells. Here
the same is done for every right half of at most twelve cells.

## Statement

Drive a right half $x$, cells $1, 2, \dots$ beside the center, with the center repeating a word $w$ of period four from
phase $\varphi$.

1. **Absorption across a white gap after twelve cells** (`twelve_0001`, `twelve_0011`, `twelve_0111`). Every right half
   whose cells $13, \dots, G$ are white enters the family, in every phase, whatever its first twelve cells and its
   cells beyond $G$, with $G = 750$ for $0001$, $995$ for $0011$ and $560$ for $0111$.
2. **The exclusion** (`twelveRight_0001`, `twelveRight_0011`, `twelveRight_0111`). No finite configuration whose cells
   $13, \dots, G$ are white has a center column that repeats the word, whatever its left half.
3. **Twelve cells** (`smallTwelve_0001`, `smallTwelve_0011`, `smallTwelve_0111`). In particular no finite configuration
   whose right half has at most twelve cells has such a center column.

## Argument

The argument of [TenCells](TenCells.md), with twelve cells:

1. The kernel checks, for each word and phase, that every right half $r < 2^{12}$ is in the family at a listed step $t$
   and depth $k$, with $t + k + 13 \le G$ (TenCells' `halvesOK`, 128 halves to a check, through
   [SparseRight](SparseRight.md)'s `entryOK`); `chunks_cover` gathers the 32 chunks of each word and phase.
2. Entry at step $t$ and depth $k$ reads only the initial cells $1, \dots, t + k + 13$, so a half white on cells
   $13, \dots, G$ enters with the half $r$ of its first twelve cells (`twelve_absorption`).
3. Entry puts column 1 in the ether at the white times of the center, which the kit's masked Jen for finite
   configurations forbids beside a center of period four (WhiteGap's `gapRight_of_absorption`).

The 49,152 entries come from [computations/small_halves.py](../../computations/small_halves.py). The latest entry is at
step 734 for $0001$, 980 for $0011$ and 547 for $0111$, and the deepest at depth 17, against 546, 639 and 358 for the
halves of at most ten cells. The module runs 384 kernel checks and builds in about 180 seconds with a peak near 400 MB.

## What it covers

Statement 1 neither contains nor is contained in TenCells' first statement: it allows any cells 11 and 12 and asks for
white cells up to a larger $G$. Statement 3 contains TenCells' third. [The absorption
census](../../findings/columns/absorption-census.md) shows entry for every half of at most 20 cells by computation;
each two more cells multiply the kernel's work by about four.

## Relation to the kit

The family, the trap, the alignments and masked Jen are the kit's
([`Rule30Ether`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Ether.lean)),
and the packed half is its `Rule30EtherThree.rowN`. The kit proves entry for one black cell under $0001$ and, for
$0001$, for every half white on cells 1 to 30 (`Rule30EtherSingleCell`).

## Lean

`Rule30Open.Columns.TwelveCells`: `chunks_cover` and `twelve_absorption`, the data `twelve<word>_<phase>` with their
384 kernel checks and the covers `twelveCover<word>_<phase>`, `twelve_*`, `twelveRight_*` and `smallTwelve_*`.
