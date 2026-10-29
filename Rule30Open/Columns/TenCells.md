---
title: A right half white past its first ten cells enters the ether-and-wall family, whatever lies beyond the gap
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.TenCells
headline: [ten_absorption, ten_0001, ten_0011, ten_0111, tenRight_0001, tenRight_0011, tenRight_0111, smallTen_0001, smallTen_0011, smallTen_0111]
kit: refines
kit_modules: [Rule30Ether, Rule30EtherSingleCell]
evidence: [computations/small_halves.py]
---

# A right half white past its first ten cells enters the ether-and-wall family, whatever lies beyond the gap

The kit reduces least period four for the center column to attraction: every finite right half, driven by the word,
enters its ether-and-wall family (the open `Rule30Ether.Absorption`). [EmptyRight](EmptyRight.md) checks every right
half of at most six cells, and [WhiteGap](WhiteGap.md) carries each check along the light cone to every half white
past its first six cells. Here the same is done for every right half of at most ten cells, with the faster kernel
check of [SparseRight](SparseRight.md).

## Statement

Drive a right half $x$, cells $1, 2, \dots$ beside the center, with the center repeating a word $w$ of period four from
phase $\varphi$.

1. **Absorption across a white gap after ten cells** (`ten_0001`, `ten_0011`, `ten_0111`). Every right half whose
   cells $11, \dots, G$ are white enters the family, in every phase, whatever its first ten cells and its cells beyond
   $G$, with $G = 562$ for $0001$, $654$ for $0011$ and $371$ for $0111$.
2. **The exclusion** (`tenRight_0001`, `tenRight_0011`, `tenRight_0111`). No finite configuration whose cells
   $11, \dots, G$ are white has a center column that repeats the word, whatever its left half.
3. **Ten cells** (`smallTen_0001`, `smallTen_0011`, `smallTen_0111`). In particular no finite configuration whose right
   half has at most ten cells has such a center column.

## Argument

1. The kernel checks, for each word and phase, that every right half $r < 2^{10}$ is in the family at a listed step
   $t$ and depth $k$, with $t + k + 13 \le G$ (`halvesOK`, 128 halves to a check, through SparseRight's `entryOK`).
2. Entry at step $t$ and depth $k$ reads only the initial cells $1, \dots, t + k + 13$ (SparseRight's
   `inFamily_of_fast`, from the light cone `drv_cone` of WhiteGap). A half white on cells $11, \dots, G$ agrees there
   with the half $r$ of its first ten cells (WhiteGap's `pack_gap`), so it enters with $r$ (`ten_absorption`).
3. Entry puts column 1 in the ether at the white times of the center, which the kit's masked Jen for finite
   configurations forbids beside a center of period four (WhiteGap's `gapRight_of_absorption`).

The 12,288 entries come from [computations/small_halves.py](../../computations/small_halves.py). The latest entry is
at step 546 for $0001$, 639 for $0011$ and 358 for $0111$, and the deepest at depth 17; for $0001$ and $0011$ the
latest entry and the bound $G$ are already reached by halves of at most eight cells.

## What it covers

Statement 1 neither contains nor is contained in WhiteGap's: it allows any cells 7 to 10 and asks for white cells up
to a larger $G$. Together with [SparseRight](SparseRight.md) and [EtherPrefix](EtherPrefix.md), a finite right half that
never enters the family, if one exists, has at least three black cells among its first cells, a black cell among
cells 7 to $B$ and one among cells 11 to $G$, and is not a truncated aligned ether with a tail of at most four cells.
The census of [the absorption finding](../../findings/columns/absorption-census.md) shows entry for every half of at
most 20 cells; the kernel check grows with the number of halves, about 45 seconds for the $2^{10}$ here.

## Relation to the kit

The family, the trap, the alignments and masked Jen are the kit's
([`Rule30Ether`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Ether.lean)),
and the packed half is its `Rule30EtherThree.rowN`. The kit proves entry for one black cell under $0001$ and, for
$0001$, for every half white on cells 1 to 30 (`Rule30EtherSingleCell`).

## Lean

`Rule30Open.Columns.TenCells`: `halvesOK` and `halvesOK_spec` for the packed entries, `ten_absorption` and `chunks8`
for the gap, the data `halves<word>_<phase>` with their 96 kernel checks, `ten_*`, `smallRight_of_gapRight`,
`tenRight_*` and `smallTen_*`. With sequential elaboration the module builds in under a minute with a peak below
600 MB.
