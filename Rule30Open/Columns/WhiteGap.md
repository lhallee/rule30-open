---
title: A right half white past its first six cells enters the ether-and-wall family, whatever lies beyond the gap
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.WhiteGap
headline: [drv_cone, inFamily_of_check_cone, gap_absorption, gap_0001, gap_0011, gap_0111, gapRight_0001, gapRight_0011, gapRight_0111, high_0011, high_0111]
kit: refines
kit_modules: [Rule30Ether, Rule30EtherSingleCell]
---

# A right half white past its first six cells enters the ether-and-wall family, whatever lies beyond the gap

The kit reduces least period four for the center column to attraction: every finite right half, driven by the word,
enters its ether-and-wall family (the open `Rule30Ether.Absorption`). [EmptyRight.md](EmptyRight.md) checks entry for
every right half of at most six cells, and the kit proves it for one black cell and, for $0001$, for every half white
on cells 1 to 30. Here the light cone joins the two kinds of result: a small half's entry survives any cells added far
enough to its right.

## Statement

Drive a right half $x$, cells $1, 2, \dots$ beside the center, with the center repeating a word $w$ of period four from
phase $\varphi$.

1. **The light cone** (`drv_cone`). Column $p$ at time $t$ depends only on the initial cells $1, \dots, p + t$.
2. **Entry travels along it** (`inFamily_of_check_cone`, `gap_absorption`). If a half $r$ is in the family at step
   $t_1$ with depth $k$, every half that agrees with $r$ on cells $1, \dots, t_1 + k + 13$ is in it at step $t_1$.
3. **Absorption across a white gap** (`gap_0001`, `gap_0011`, `gap_0111`). Every right half whose cells $7, \dots, B$
   are white enters the family, in every phase, whatever its first six cells and its cells beyond $B$, with $B = 316$
   for $0001$, $535$ for $0011$ and $310$ for $0111$.
4. **The exclusion** (`gapRight_0001`, `gapRight_0011`, `gapRight_0111`). No finite configuration whose cells
   $7, \dots, B$ are white has a center column that repeats the word, whatever its left half.
5. **White on cells 1 to 30** (`high_0011`, `high_0111`, and `high_0001`). Every right half white on cells
   $1, \dots, 30$ enters the family, for each of the three words.

## Argument

1. By induction on $t$: cell $p + 1$ at time $t + 1$ reads cells $p$, $p + 1$ and $p + 2$ at time $t$, whose cones
   reach at most cell $p + 2 + t$; column 0 is the prescribed center.
2. The family condition at step $t_1$ reads columns $1, \dots, k + 13$: the ether on $1, \dots, k$ and a wall state on
   the next 13. By statement 1 those cells agree for the two halves. Since the family is a trap
   (`Rule30Ether.trap_invariant`), what the far cells do afterwards cannot undo entry.
3. Every half of at most six cells passes a kernel-checked entry at a listed step and depth
   ([EmptyRight.md](EmptyRight.md), `check0001_0` to `check0111_3`), and every listed step plus depth plus 13 is at most
   $B$ (`bound0001`, `bound0011`, `bound0111`, by `decide`). A half white on cells $7, \dots, B$ agrees up to cell $B$
   with the half of its first six cells (`pack_gap`), so statement 2 applies. The phase matters only modulo 4
   (`inFamily_phase`, `gap_phase`).
4. Entry puts column 1 in the ether at the white times of the center, which the kit's masked Jen for finite
   configurations forbids beside a center of period four (`no_finite_of_family` of [EmptyRight.md](EmptyRight.md)).
5. The white half enters by step 16 at depth at most 3, and step plus depth plus 13 is at most 30 in every phase and
   for every word.

## What it covers

A finite right half that never enters the family, if one exists, has a black cell among cells $7, \dots, B$
(statement 3) and one among cells $1, \dots, 30$ (statement 5), and at least three among its first cells
([SparseRight.md](SparseRight.md), which also proves one black cell anywhere for all three words). The bound $B$ comes from the latest entry among the
halves of six cells; the census of every half of up to 20 cells ([absorption census](../../findings/columns/absorption-census.md))
gives, by the same argument, white gaps after cell 20 of length about the latest entry there, about 2,000 steps, but
that census is computed and not yet in Lean.

## Relation to the kit

The kit's `Rule30EtherSingleCell.absorption_high` is statement 5 for $0001$, proved there by tracking the white half;
here it follows for all three words from the checked entries and the light cone. The family, the trap and masked Jen
are the kit's ([`Rule30Ether`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Ether.lean)).
The light cone of the driven half (statement 1) refines the kit's `drv_congr`, which asks for agreement on every cell.
