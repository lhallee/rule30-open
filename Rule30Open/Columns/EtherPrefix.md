---
title: Every truncation of the aligned ether, followed by a short word, enters the ether-and-wall family
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.EtherPrefix
headline: [shift7_drv, shift7_family, prefix_absorption, etherPrefix_0001, etherPrefix_0011, etherPrefix_0111, prefixRight_0001, prefixRight_0011, prefixRight_0111]
kit: refines
kit_modules: [Rule30Ether, Rule30EtherThreeReach]
evidence: [computations/ether_prefix.py]
---

# Every truncation of the aligned ether, followed by a short word, enters the ether-and-wall family

The kit reduces least period four for the center column to attraction: every finite right half, driven by the word,
enters its ether-and-wall family (the open `Rule30Ether.Absorption`). The ether itself, aligned with the word, is a
right half that never enters: it keeps its period and never forms a wall. In
[the absorption census](../../findings/columns/absorption-census.md) it is the only infinite half seen to stay out, so
the finite halves that look like it for a long stretch are the natural candidates for slow entry. They all enter.

## Statement

Drive a right half $x$, cells $1, 2, \dots$ beside the center, with the center repeating a word $w$ of least period four
from phase $\varphi$, and let $e_t(p)$ be the ether aligned with the drive through one of the kit's alignments $(j_0, s)$
of $w$: column $p$ at time $t$ is the ether column $j_0 + p$ at phase $t + s + \varphi$, and column 0 is the drive.

1. **Seven columns of ether in front** (`shift7_drv`). Let $y$ be $x$ behind seven columns of the aligned ether: cells
   $1, \dots, 7$ of $y$ are $e_0(1), \dots, e_0(7)$ and cell $p + 7$ of $y$ is cell $p$ of $x$. If column 1 of $x$ is
   $e_t(1)$ at every step $t < T$, then up to step $T$ columns $0, \dots, 7$ of $y$ are the ether and column $p + 7$ of
   $y$ is column $p$ of $x$.
2. **Entry survives the shift** (`shift7_family`). If moreover $x$ is in the family at step $T$ through the alignment
   $(j_0, s)$ at depth $k$, then $y$ is in it at step $T$ at depth $k + 7$, and column 1 of $y$ is again the ether's
   before $T$. So the same holds after any number of shifts.
3. **Truncated ether** (`prefix_absorption`). Let $x_{K,u}$ be the aligned ether on cells $1, \dots, K$, then a word
   $u$, then white. Given a base for each residue of $K$ modulo 7, a truncation length at which statement 2 applies,
   and a direct check of every shorter truncation, $x_{K,u}$ enters the family for every $K$.
4. **The three words** (`etherPrefix_0001`, `etherPrefix_0011`, `etherPrefix_0111`). For each word, each of its
   alignments and every phase, $x_{K,u}$ enters the family for every $K$ and every word $u$ of at most four cells.
5. **The exclusion** (`prefixRight_0001`, `prefixRight_0011`, `prefixRight_0111`). No finite configuration whose right
   half is such an $x_{K,u}$ has a center column that repeats the word, whatever its left half.

## Argument

1. By induction on the step. Columns $1, \dots, 6$ of $y$ read only columns $0, \dots, 7$, which are the ether, and the
   ether is a rule-30 orbit (`Rule30Ether.ether_rule`). Column 7 reads column 8, which is column 1 of $x$, the ether's
   by assumption, and the ether has spatial period 7. Column $p + 7$ of $y$ reads columns $p + 6$ to $p + 8$, which are
   columns $p - 1$ to $p + 1$ of $x$; for $p = 1$, column 7 of $y$ is the ether column $j_0 + 7$, the drive's.
2. At step $T$ columns $1, \dots, 7$ of $y$ are the ether, columns $8, \dots, k + 7$ are columns $1, \dots, k$ of $x$,
   the ether moved by its period, and the 13 columns after them are the same wall state; $j_0 + k + 7 \equiv 2$ modulo
   7 as before. Column 1 of $y$ is among the first seven, the ether's.
3. Every $K \ge B$ is a base length in $B, \dots, B + 6$ plus a multiple of 7, and $x_{K,u}$ is the base half behind
   that many blocks of seven ether columns. The kernel checks each base, its entry through its own alignment and its
   clean column 1 (`baseOK`), on the packed half stepped by the kit's `Rule30EtherThree.rowN`, and each shorter
   truncation's entry through any alignment with the mask check of [SparseRight](SparseRight.md) (`entryOK`).
4. For the 24 pairs of alignment and phase and the 16 words of at most four cells, $B$ is at most 44, the bases enter
   by step 222 and the shorter truncations by step 688. The certificates come from
   [computations/ether_prefix.py](../../computations/ether_prefix.py), one kernel computation per alignment and phase
   (`tails0001_5_0_ok` and the others).
5. As in [EmptyRight](EmptyRight.md): entry puts column 1 in the ether at the white times of the center, which the
   kit's masked Jen for finite configurations forbids beside a center of period four (`no_finite_of_family`).

## What it covers

The truncation point is unbounded, so these halves have any number of cells, between 1 and 6 of every 7 of them black by
phase. A long truncation enters at a step that depends only on its length modulo 7: its boundary sends a disturbance
into the ether, which leaves a wall a fixed distance from the boundary, at most 37 cells behind it for the white tail,
while column 1 never sees it. A short one may enter only through another alignment. The argument does not reach the
infinite ether, which has no boundary to send the wall. Nor does it reach the halves that enter last in the census: the
three slowest halves of 16 cells for each word and phase agree with a rotation of the ether on at most their first 7
cells (`python -m computations.ether_prefix --slowest 16`), so their delay comes from elsewhere. Together with
[SparseRight](SparseRight.md) and [WhiteGap](WhiteGap.md), a finite right half that never enters, if one exists, has at
least three black cells among its first cells, a black cell among cells 7 to $B$, and is not a truncated aligned ether
with a tail of at most four cells.

## Relation to the kit

The family, the trap, the alignments and masked Jen are the kit's
([`Rule30Ether`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Ether.lean)),
and the packed half is its `Rule30EtherThree.rowN`. The kit shows that the pure ether lies in no trap of width at most
20 and that some finite halves stay in deeper members of the family forever (`never_enters_S0001`); the shift lemma
is what turns entry at one truncation length into entry at all of them.

## Lean

`Rule30Open.Columns.EtherPrefix`: `shift7`, `shift7_drv`, `shift7_family`, `shiftN` and `shiftN_family` for the shift;
`prefixHalf`, `shiftN_prefix`, `packHalf` and `testBit_packHalf` for the truncated ether; `cleanCheck`, `baseOK`,
`directN`, `basesN`, `tailOK`, `tailsOK` and their specs for the certificates; `prefix_absorption` and
`prefix_of_tails`; the data `tails<word>_<j0>_<phase>` with their kernel checks; `etherPrefix_*`, `PrefixRight` and
`prefixRight_*`. The module builds in about 2 minutes with a peak below 1 GB.
