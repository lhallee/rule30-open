---
title: Every right half that begins with the background is in 162 carried traps of periods 10, 12 and 14 from step 0
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.BackgroundPrefix
headline: [ten_background_prefix, twelve_background_prefix, fourteen_background_prefix, prefixRightW_of_bg, tenRing_ok, twelveRing_ok, fourteenRing_ok]
kit: new
kit_modules: [Rule30Ether, Rule30EtherThreeTrap]
evidence: [computations/background_prefix.py]
---

# Every right half that begins with the background is in 162 carried traps of periods 10, 12 and 14 from step 0

For period four the aligned ether is a right half that never enters the kit's ether-and-wall family, and its truncations
are the natural slow halves: [EtherPrefix](EtherPrefix.md) proves that they all enter, through a shift lemma and one
base per residue modulo 7. The wall modules of periods 9 to 14 carry a wall leftward along a chain that ends in a
background periodic in time and space, as the kit's wall ends in the ether. For three of these walls the analogy breaks
at the first step: the chain is periodic from the wall's own column, and the background's window beside that column is
already a state of the wall. So beside every column of the background aligned with a block's distance, the background
half is a state of the block's carried trap at every label, and so is every right half that begins with it. The
truncations need no shift lemma and no base: those at least as long as the trap are in it at step 0.

## Statement

Let a background of period $m$ be given by its rows on a ring of $q$ cells, one row per label, and let $p$ be the
position of a column that repeats the block $b$ of a trap $C$ of $K$ cells.

1. **The rings** (`ringOK`, `tenRing_ok`, `twelveRing_ok`, `fourteenRing_ok`). Each row, stepped once by Rule 30 on the
   ring, is the next row, and the last steps to the first: the backgrounds of period 10 on 155 cells, 12 on 138 and 14
   on 728 are orbits of the rule.
2. **Beginning with the background** (`prefixRightW_of_bg`, `background_prefix_of`). If the column at $p$ reads $b$ at
   phase $\varphi$ from label $l$ (`readsAt`) and the $K$ cells right of it at label $l$ (`bgWin`) are a state of $C$
   whose label reads $\varphi$, then no finite configuration whose cells $1, \dots, K$ are those cells has a center
   column that repeats $b$ from phase $\varphi$ (`PrefixRightW` of [TenGap](TenGap.md)), whatever its other cells.
3. **The three walls** (`ten_background_prefix`, `twelve_background_prefix`, `fourteen_background_prefix`). For each of
   the 25 traps of [TenTraps](TenTraps.md), the 36 of [TwelveTraps](TwelveTraps.md) carried from $000110110011$ and the
   101 of [FourteenTraps](FourteenTraps.md), each column of the ring aligned with it (5, 3 and 7 columns) and each
   label, the column reads the trap's block at some phase and statement 2 applies: 1,250, 1,296 and 9,898 cases.

In particular, for every $K' \ge K$ and every word $u$ of any length, the truncation $x_{K', u}$ (the background on
cells $1, \dots, K'$, then $u$, then white) is excluded: no finite configuration whose right half at an onset of the
block is $x_{K', u}$ has a center column that repeats the block, whatever its left half.

## Argument

1. **The chains are periodic from the wall.** Carried leftward, the wall's chain becomes periodic from a distance $s$
   ([the backgrounds](../../findings/columns/space-time-backgrounds.md)); for the walls $0000010001$, $000110110011$ and
   $00011100101011$, $s = 0$ (`background` in
   [computations/background_prefix.py](../../computations/background_prefix.py)). The wall's column is then a column of
   the background, and the background continues to its right.
2. **The window is in the wall.** At each label, the background's window of 16 cells beside the wall's column is a state
   of the wall (computed by `inside_counts`, and checked by the kernel through `bgOK`). Carrying puts the same chain
   columns in front of the wall's states and of the background's window, so beside the column at distance $d$ the
   background's window of $d + 16$ cells is a state of the trap carried to $d$, and so beside every column that the
   background's symmetries map to it: its glide, a shift by a fifth of the ring and a shift in time for period 10.
3. **No run is needed.** A half whose first $K$ cells are a state of the trap at the right phase is in the trap at step
   0, and `prefixRightW_of_entry` of [TenGap](TenGap.md) with $T = 0$ turns that into the exclusion, through the trap's
   check and Jen's theorem on adjacent columns ([WordTraps](WordTraps.md)). The kernel checks the rings, the phases and
   the windows from the rows themselves (`bgOK`), so the chain and the search are not trusted.

## What it covers

The truncations at least as long as the trap are not slow halves: they are in it at step 0. The shorter ones are small
halves of the kind [TenGap](TenGap.md) runs, and some are slow. For the wall of period 10 itself, `ten0`, all 144,150
truncations beside its column, $K = 1, \dots, 465$ (three spatial periods), every $u$ of at most four cells and all ten
labels, enter within 50,000 steps: 140,549 at step 0, every one with $K \ge 16$, and the latest at step 2,615, a
truncation shorter than the trap (`python -m computations.background_prefix --truncate ten`). The shift lemma's base
length, the largest over the residues of $K$ modulo 155 of the least $K$ whose truncations all enter with column 1 on
the background before entry, is 165, since some of the 15 shortest residues enter only after column 1 has left the
background; it plays no role, as every $K \ge 16$ is in at step 0. For `ten1`, of $0001001101$, beside its aligned
columns 142,863 of the 144,150 truncations enter within 50,000 steps, 140,239 at step 0 (every one with $K \ge 17$) and
the latest at step 49,934, and 1,287 shorter than the trap do not; beside its other columns, which no symmetry maps to
the aligned ones, 137,512 are inside the apart sibling $T_{18}$ (the latest from step 40,553 on), 2,779 enter `ten1` and
3,859 neither. For `ten23`, of $0000000001$, 135,961 enter, 133,419 at step 0 (every one with $K \ge 39$) and the latest
at step 575, and 8,189 shorter than the trap do not within 50,000 steps, as the trap's failure of the test of reach
allows. The runs took a few seconds for `ten0`, about 43 minutes for `ten1` and 32 for `ten23`, with one process each.

Two kinds of half lie outside this module. Beside the columns of three blocks that the symmetries do not map to the
aligned ones, $0001001101$ and $0001010111$ of period 10 and $00010010110111$ of period 14, the background half is a
state of the carried trap at no label; there the wall carried farther into the background is a trap of the block apart
from the module's, so entry into the module's trap is false ([BackgroundSiblings](BackgroundSiblings.md)). For the
walls whose chains reach their background only after $s > 0$ columns, of periods 9, 11, 12 and 13, the same holds
beside every column, which refutes entry into every trap of those modules whose block is a column of the background.
So truncated backgrounds give no class of halves that enter beyond the traps' own states: at $s = 0$ they are inside
from the start, and at $s > 0$ the trap's entry is false.

## Relation to the kit

The kit's ether is the background of period 4 that its wall ends in, and the aligned ether is outside its family at
every depth (`Rule30Ether`); entry of its truncations is [EtherPrefix](EtherPrefix.md). The backgrounds here are the
first of the others that are inside their walls. The rings are cycles of the leftward column map, the backgrounds the
kit's equivalent forms count (`evol_add_factorial` in `Rule30Equivalents.PeriodicPoints`). The kit's main branch, after
the pinned commit, adds `Rule30RingOrbits`, a related correspondence between rings that return after $P$ steps, in
the frame moving one cell right per step, and closed walks of $P$-periodic profiles; the kit has no trap for a block of
period 10, 12 or 14.

## Lean

`Rule30Open.Columns.BackgroundPrefix`: `ringStep`, `rowAt`, `ringOK`, `bgWin`, `readsAt`, `bgEntry`, `bgOK`,
`phased_black`, `prefixRightW_of_bg` and `background_prefix_of`; the rings `tenRing`, `twelveRing` and `fourteenRing`
with their checks; the lists `tenBackground`, `twelveBackground` and `fourteenBackground`, each trap with the positions
of its aligned columns and its entries packed 16 bits each, with `_traps` and `_ok`; and the three headline theorems.
It builds in about 90 seconds with a peak of about 4.3 GB. The data come from
`python -m computations.background_prefix --lean-prefix`.

## Reproduce

```bash
python -m computations.background_prefix --walls
python -m computations.background_prefix --lean-prefix
python -m computations.background_prefix --truncate ten --kmax 465 --tail 4 --steps 50000
```

The first prints, for every trap of the wall modules, the chain's start and period and at how many labels the
background half beside each column of its block is in the trap, in a few seconds. The last runs the truncations of
`ten0`, `ten1` and `ten23` in about 75 minutes with one process, nearly all of it for `ten1` and `ten23`, since the
short truncations that do not enter run to the step limit.
[tests/test_background_prefix.py](../../tests/test_background_prefix.py) checks the ring of period 10 against a direct
step on the ring, the prepending of 155 background columns and the background half beside two columns against a run
with integers, the entries of short truncations against a plain run, and the sibling of `nine8` with `apart_closed`.
