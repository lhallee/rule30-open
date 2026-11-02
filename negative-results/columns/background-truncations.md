---
title: Truncated backgrounds add no class of halves that enter the carried traps; they are inside at once or refute them
category: columns
problems: [1]
status: negative
kind: refuted
evidence: [computations/background_prefix.py]
---

# Truncated backgrounds add no class of halves that enter the carried traps; they are inside at once or refute them

**Question.** The 340 blocks of periods 9 to 14 that the wall modules carry traps for come down, by
`absorption_excludes` of [WordTraps](../../Rule30Open/Columns/WordTraps.md), to entry into a trap carried leftward from
a wall at the edge of a background periodic in time and space. For period four,
[EtherPrefix](../../Rule30Open/Columns/EtherPrefix.md) proves that every truncation of the aligned ether, then a word of
at most four cells, enters the kit's family, through a shift lemma (seven ether columns in front keep entry, at depth
$k + 7$) and one base per residue modulo 7. The picture to test: the truncations of a block's own background are its
slow halves, they enter its carried trap $T_d$ or a sibling $T_{d + i q}$, and the same shift lemma with $q$ background
columns, $q$ the background's spatial period, gives a Lean class of halves for each block, unless some truncation never
enters, which would refute the block's single-trap hypothesis.

**What was done.** [computations/background_prefix.py](../../computations/background_prefix.py) rebuilds the chain of
each wall of the wall modules, the distance $s$ from which it is periodic and its period $q$, and the background's
columns. For every trap of NineTraps, TenTraps and ElevenTraps to FourteenTraps it compares the background half beside
every column of the trap's block with the trap's states at every label (`inside_counts`), and checks that
$T_{d + q}$ is $T_d$ with $q$ background columns in front (`sibling_identity`). It runs the truncations $x_{K,u}$, the
background on cells $1, \dots, K$, then a word $u$, then white, from every label, vectorized, recording entry into
$T_d$, whether column 1 kept the background's values before entry, and entry into a trap $T_D$ carried to a distance of
another column class whose cut is apart from $T_d$ (`truncation_entry`).

**Outcome.** The picture fails at its first step, in two opposite ways.

- *Inside from the start* ($s = 0$: the walls of periods 10 and 14 and the wall $000110110011$ of period 12, 162 traps).
  The background's window beside the wall's column is a state of the wall at every label, so beside every aligned column
  the background half is a state of the block's trap, and every truncation at least as long as the trap is in it at step
  0, whatever follows. For `ten0`, of the 144,150 truncations with $K = 1, \dots, 465$ (three periods), $u$ of at most
  four cells and all ten labels, all enter within 50,000 steps: 140,549 at step 0, every one with $K \ge 16$, and the
  latest at step 2,615. For `ten1`, of $0001001101$, beside its aligned columns 142,863 of the 144,150 truncations enter
  within 50,000 steps, 140,239 at step 0 (every one with $K \ge 17$) and the latest at step 49,934, and 1,287 shorter
  than the trap do not; beside its other columns, which no symmetry maps to the aligned ones, 137,512 are inside the
  apart sibling $T_{18}$ (the latest from step 40,553 on), 2,779 enter `ten1` and 3,859 neither. For `ten23`, of
  $0000000001$, 135,961 enter, 133,419 at step 0 (every one with $K \ge 39$) and the latest at step 575, and 8,189
  shorter than the trap do not within 50,000 steps, as the trap's failure of the test of reach allows. The runs took a
  few seconds for `ten0`, about 43 minutes for `ten1` and 32 for `ten23`, with one process each. No shift lemma or base
  is needed, and the class adds nothing beyond the trap's own states:
  [BackgroundPrefix](../../Rule30Open/Columns/BackgroundPrefix.md) proves the exclusion for all 162 traps from the
  window alone.
- *Apart from the trap* ($s > 0$: the walls of periods 9 and 13, both of period 11, and $001011100111$ and
  $000010011111$ of period 12). The background half beside a column of the block is a state of $T_d$ at no label, and
  the wall carried to $D = x + i q$, with $D - s$ at least the trap's width, is a trap of the block apart from $T_d$.
  Entry into $T_d$ is false for every trap whose block is a column of the background, 104 traps, and for three more
  blocks at $s = 0$ beside their other columns, two of period 10 and one of period 14: 107 in all, 41 of them not
  refuted before, checked in Lean in [BackgroundSiblings](../../Rule30Open/Columns/BackgroundSiblings.md). For the three
  blocks tested at $s > 0$, the trap and its siblings with $i \le 2$ are pairwise apart, so no list drawn from them is a
  hypothesis that could hold; that this goes on for every $i$ is untested. Within 5,000 steps the truncations mostly
  stay out of both the trap and its apart siblings. Beside a column of $001001101$ (`nine8`, $s = 10$, $q = 135$), of
  the 8,505 truncations with $K = 1, \dots, 135$, $u$ of at most two cells and all nine labels, 11 enter `nine8` (the
  latest at step 2,035), none is in an apart sibling and 8,494 are in neither. Beside a column of $00010111011$
  (`el1_9`, $s = 9$, $q = 275$), of the 7,700 with $K = 1, \dots, 100$, 11 enter, 22 are in an apart sibling and 7,667
  in neither. Beside a column of $0010110110011$ (`th0_11`, $s = 1$, $q = 689$), of the 9,100 with $K = 1, \dots, 100$,
  3,392 enter `th0_11` (the latest at step 477, each with column 1 on the background until it enters), 214 are in the
  apart sibling $T_{64}$ and 5,494 in neither. Whatever closed sets the halves in neither settle into, the run does not
  identify them.

**Where it stops, and why.** The shift lemma needs a background half that is outside the trap while the trap's
siblings, each one background period deeper, are entered: the ether's situation, where the wall forms at the boundary
of a truncation and column 1 never sees it. The backgrounds of the wall modules are not in that situation. Either the
wall is part of the background ($s = 0$), so its half is inside every carried trap and the truncations are trivially
inside, or the chain has a transient of $s$ columns between the wall and the background ($s > 0$), so the background
half carries no transient and each sibling is a closed set apart from the trap. In the second case the hypothesis
the route was to serve is false, and the natural replacement is entry into the whole family $\{T_{x + i q}\}$, the
form of the kit's ether-and-wall family; within 5,000 steps most truncations of the backgrounds of periods 9, 11 and
13 enter neither it nor the trap.

**What it means.** For the 162 traps at $s = 0$, a right half that begins with the background is already excluded, so
the open entry question for them is about halves that differ from the background in their first cells, as
[TenGap](../../Rule30Open/Columns/TenGap.md) and [WallGaps](../../Rule30Open/Columns/WallGaps.md) treat. For the walls
with $s > 0$, each block of the background keeps at most entry into some trap of the block
(`WTrap.AbsorptionAny` of [Traps001](../../Rule30Open/Columns/Traps001.md)) or into an infinite carried family, and a
proof of entry for those blocks would have to name the family, as the kit does for period four.

**Reproduce.**

```bash
python -m computations.background_prefix --walls
python -m computations.background_prefix --siblings
python -m computations.background_prefix --truncate ten --kmax 465 --tail 4 --steps 50000
python -m computations.background_prefix --truncate NineTraps --names nine8 --kmax 135 --tail 2 --steps 5000
python -m computations.background_prefix --truncate ElevenTraps --names el1_9 --kmax 100 --tail 2 --steps 5000
python -m computations.background_prefix --truncate ThirteenTraps --names th0_11 --kmax 100 --tail 2 --steps 5000
```

The first two take a few seconds each; the truncations of `ten0`, `ten1` and `ten23` about 75 minutes with one
process, since the short truncations that do not enter run to the step limit, and the last three about three minutes
each.
