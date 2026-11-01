---
title: The game at 15 or 16 cells excludes 00110011111111, 0000000000111011 and 0000101111111001, which nothing else excludes
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.GameBlocksWide
headline: [column_not_00110011111111, center_not_00110011111111, not_eventually_00110011111111, column_not_0000000000111011, center_not_0000000000111011, not_eventually_0000000000111011, column_not_0000101111111001, center_not_0000101111111001, not_eventually_0000101111111001]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/class_blocks_wide.py, computations/class_blocks.py, computations/class_certificate.py, computations/class_survey.py, computations/game.py]
---

# The game at 15 or 16 cells excludes 00110011111111, 0000000000111011 and 0000101111111001, which nothing else excludes

No column of the orbit of a row with a leftmost 1, the center column of the single cell among them, eventually repeats
$00110011111111$, $0000000000111011$ or $0000101111111001$, from any time on and in any rotation. [The finite
game](FiniteGame.md) excludes the first at 16 cells and the other two at 15, and at no width up to 14, so [the game
blocks up to period 16](../../findings/columns/game-blocks.md), which ran the game at widths 6, 10 and 14, miss them;
neither the kit nor any other module of this repository excludes them ([the class-test
survey](../../findings/columns/class-blocks.md)). The proof is the certificate of [ClassGame](ClassGame.md), which
covers the plain game as a special case.

## Statement

For each block $b$ here, with `w` the word `wordOf P 0b<b>`:

- `column_not_<b>`: for a row `init` with a leftmost 1 and any column $k$, there are no $T$ and shift $s$ with `evolve
  init t k = w.getD ((t + s) % P) false` for every $t \ge T$.
- `center_not_<b>`: the same for `Rule30Prize.center`.
- `not_eventually_<b>`: `¬ Rule30StripCertificates.EventuallyWord w`.

## Argument

1. **The game is a case of the class test.** Let column $k$ repeat $b$ of period $P$. The game at width $w$ follows the
   phase and the cells $k + 1, \dots, k + w$ with cell $k + w + 1$ free, and every real row is one play at every width.
   Every move advances the phase by one, so in a strongly connected component every cycle has a length divisible by
   $P$, the gcd $d$ of those lengths is a multiple of $P$, and the phase is a function of the cyclic class. Where the
   game's test holds, the column $k - 1$, which is $b_{\varphi + 1} \oplus (b_\varphi \lor \text{cell } k + 1)$, is a
   function of the phase, hence of the class, and the class test holds. So [ClassGame](ClassGame.md)'s `class_column`,
   which holds for any block with a valid `ClassCert`, proves every block the game excludes.
2. **The certificate.** It gives, width by width, heights under which every play enters a set closed under moves and
   stays there, and on that set at the last width a rank, which no move lowers, and a label modulo the cyclic period of
   each component that can hold a play, which a move inside it raises by one; at such a rank the left column is a
   function of the label. So the play settles in one component, column $k - 1$ repeats with period $d$, and [the
   adjacent-column theorem](AdjacentColumns.md) excludes two adjacent eventually periodic columns.
3. **The least width.** Each certificate is at the least width at which the class test closes the block. For
   $0000000000111011$ and $0000101111111001$ that is 15, the plain game's own least width, and every component that can
   hold a play has cyclic period $P$. For $00110011111111$ it is 13, three cells fewer than the plain game needs: at 13
   cells one component of 72 nodes has cyclic period 28, the left column takes both values at one phase there, which is
   where the plain game fails, and one value on each of its 28 classes.

`computations/class_blocks_wide.py` builds each certificate with `class_certificate.certificate`, renumbers its ranks
with `class_blocks.compact`, and checks every condition node by node in plain Python (`class_certificate.check`) before
writing it.

| block | period | plain game's least width | cells | nodes checked | height 0 at the last width | largest height | ranks | components that can hold a play: nodes (cyclic period) |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| $00110011111111$ | 14 | 16 | 13 | 28,134 | 8,574 | 39 | 262 | 1,633 (14); 166 (14); 124 (14); 72 (28, mixed by phase); 40 (14); 32 (14) |
| $0000000000111011$ | 16 | 15 | 15 | 70,992 | 20,149 | 54 | 114 | 6,666 (16); 83 (16) |
| $0000101111111001$ | 16 | 15 | 15 | 68,352 | 10,217 | 156 | 1 | 10,217 (16) |

"Mixed by phase" marks a component where the left column takes both values at one phase. At one cell fewer the class
test fails for each block (`class_survey.classify`), and the plain game fails at one cell fewer than its least width
(`game.bad_pairs` is 2 for $00110011111111$ at 15 cells, 3 for $0000000000111011$ and 1 for $0000101111111001$ at 14).

## In Lean

`Rule30Open.Columns.GameBlocksWide` has one section per block, written by `class_blocks.block_section`: the tries
`cls<b>L<w>_<phase>` and `cls<b>F_<phase>`, each phase in a definition of its own, the certificate `cls<b>`, one
`decide +kernel` per width and phase and one per phase of the classes, `cls<b>_valid`, and the three theorems, which
apply `class_column`, `center_not_class` and `class_not_eventuallyWord`. The module builds in about 13 minutes with a
peak of about 3.7 GB.

## Relation to the kit and to the other game modules

The kit does not exclude these blocks: its strip-certificate table, its padded words $0^q 1$, $0^r 11$ and $0^q 10111$,
its long runs of 1s and its padding and black-run families do not include them (`game.kit_blocks`). [GameBlocks](GameBlocks.md),
[GameBlocksLong](GameBlocksLong.md) and [BitGame](BitGame.md) check the blocks the game excludes at widths up to 14;
[BitPhases](BitPhases.md) and its sequels check blocks of period 17 to 21 phase by phase at 13 or 14 cells. Neither [WallSets](WallSets.md) nor [limit
windows](../../findings/columns/limit-windows.md) reach these blocks (`class_survey.elsewhere`).
[NaturalTrapsWalls](NaturalTrapsWalls.md) and [FourteenTraps](FourteenTraps.md) hold traps for $00110011111111$, which
hold once the column enters them; the exclusion here is unconditional.

## Reproduce

```bash
python -m computations.class_blocks_wide                                     # every certificate, checked, about 40 s
python -m computations.class_blocks_wide --lean GameBlocksWide > Rule30Open/Columns/GameBlocksWide.lean
lake build Rule30Open.Columns.GameBlocksWide
```
