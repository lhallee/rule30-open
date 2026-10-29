---
title: After nine 1s the next cell stays known through five kinds of segment, excluding infinite families of periods
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.WallSegments
headline: [center_run_family, center_wall_block, center_run_segment, wall_segments_column, run_family_column]
kit: refines
kit_modules: [Rule30BlackRuns, Rule30BlackRunBlocks]
evidence: [computations/wall_segments.py]
---

# After nine 1s the next cell stays known through five kinds of segment, excluding infinite families of periods

[The long-runs theorem](LongRuns.md) excludes every eventual period whose runs of 1s all last at least nine steps:
nine 1s in a column fix the two cells right of it at 0 1, and a run of 0s then keeps the first of them at 1. This
module follows those two cells further, through segments that contain 1s, with three-valued Rule 30. It excludes
every eventual period whose long runs of 1s are separated by segments that the three-valued run follows, a set of
blocks that grows with the period and contains infinite families with short runs of 1s.

## Statement

For a column $x_t$ of the orbit of a row with a leftmost 1, write its eventual period as a block $B$ read cyclically.

1. **Single runs** (`run_family_column`, `center_run_family`). For every $a \ge 9$ and $z \ge 0$, no column repeats
   $1^a\, h\, 0^z\, t$ from any time on, with $h$ one of $0$ and $011$ and $t$ one of the empty word and $10$. These
   are the blocks $1^a 0^b$, $1^a 0^b 1 0$, $1^a 0 1 1 0^c$ and $1^a 0 1 1 0^c 1 0$; the first family is the long-runs
   theorem's.
2. **Any segment** (`run_segment_column`, `center_run_segment`). For every $a \ge 9$, no column repeats $1^a u$, for
   every segment $u$ that starts with 0, passes the three-valued check `segOK` from the wall, and has a 0 at or just
   before each of its places $9, 10, \dots$, counted from 0.
3. **Any block** (`wall_block_column`, `center_wall_block`). No column repeats a block $B$ with `wallGood B = true`:
   some place of $B$, read cyclically, follows nine 1s, and from there the three-valued run, back at the wall after
   every nine 1s, knows the cell right of the column at every 0 of one period. `wallGood` is a computation on $B$
   alone, so `decide` settles it for any given block.
4. **The general form** (`wall_segments_column`). The same, stated along the column itself.

## The three-valued run

Let $c_1, c_2$ be the two cells right of the column, each 0, 1 or unknown, with the cell beyond them unknown. When the
column reads $x$, Rule 30 gives $c_1' = x \oplus (c_1 \lor c_2)$ and $c_2' = c_1 \oplus (c_2 \lor \,?)$, with
$1 \lor\, ? = 1$ and every other operation with an unknown giving an unknown (`tstep`). Nine 1s set $(c_1, c_2) =
(0, 1)$, the wall. From it the states and moves are

| state $c_1 c_2$ | column 0 | column 1 |
|---|---|---|
| 01 (the wall) | 11 | 01 |
| 11 | 10 | 00 |
| 10 | 1? | 0? |
| 00 | 0? | 1? |
| 1? | 1? | 0? |
| 0? | ?? | ?? |
| ?? | fails | ?? |

A segment passes if it never reads a 0 in state ??. Reading the table, the segments that start with 0, end with 0
and are followed by the next run of 1s, which merges with any 1s that follow ??, pass exactly when they are one of
$0^b$ ($b \ge 1$), $0^b 1 0$ ($b \ge 1$), $0100$, $0 1 1 0^c$ ($c \ge 1$) and $0 1 1 0^c 1 0$ ($c \ge 0$);
[computations/wall_segments.py](../../computations/wall_segments.py) confirms this for every segment of up to 18 cells.

## Argument

1. **The wall** (`wall_forms`, from [LongRuns](LongRuns.md)). Nine 1s in column $k$ leave columns $k + 1$ and $k + 2$
   reading 0 1, whatever the rest of the row holds.
2. **Soundness** (`tstep_sound`, `wstate_sound`). The three-valued step is checked over every case: the cells it
   knows are the true ones, whatever the unknown cells hold. So along a real column, started just after nine 1s and
   sent back to the wall after every nine 1s, the state agrees with the two true cells at every later time.
3. **The left column** (`left_cell`). Rule 30 is permutive in its left cell, so
   $x_t(k - 1) = x_{t+1}(k) \oplus (x_t(k) \lor x_t(k + 1))$. At a 1 of column $k$ the OR is 1; at a 0 the state
   knows $x_t(k + 1)$. So column $k - 1$ is a function of column $k$ at times $t$ and $t + 1$ and of the state.
4. **Periods** (`wstate_periodic`). If column $k$ has period $P$ and the state starts just after nine 1s, the state
   has period $P$: it is back at the wall after the same nine 1s one period later. So column $k - 1$ has period $P$
   too, and two adjacent columns are eventually periodic, which [the adjacent-column
   theorem](AdjacentColumns.md) rules out (`wall_segments_column`).
5. **Blocks and families.** For a block, a phase of the block plays the time just after nine 1s, and the state along
   the block equals the state along the column (`wstate_congr`, `wall_block_column`). For $1^a u$ the state is checked
   along $u$ alone (`segOK`, `segOK_known`): within $u$ no nine 1s occur, so the state runs without returning to the
   wall (`wstate_eq_wrun`), and the next run of 1s needs no check. For the families, a 0 in state $1?$ leaves $1?$
   (`segOK_zeros`), which carries the check through $0^z$ for every $z$.

## What it adds

Up to period 22, 275 primitive blocks are in the family (`in_family`, the computation of `wallGood`; the two agree on
every primitive block up to period 18), and 177 of them have a run of 1s shorter than nine
(`python -m computations.wall_segments --max-period 22`). Up to period 16 the family has 64 blocks. All 64 are among
the 77 blocks with nine 1s in a row that [the finite game](../../findings/columns/game-blocks.md) excludes, and 30 of
them are beyond the blocks of that range that the kit excludes (`--max-period 16 --game`). The game proves those 30 one certificate at a time; this
module proves them, and the family at every period, with one argument.

## Beyond three values

The three-valued run forgets correlations between unknown cells. Brute force over every row in the light cone
(`brute_segment`) accepts 84 more segments of at most 12 cells that start and end with 0
(`python -m computations.wall_segments --brute 12`), in patterns with a parity, such as $0^b 1 0 0$ and $0^b 1 1 0$
for odd $b \ge 3$ and $0^b 1 0 1 0$ for even $b \ge 2$. A finer abstraction that keeps those correlations would exclude
more families by the same argument; [WallSets](WallSets.md) does so with sets of three-cell windows, which accept 123
of the 124 segments of at most 12 cells that brute force accepts.

## Relation to the kit

The kit's
[`Rule30BlackRuns`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30BlackRuns.lean)
proves the nine-black wall for the single seed, excludes every eventual period whose runs of 1s that end are all at
least nine long, and, with longer runs, every period with a black run $r \ge 9 \lceil (P - r + 9)/2 \rceil$ (Theorem B)
or a black run of at least nine followed by a long white run (Theorem D). Its
[`Rule30BlackRunBlocks`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30BlackRunBlocks.lean)
(Theorem B′) excludes $1^r u$ for eight tails $u$ found by a SAT search, with $r \ge 18$ for $0$, $00$, $000$, $0000$
and $0100$ and $r \ge 27$ for $010$, $0010$ and $0110$, by checking that column 1 is the same for every row through
$u$ and the next nine 1s. Here column 1 is needed only at the 0s of the column, so the two cells of the wall suffice:
all eight tails pass `segOK` (`segOK_kit_tails`), so `center_run_segment` excludes them after nine 1s, and the families
of statement 1 have tails of every length. Outside its finite table of strip certificates, the kit reaches
$1^a 0^b 1 0$ through Theorem B when $a \ge 9 \lceil (b + 11)/2 \rceil$, through Theorem D when $b \ge 46$, and through
Theorem B′ when $b \le 2$ and $a \ge 27$; the rest of that family is new, and so are most blocks with several long
runs. The statements here hold for every column of every row with a
leftmost 1, as [LongRuns](LongRuns.md) does.

## Lean

`Rule30Open.Columns.WallSegments`: `Tri`, `tor`, `txor`, `tstep`, `agree`, `tstep_sound`, `wall`, `nine`, `wstate`,
`wstate_sound`, `wstate_periodic`, `wall_segments_column`, `cyc`, `wallGood`, `wstate_congr`, `wall_block_column`,
`center_wall_block`, `segOK`, `segRun`, `segOK_append`, `wrun`, `segOK_known`, `wstate_eq_wrun`, `nine_false`,
`run_segment_column`, `segOK_zeros`, `run_family_column`, `center_run_family`, `center_run_segment`,
`segOK_kit_tails` and `wallGood_two_runs`. The module builds in a few seconds.
