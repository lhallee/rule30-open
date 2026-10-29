---
title: A black run of r ≥ 9 steps rules out every eventual period with a tail of at most 4⌊r/9⌋ steps
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.WideWall
headline: [center_long_run_tail, long_run_tail_column, wide_wall_column, shield_agree, black_shield]
kit: refines
kit_modules: [Rule30BlackRuns]
evidence: [computations/wall_segments.py]
---

# A black run of r ≥ 9 steps rules out every eventual period with a tail of at most 4⌊r/9⌋ steps

The kit's Theorem B (`Rule30BlackRuns.no_long_black_run`) excludes every eventual period of length $P$ of the center
column that contains a black run of length $r$ with $9 \lceil (P - r + 9)/2 \rceil \le r$, roughly $r \ge 0.82 P + 8.2$.
Here the same is proved under the much weaker condition $P - r \le 4 \lfloor r / 9 \rfloor$, roughly $r \ge 0.69 P$,
for every column of every row with a leftmost 1, whatever the rest of the period holds.

## Statement

1. **Long run, any tail** (`long_run_tail_column`, `center_long_run_tail`). No column of the orbit of a row with a
   leftmost 1 is periodic with period $P$ from some time on while containing a black run of length $r \ge 9$ with
   $P - r \le 4 \lfloor r/9 \rfloor$. For $r = 45$ that allows a tail of 20 cells, where Theorem B allows 1; for
   $r = 90$, 40 where it allows 11.
2. **The general form** (`wide_wall_column`). No column is eventually periodic if, for some $j$, each of its 0s comes
   less than $4j$ steps after $9j$ 1s in a row.
3. `kit_theoremB_condition`: Theorem B's condition implies that of statement 1.

## Argument

1. **The shield** (`wall_stays`, `black_shield`). Nine 1s in column $k$ leave columns $k + 1$, $k + 2$ reading 0 1
   ([LongRuns](LongRuns.md)), and while column $k$ stays black that pair stays: $1 \oplus (0 \lor 1) = 0$ and
   $0 \oplus (1 \lor \cdot) = 1$. So column $k + 2$ is black from then on, and by induction $9j$ 1s leave columns
   $k + 1, \dots, k + 2j$ reading $(0 1)^j$. The kit proves this for the single seed (its Lemma A*).
2. **Two shielded rows agree** (`shield_agree`). Take two rows, or one row at two times, that carry the shield and then
   see the same column $k$. The stripe $0 1 0 1 \dots$ is fixed by Rule 30, and each of its 1s hides the cell to its
   right from the OR. So for $s \le 2j$ steps the cells beyond $s$ are still the stripe in both, and cell $k + 2j$,
   a 1, hides whatever lies beyond the shield: the rows agree on all $2j$ cells. After that, each step can lose only
   the outermost cell of the agreement, since a cell reads only its neighbors. So the rows agree on cell $k + 1$ for
   $4j$ steps, whatever column $k$ reads.
3. **The left column follows** (`wide_wall_column`). If column $k$ has period $P$, then at a 0 of column $k$ less than
   $4j$ steps after $9j$ 1s, the row at that time and the row $P$ steps later are two such rows, so cell $k + 1$
   repeats there. With $x_t(k - 1) = x_{t+1}(k) \oplus (x_t(k) \lor x_t(k + 1))$, column $k - 1$ has period $P$, and
   [the adjacent-column theorem](AdjacentColumns.md) rules out two adjacent eventually periodic columns.
4. **Long run, any tail** (`long_run_tail_column`). With $j = \lfloor r/9 \rfloor$, every 0 of the period comes in its
   tail, less than $P - r \le 4j$ steps after the run.

## Sharpness

The four steps per nine 1s are the most this argument gives: brute force over every column and every cell beyond the
shield finds cell $k + 1$ the same for $4j$ steps and not for $4j + 1$, for $j = 1$ and 2, and three-valued Rule 30
from the shield first loses it at step $4j$ for $j \le 6$ (`shield_brute`, `shield_known_steps` in
[computations/wall_segments.py](../../computations/wall_segments.py)). Specific tails can be followed further:
[WallSegments](WallSegments.md) and [WallSets](WallSets.md) do so after nine 1s.

## Relation to the kit

[`Rule30BlackRuns`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30BlackRuns.lean)
proves the shield for the single seed and Theorem B by making column 1 periodic from a cone bound: the shield must
cover every cell the tail can reach. Here only the cell beside the column is needed, and only at the 0s, and the
stripe's 1s hide the rest, which halves the run the shield needs and removes the additive constant. Its Theorems D and
B′ and its strip certificates cover other blocks.

## Lean

`Rule30Open.Columns.WideWall`: `evolve_succ`, `wall_stays`, `black_shield`, `stripeAt`, `shield_agree`,
`wide_wall_column`, `long_run_tail_column`, `center_long_run_tail` and `kit_theoremB_condition`. It builds in a few
seconds.
