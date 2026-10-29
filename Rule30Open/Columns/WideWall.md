---
title: A black run of r ≥ 9 steps rules out every eventual period with a tail of at most 4⌊r/9⌋ steps; nine 1s and then b 0s rule out every tail of at most 4⌊(b - 1)/9⌋ + 2
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.WideWall
headline: [center_long_run_tail, center_black_white_tail, long_run_tail_column, black_white_tail_column, wide_wall_column, stripe_agree, black_shield]
kit: refines
kit_modules: [Rule30BlackRuns]
evidence: [computations/wall_segments.py]
---

# A black run of r ≥ 9 steps rules out every eventual period with a tail of at most 4⌊r/9⌋ steps; nine 1s and then b 0s rule out every tail of at most 4⌊(b - 1)/9⌋ + 2

The kit's Theorem B (`Rule30BlackRuns.no_long_black_run`) excludes every eventual period of length $P$ of the center
column that contains a black run of length $r$ with $9 \lceil (P - r + 9)/2 \rceil \le r$, roughly $r \ge 0.82 P + 8.2$,
and its Theorem D (`Rule30BlackRuns.no_black_white_run`) every period with a black run of $s \ge 9$ steps followed by a
white run of $b \ge 1 + 9 \lceil (m + 8)/2 \rceil$ steps, where $m = P - s - b$ is the rest of the period. Here the same
is proved under the much weaker conditions $P - r \le 4 \lfloor r / 9 \rfloor$, roughly $r \ge 0.69 P$, and
$m \le 4 \lfloor (b - 1)/9 \rfloor + 2$, for every column of every row with a leftmost 1, whatever the rest of the
period holds.

## Statement

1. **Long run, any tail** (`long_run_tail_column`, `center_long_run_tail`). No column of the orbit of a row with a
   leftmost 1 is periodic with period $P$ from some time on while containing a black run of length $r \ge 9$ with
   $P - r \le 4 \lfloor r/9 \rfloor$. For $r = 45$ that allows a tail of 20 cells, where Theorem B allows 1; for
   $r = 90$, 40 where it allows 11.
2. **Black run, white run, any tail** (`black_white_tail_column`, `center_black_white_tail`). No such column is
   periodic with period $P$ while a period holds a black run of $s \ge 9$ steps, then a white run of $b \ge 1$ steps,
   then a tail of $m = P - s - b \le 4 \lfloor (b - 1)/9 \rfloor + 2$ steps. A tail of at most two steps needs $b \ge 1$,
   where Theorem D needs $b \ge 46$ (37 for no tail); at most six steps, $b \ge 10$ where it needs 64; at most ten,
   $b \ge 19$ where it needs 82 (`python -m computations.wall_segments --tails`).
3. **The general form** (`wide_wall_column`). No column is eventually periodic if, for some $j$, each of its 0s comes
   less than $4j$ steps after $9j$ 1s.
4. `kit_theoremB_condition` and `kit_theoremD_condition`: the conditions of Theorems B and D imply those of statements
   1 and 2.

## Argument

1. **The shield** (`wall_stays`, `black_shield`). Nine 1s in column $k$ leave columns $k + 1$, $k + 2$ reading 0 1
   ([LongRuns](LongRuns.md)), and while column $k$ stays black that pair stays: $1 \oplus (0 \lor 1) = 0$ and
   $0 \oplus (1 \lor \cdot) = 1$. So column $k + 2$ is black from then on, and by induction $9j$ 1s leave columns
   $k + 1, \dots, k + 2j$ reading $(0 1)^j$. The kit proves this for the single seed (its Lemma A*).
2. **Two rows that end in the same stripe agree** (`stripe_agree`). The stripe of length $L$ is $\dots 1 0 1$ on cells
   $k + 1, \dots, k + L$, black at $k + L$: cell $k + i$ is black when $L - i$ is even. Take two rows, or one row at
   two times, that read the stripe there and then see the same column $k$. The stripe is fixed by Rule 30 away from
   the column, by the two identities above, and each of its 1s hides the cell to its right from the OR. So for
   $s \le L$ steps the cells beyond $s$ are still the stripe in both, and cell $k + L$, a 1, hides whatever lies beyond:
   the rows agree on all $L$ cells. After that, each step can lose only the outermost cell of the agreement, since a
   cell reads only its neighbors. So the rows agree on cell $k + 1$ for $2L$ steps, whatever column $k$ reads. The
   shield $(0 1)^j$ is the stripe of length $2j$ (`shield_stripe`, `shield_agree`), which gives $4j$ steps.
3. **The latch** (`white_latch`, `black_shield_stripe`). At the first 0 after a black run of $s \ge 9$ steps the wall
   reads 0 1, so one step later the cell right of the column is $0 \oplus (0 \lor 1) = 1$, and while the column stays
   white it stays black: $0 \oplus (1 \lor \cdot) = 1$. So at the end of a white run of $b$ steps column $k + 1$ has
   read 1 for $b$ steps, and its own shield, from the last $9j$ of those steps before the end with
   $j = \lfloor (b - 1)/9 \rfloor$, leaves the cells right of column $k$ reading $1 (0 1)^j$: the stripe of length
   $2j + 1$.
4. **The left column follows** (`zeros_repeat_column`). If column $k$ has period $P$ and cell $k + 1$ repeats with
   period $P$ at each 0 of column $k$, then with $x_t(k - 1) = x_{t+1}(k) \oplus (x_t(k) \lor x_t(k + 1))$ column
   $k - 1$ has period $P$, and [the adjacent-column theorem](AdjacentColumns.md) rules out two adjacent eventually
   periodic columns. For the general form (`wide_wall_column`), the row at a covered 0 and the row $P$ steps later
   carry the same shield and see the same column, so step 2 applies.
5. **Long run, any tail** (`long_run_tail_column`). With $j = \lfloor r/9 \rfloor$, every 0 of the period comes in its
   tail, less than $P - r \le 4j$ steps after the run.
6. **Black run, white run, any tail** (`black_white_tail_column`). In every period the first 0 has the wall's 0 beside
   it, the other 0s of the white run have the latched 1, and the 0s of the tail come less than $4j + 2$ steps after the
   stripe of step 3 forms, so cell $k + 1$ repeats at every 0.

## Sharpness

A stripe of $L$ cells that ends in a black cell keeps the cell right of the column for exactly $2L$ steps: brute force
over every column and every cell beyond the stripe finds that cell the same for $2L$ steps and not for $2L + 1$, for
$L \le 4$, and three-valued Rule 30 from the stripe first loses it at step $2L$ for $L \le 10$ (`stripe_brute`,
`stripe_known_steps` in [computations/wall_segments.py](../../computations/wall_segments.py)). So four steps per nine 1s,
and two more for the latched cell, are the most the stripes give. Specific tails can be followed further:
[WallSegments](WallSegments.md) and [WallSets](WallSets.md) do so after nine 1s.

## Relation to the kit

[`Rule30BlackRuns`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30BlackRuns.lean)
proves the shield for the single seed and Theorems B and D by making column 1 periodic from a cone bound: the shield
must cover every cell the tail can reach. Here only the cell beside the column is needed, and only at the 0s, and the
stripe's 1s hide the rest, which halves the runs the shield needs and removes the additive constants. For a tail of at
most two steps, statement 2 gives the blocks $1^a 0^b$ and $1^a 0^b 1 0$, which [WallSegments](WallSegments.md) also
excludes with three values per cell; for longer tails it holds whatever the tail is. The kit's Theorem B′ and strip
certificates cover other blocks.

## Lean

`Rule30Open.Columns.WideWall`: `evolve_succ`, `wall_stays`, `black_shield`, `stripeEnd`, `stripe_agree`,
`shield_stripe`, `shield_agree`, `zeros_repeat_column`, `wide_wall_column`, `long_run_tail_column`,
`center_long_run_tail`, `kit_theoremB_condition`, `white_latch`, `black_shield_stripe`, `black_white_tail_column`,
`center_black_white_tail` and `kit_theoremD_condition`. It builds in a few seconds.
