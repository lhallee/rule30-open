---
title: From a late onset a small row follows a periodic word no longer than a random one
category: columns
problems: [1]
status: negative
kind: no-signal
evidence: [computations/late_onset.py, computations/periodic_columns.py]
---

# From a late onset a small row follows a periodic word no longer than a random one

**Question.** [Columns that repeat from time 0](periodic-from-start.md) searches every row of up to 24 cells for a
column that repeats from the start, and leaves out onsets $T_0 > 0$. A column that repeats only from $T_0$ repeats from
time 0 in the row at time $T_0$, whose support has at most $w + 2T_0$ cells, so finiteness at the onset might constrain
a small row more than the search at time 0 sees. Three things are asked: does the longest run along a periodic word grow
with the onset, is a periodic word easier to follow than a random one, and can a search with a fixed horizon (a SAT
instance per width) refute Problem 1 for finite rows?

**Method.** [late_onset.py](../../computations/late_onset.py) runs every row with black cells in cells $0, \dots, w -
1$, for $w = 8$, 12, 16 and 20, for 160 steps, bit-sliced as in
[periodic_columns.py](../../computations/periodic_columns.py). For every column of the support, every onset $T_0 <
120$ and every target it records the longest run $L$ for which the column equals the target at the times $T_0, \dots,
T_0 + L - 1$. The targets are $01$, $001$ and $011$ in every phase (8 periodic targets), and as controls 24 words of a
fair coin. The tests check the bit slices against every row stepped as an integer.

**Outcome.**

The longest run over every row, column of the support and onset of a bucket, at $w = 16$ and $w = 20$:

| | $T_0 = 0$ | $T_0 \in [1, 8)$ | $T_0 \in [8, 32)$ | $T_0 \in [32, 64)$ | $T_0 \in [64, 120)$ |
|---|---|---|---|---|---|
| $w = 16$: 8 periodic targets | 16 to 21 | 18 to 22 | 17 to 22 | 18 to 21 | 18 to 24 |
| $w = 16$: 24 random targets (median) | 16 to 25 (17) | 16 to 25 (18) | 17 to 24 (19) | 19 to 29 (21) | 20 to 28 (22) |
| $w = 16$: $\log_2$ of the trials of one target | 20.0 | 22.8 | 24.6 | 25.0 | 25.8 |
| $w = 20$: 8 periodic targets | 20 to 24 | 20 to 24 | 22 to 27 | 20 to 24 | 24 to 26 |
| $w = 20$: 24 random targets (median) | 20 to 25 (22) | 21 to 29 (22) | 20 to 28 (22) | 21 to 29 (23) | 23 to 28 (26) |
| $w = 20$: $\log_2$ of the trials of one target | 24.3 | 27.1 | 28.9 | 29.3 | 30.1 |

The longest run at one onset, averaged over the onsets of each bucket:

| $w$ | targets | $T_0 = 0$ | $[1, 8)$ | $[8, 32)$ | $[32, 64)$ | $[64, 120)$ | all onsets |
|---|---|---|---|---|---|---|---|
| 8 | periodic | 9.2 | 9.2 | 8.9 | 9.0 | 9.4 | 9.18 |
| 8 | random | 10.5 | 9.3 | 8.9 | 9.3 | 9.5 | 9.32 |
| 12 | periodic | 13.4 | 12.9 | 12.6 | 12.9 | 13.9 | 13.30 |
| 12 | random | 14.2 | 12.8 | 12.2 | 13.5 | 13.7 | 13.31 |
| 16 | periodic | 18.2 | 16.9 | 16.4 | 15.8 | 17.1 | 16.63 |
| 16 | random | 17.3 | 16.9 | 15.7 | 16.7 | 17.4 | 16.83 |
| 20 | periodic | 21.6 | 20.4 | 20.3 | 19.2 | 20.6 | 20.15 |
| 20 | random | 22.0 | 20.8 | 19.3 | 19.5 | 20.7 | 20.11 |

1. **The onset does not help.** The longest run at one onset shows no trend in $T_0$: its mean moves by at most 2.7
   between buckets and is about $w$ at every onset. The longest run over a bucket grows with the bucket's number of
   onsets: from $T_0 = 0$ to the 56 onsets of $[64, 120)$ the most over the periodic targets goes from 11 to 17, 15 to
   20, 21 to 24 and 24 to 26 at the four widths, up by 2 to 6, against $\log_2 56 \approx 5.8$, and the random
   targets' median goes up by 4 or 5. The periodic targets' longest runs are at most 1 above $\log_2$ of the number of
   (row, column, onset) trials of one target, and mostly below it; as a heuristic for chance the count overstates it,
   since runs from neighboring onsets and columns overlap. With every column within 120 cells of the support at $w =
   12$, which adds the $2 T_0$ columns that the row at the onset has beyond the support, and 8 random targets, the mean
   at one onset rises from 13.9 at $T_0 = 0$ to 17.0 over $[64, 120)$ for the periodic targets and from 15.2 to 17.7
   for the random ones: the number of columns looked at grows, and, heuristically, the run with its logarithm.
2. **Periodic targets are not special.** At each width the mean over all onsets differs between the periodic and the
   random targets by at most 0.2 (0.43 with the columns beyond the support), and over each bucket the periodic targets'
   longest run is at most the random targets' largest, except at $w = 12$ over $[8, 32)$, where it is 20 against 19.
   Within these widths and onsets a small row follows $01$, $001$ or $011$ from a late onset no longer than it follows
   a fair coin's word, within the spread of the controls. The random targets' largest runs, 25 at $T_0 = 0$ and 29 over
   $[32, 64)$, are already reached at $w = 8$ and $w = 12$, and a row of fewer cells is also a row of more, so they
   recur at every larger width.
3. **No fixed horizon refutes anything.** Rule 30 is permutive in its left input, so cell $(t, x)$ changes with cell
   $x - t$ of the row at time 0 whatever the cells right of it hold. Column $w - 1 + T_0$ at the times $T_0, T_0 + 1,
   \dots, T_0 + w - 1$ therefore takes the cells $w - 1, w - 2, \dots, 0$ of the row one at a time, and for every word
   $u$ of length $w$ and every onset some row of $w$ cells has that column equal to $u$ from $T_0$ (`free_bit_row`,
   checked in the tests; it is the bijection of [LeftWindow](../../Rule30Open/RandomRows/LeftWindow.md), read at the
   right end of the row). So the question "does some row of $w$ cells follow $b$ on the times $T_0, \dots, T_0 + L -
   1$" has the answer yes once $w \ge L$, whatever $T_0$, and no family of such instances with a fixed horizon is
   unsatisfiable for every $w$. Only the instance with every time, Problem 1 for finite rows itself, can be. Within the
   support the same count gives column $w - 1$ the $w - T_0$ free cells at onsets $T_0 < w$; at later onsets no column
   of the support has free cells, and the runs stay at about $w$ all the same. With the columns beyond the support, at
   $w = 12$, the longest run is at least 12 at every onset for every target, and exactly 12 for some.

**What it means.** Extending the search of [columns that repeat from time 0](periodic-from-start.md) to late onsets
finds nothing a proof could use: for $w \le 20$ and $T_0 < 120$ the run a small row sustains follows its number of cells
and the number of places looked at, whether the target is periodic or not. That is, as a heuristic, the information
count of [the random-rows barrier](../random-rows/almost-every-row.md) for one row. With both halves finite at the onset
and the right half small, the one left half that could keep the center on a block is computed in [the finite onset
census](../../findings/columns/finite-onset-census.md), with the same outcome.

**Reproduce.**

```bash
python -m computations.late_onset --cells 8 12 16 20 --steps 160 --max-onset 120   # 85 s
python -m computations.late_onset --cells 12 --margin 120 --controls 8            # columns beyond the support, 3 s
```

[late_onset.py](../../computations/late_onset.py) also has `sat_longest`, the same question for the middle column of
wider rows as a SAT instance on the light cone; it needs the optional dependency python-sat
(`pip install .[sat]`), and its test is skipped without it.
