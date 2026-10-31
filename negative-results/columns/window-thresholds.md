---
title: Windows of up to 16 cells with the column's whole history leave the kit's white-run thresholds where they are
category: columns
problems: [1]
status: negative
kind: barrier
evidence: [computations/limit_windows.py]
---

# Windows of up to 16 cells with the column's whole history leave the kit's white-run thresholds where they are

**Question.** Every exclusion so far rests on a run of five or more equal values. [WallSegments](../../Rule30Open/Columns/WallSegments.md)
and [WallSets](../../Rule30Open/Columns/WallSets.md) need nine 1s, and the kit's main branch excludes, for the center
column of the single cell, every eventual period whose white runs are all at least 17 and, with black runs of 1, 2, 4
and at least 9, white runs of at least 10, 8, 7 and 9 ([the kit's pull requests](../../literature/kit-pull-requests.md);
the pinned kit has neither). Does a shorter run force a state of the cells beside the column that a finite
automaton on the rest of the block follows exactly, so that the thresholds of these families drop? The automaton here is
that of [limit windows](../../findings/columns/limit-windows.md): sets of windows of up to 16 cells with the cell beyond
free, started from every window, so that the column's whole history is used and nothing is assumed about the rest of
the block. A block passes when cell $k + 1$ is known at every 0.

**What was done.** `python -m computations.limit_windows` at widths 4 to 16: what a long run of 0s leaves
(`--stabilize`), one run of $r \le 8$ ones with the white run after it alone (`--runs`), and mixtures of black runs with
a least white run each, decided by the fixed point of the windows any history leaves (`consistent`).

**Outcome.**

1. **A white run alone leaves no known cell.** The windows after $t$ steps beside 0s, from every window, stop
   decreasing after $t = 2, 2, 10, 13, 16, 19, 28, 33$ steps at widths $4, 5, 6, 8, 10, 12, 14, 16$, as 11, 20, 27, 62,
   135, 303, 556 and 1,250 windows, and they hold both values of cell $k + 1$ at every width. So no white run, however
   long, is a wall: it helps only through the black run before it, and the black run $r \le 8$ alone leaves both values
   too (WallSets, "Why nine").
2. **One run with its own white run works at about 14 cells.** The least $q$ such that $1^r 0^q$ is good for every
   larger $q$ is, at 14 cells, $r = 1$ to 8: 10, 8, 18, 9, 13, 14, 16, 16, with sporadic $q$ below that: 6 for $r = 2$, 7
   for $r = 4$, 1 and 13 for $r = 7$, 2 for $r = 8$. At 16 cells it is the same (and $q = 16$ is good for $r = 3$,
   12 also for $r = 7$); at 12 cells $r = 3$ has none and $r = 7$ needs 19; at 8 cells $r = 3, 4, 5$ and 7 have none. So
   the single-run thresholds are final at 14 cells. Those below 17 are 13 to 16 for $r = 5$ to 8; the kit's families
   cover $r = 1, 2, 4$ at 10, 8, 7 and its main branch every $q \ge 17$.
3. **Mixing the run lengths costs the difference.** With a white run of at least $T$ after every run of 1 to 8 ones and
   after every run of at least nine, the mixture is consistent at $T = 16, 17, 18$, with $T \ge 18$ after exactly
   three 1s, and not at $T = 14, 15$, at 14 and at 16 cells; at those the runs 3, 5, 6, 7 and 8 fail, and the runs 1, 2 and 4 with the long
   runs are consistent down to $T = 9$ (with $q$ at least 10, 9 and 9). Windows of 14 and 16 cells agree. So the
   uniform threshold 17 of the kit's main branch becomes 16, with 18 after three 1s: no real gain, and the kit's three
   small thresholds 10, 8 and 7 are not reached (the run $1^4 0^8$ is not good alone, so $T = 7$ fails).
4. **The same count, a finer test.** The windows that the kit's four categories leave at 14 cells number 1,791, the
   number of strips the kit reports for its envelope of the four categories; the two sets are compared only by size. The
   test here fails on that envelope for the
   runs 1, 2 and 4, so the kit's rank argument is finer than asking for cell $k + 1$ to be known at every 0: it needs the
   cell only up to what the rank fixes, and covers $1^4 0^8$, which this test does not. [The finite game](../../Rule30Open/Columns/FiniteGame.md)
   is finer too: of the 76 blocks of period at most 14 that it excludes, 10 are not good here, among them $1^4 0^8$.

**What it means.** The mechanism of WallSegments, the cells beside the column driven by the column and the cell beyond
unknown, reaches the kit's thresholds from below at only one value, 16 instead of 17, however many cells the window
holds up to 16, and for every run length together it needs a white run as long as the kit's. The reason is in the first
0 after a black run of $r \le 8$: the windows still hold both values of cell $k + 1$ unless the white run before it was
long enough to have ruled out the starts that give the other value, and a mixture of run lengths lets the history be the
worst of them. Thresholds below the kit's hold for specific tails and specific runs ([limit windows](../../findings/columns/limit-windows.md)),
where the history is the block's own, not for a grammar of all of them.

## Reproduce

```bash
python -m computations.limit_windows --stabilize 4,5,6,8,10,12,14,16
python -m computations.limit_windows --runs 8,10,12,14,16
```

The mixtures of outcome 3 are `limit_windows.consistent({"1" * r: max(threshold, T) for r in range(1, 9)}, width, T)` with
the thresholds of outcome 2, `width` 14 or 16 and $T$ in 9, 10, 14, 15, 16, 17, 18; `consistent({"1": 10, "11": 8, "1111": 7}, 14, 9)` is outcome 4. The
kit's figures are from the descriptions in [the kit's pull requests](../../literature/kit-pull-requests.md#excluding-eventual-periods-by-families-of-blocks),
not from its Lean.
