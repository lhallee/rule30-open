---
title: No row of up to 24 cells has a column that repeats from time 0
category: columns
problems: [1]
status: negative
kind: no-signal
evidence: [computations/periodic_columns.py]
---

# No row of up to 24 cells has a column that repeats from time 0

**Question.** Problem 1 has a form for every finite row: is any column of a finite nonzero row eventually periodic?
The kit proves that none is eventually constant and that at most one is eventually periodic (`Rule30FiniteConfigs`). An
eventually periodic column is a column that repeats from time 0 in a later row, so the first test is whether some
column of a small row repeats from the start. A counterexample would show that a proof of Problem 1 must use more of
the single cell than finiteness.

**Method.** Every row whose black cells lie in cells $0, \dots, w - 1$, for $w$ up to 24, run for 256 steps. Every
column within 32 cells of the support is checked against every period up to 32; a column farther out stays white until
an edge reaches it and then turns black, which no such period survives. The rows are bit-sliced, 64 to a machine word,
so all of them run at once. As controls the same search runs under Rule 90 and Rule 150, whose single-cell center
columns are eventually constant.

**Outcome.**

- Rule 30: no row, column and period survive 256 steps, for $w = 8$, 12, 16, 20 and 24, the last over all
  16,777,215 nonzero rows.
- Controls, at $w = 12$: Rule 90 keeps 3,648 triples in 114 rows, and Rule 150 keeps 7,680 in 240 rows, its single
  cell's center column among them, so the search sees a repeating column when there is one.
- Near misses: the most times a column of the support repeated with a period before it first failed is 15, 17, 20, 27
  and 28 at $w = 8$, 12, 16, 20 and 24. Chance gives about $\log_2$ of the number of row, column and period triples:
  16, 20.6, 25, 29.3 and 33.6.

**What it means.** The finite-row form of Problem 1 has no counterexample among small rows in this sense, and the
nearest misses sit at or below chance. The search covers repetition from time 0 only, with period at most 32 within
256 steps. A column of one of these rows that becomes periodic only at time $T > 0$ repeats from time 0 in the row at
time $T$, whose support has $w + 2T$ cells, so the search does not exclude it.

**Reproduce.**

```bash
python -m computations.periodic_columns --cells 20 --max-period 32 --steps 256
python -m computations.periodic_columns --cells 12 --max-period 32 --steps 256 --rule 150   # a control
```

[computations/periodic_columns.py](../../computations/periodic_columns.py) runs 20 cells in about 15 s and 24 cells in
about 4 min.
