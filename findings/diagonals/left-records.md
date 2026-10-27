---
title: Where the left diagonals turn white, to depth 100,000
category: diagonals
problems: [1]
status: computed
formalization: partial
evidence: [computations/left_diagonals.py]
---

# Where the left diagonals turn white, to depth 100,000

Below depth 100,000 exactly seven left diagonals of the single cell's pattern are eventually white: depths 2, 7, 28,
399, 53,207, 58,286 and 87,866. By [the memory theorem](../../Rule30Open/Diagonals/LeftMemory.md), only these can make
a period grow, and the period doubles behind one exactly when the diagonal before it has odd weight per period. The
weights are 1, 1, 3, 3, 6, 10 and 5, so the periods double at depths 3, 8, 29, 400 and 87,867 and not at 53,208 or
58,287. So the settled left side down to depth 100,000 is fixed by seven bits of memory.

## Result

| White diagonal | Period and weight of the diagonal before it | Period of the diagonal after it |
|---:|---|---:|
| 2 | 1, weight 1 | 2 |
| 7 | 2, weight 1 | 4 |
| 28 | 4, weight 3 | 8 |
| 399 | 8, weight 3 | 16 |
| 53,207 | 16, weight 6 | 16 |
| 58,286 | 16, weight 10 | 16 |
| 87,866 | 16, weight 5 | 32 |

The period records, at depths 3, 8, 29, 400 and 87,867, are those in Wolfram's notes to *A New Kind of Science* (OEIS
A364239 lists them one-based, 4, 9, 30, 401, 87,868). What is new is the mechanism and the two white diagonals at
53,207 and 58,286 that do not double the period.

## Heuristic for the next record

White events among diagonals of period $p$ come about once per $2^p$ depths (here 1, 1, 1 and 3 events in the
regimes of period 2, 4, 8 and 16, against 1.25, 1.3, 1.45 and 1.33 expected), and each doubles the period with
probability about 1/2 (odd weight). On that model the period-64 record lies near depth $2^{33}$, about $10^{10}$. The
memory bits come from the chaotic transient, so the recursion alone cannot predict the next record exactly.

## Reproduce

```bash
python -m computations.left_diagonals 140000 100000
```

[computations/left_diagonals.py](../../computations/left_diagonals.py) evolves 140,000 steps and reads every diagonal
below 100,000 over the last 128 steps, in about 3 s. Each diagonal settles after about $1.35j$ steps, which is why the
run needs 140,000 steps for depth 100,000.
