---
title: Direct comparison with a true strip of the pattern near the left edge of any fixed depth leaves the slope of black center runs at 3/5
category: diagonals
problems: [2]
status: negative
kind: barrier
evidence: [computations/diagonal_cones.py]
---

# Direct comparison with a true strip of the pattern near the left edge of any fixed depth leaves the slope of black center runs at 3/5

**Question.** A black run of length $L$ from time $a$ forces an alternating trapezoid behind it (cell $-k$ of row
$a - s$ is black exactly for even $k$, for $-(L - 1) - s \le -k \le -4s$). The trapezoid is forced (Lean:
`black_block_back` in [SettledRuns](../../Rule30Open/Diagonals/SettledRuns.md)), and for a run of 12 and up to three
steps back it is exactly the forced set (enumeration of every preimage in `tests/test_diagonal_cones.py`). The erosion
argument of kit pull request #46 (`Rule30BlackRunErosion`, merged after the pinned revision; see
[the kit pull requests](../../literature/kit-pull-requests.md)) collides it with the rigid left edge, which gives
$5L + 18\lfloor \log_2 \log_2 a \rfloor \le 3a + 51$, slope $3/5$.
If the collision is made with the true pattern on a strip of the $k$ diagonals nearest the edge instead of the bare
edge, does the slope fall?

**What was done.** `strip_excluded(D, a, run, k)` excludes a run when the forced trapezoid disagrees with the true
diagonals $D_0 .. D_{k-1}$ at some time before $a$, and `longest_open_strip(D, a, k)` is the longest run that survives.
It was computed from the true orbit for strip depths $k = 2$ to 600 and $a = 500$ to 3,000.

**Outcome.** The longest surviving run at $a$ and $k$:

| $k$ | $a = 500$ | $a = 1000$ | $a = 2000$ | $a = 3000$ |
|---:|---:|---:|---:|---:|
| 2 | 302 | 602 | 1202 | 1802 |
| 5 | 298 | 598 | 1198 | 1798 |
| 100 | 241 | 541 | 1141 | 1741 |
| 600 | 0 | 241 | 841 | 1441 |

For fixed $k$ the run bound is $3(a - k)/5 + O(1)$: a strip of depth $k$ lowers the bound by about $3k/5$ and leaves
the slope at $3/5$ (the test checks $a = 200, 300$ at $k = 5$: 118 and 178, which is $3a/5 - 2$). To get a slope below
$3/5$, the depth has to grow in proportion to $a$.

**Why.** The barrier has a two-line proof. At time $a - s$ the leftmost cell of the trapezoid, $-(L - 1) - s$, lies on
the diagonal of depth $a - L + 1 - 2s$, and the trapezoid is nonempty only for $s \le (L - 1)/3$. So the trapezoid never
enters the depths below $k$ when $L \le 3(a - k)/5 + 1$, and direct comparison with the strip cannot exclude such a run.
At $k = 100$, $a = 1000$ this is 541, the computed value.

**What it means.** Direct comparison of the forced cone with the true left side, without propagating the rule, cannot
improve the slope with a bounded amount of the left side. A rule-aware argument can do more from a fixed strip (by
`D_reset`, $D_{k}(t + 1) = \lnot D_{k-2}(t)$ wherever $D_{k-1}(t) = 1$, so a strip determines deeper diagonals in
places); this entry does not cover it. Something has to say what the left side does at depth proportional to $a$, which
is the linear settling time of [the conditional entry](../../findings/diagonals/settled-runs.md). That is open.

## Reproduce

```python
from computations.diagonal_cones import diagonal_table, longest_open_strip
D = diagonal_table(3600, 700)  # (700, 3600)
print(longest_open_strip(D, 1000, 100))  # 541
```
