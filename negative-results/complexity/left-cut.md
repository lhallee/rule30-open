---
title: The leftmost t - 2 cells of the cone are pairwise distinguishable for 3 ≤ t ≤ 17 and not for 18 ≤ t ≤ 22, where alternating stripes ending at -3 and -4 fix the center
category: complexity
problems: [3]
status: negative
kind: refuted
evidence: [computations/left_cut.py, tests/test_left_cut.py]
---

# The leftmost t - 2 cells of the cone are pairwise distinguishable for 3 ≤ t ≤ 17 and not for 18 ≤ t ≤ 22, where alternating stripes ending at -3 and -4 fix the center

**Question.** Write $c_t$ for the center cell after $t$ steps as a function of the $2t + 1$ cells $x_{-t}, \dots, x_t$ of
an arbitrary row, and $N_{\mathrm{L}}(t, k)$ for the number of distinct functions of the other cells that the $k$ leftmost
cells leave when they are fixed ([cone screening](../../findings/complexity/cone-screening.md)). The statement tested is
$L(t)$: for every $t \ge 3$, $N_{\mathrm{L}}(t, t - 2) = 2^{t-2}$, that is, the $2^{t-2}$ settings of
$x_{-t}, \dots, x_{-3}$ give pairwise distinct functions of $x_{-2}, \dots, x_t$. It would give every ordered decision
diagram that reads the row from the left a level of width $2^{t-2}$, and one-way communication across a cut after
$k \le t - 2$ left cells a cost of exactly $k$ bits, for every $t$. Every linear rule has width 2 at every level, so the
bound would separate Rule 30 from Rules 90 and 150, which the bounds of [restricted
models](restricted-models.md) do not.

**Outcome.** $L(t)$ holds for $3 \le t \le 17$, proved in Lean
([LeftCut](../../Rule30Open/Complexity/LeftCut.md), `left_cut`), and fails at $t = 18$, also proved in Lean
(`left_cut_fails_18`), and at $t = 19, \dots, 22$ by computation (the counts to $t = 20$, the stripes below to
$t = 22$); whether it fails for every $t \ge 23$ is open. The failures come from prefixes that end in an alternating
stripe, the mechanism of [ConeScreening](../../Rule30Open/Complexity/ConeScreening.md) two cells further left. So a
proof of $L(t)$ for every $t$, by decoding or by induction, cannot exist; what survives is the finite range and a
smaller deficit.

## The counts

Computed by `computations/left_cut.py`: by streaming every prefix (`scan`) for $k = t - 2$ with $13 \le t \le 17$ and
for $k = t - 1$ with $12 \le t \le 15$; and for the other entries by grouping the prefixes by their values on the
completions with at most two black cells in the right half and comparing the subfunctions within each group in full
(`family_count`, which also gives the streamed counts at $k = t - 1$, $t = 13, 14, 15$). Each entry is exact. For
$k = t - 2$ and $t \le 17$ the counts are also proved in Lean.

| $t$ | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $2^{t-2} - N_{\mathrm{L}}(t, t - 2)$ | 0 | 0 | 0 | 0 | 0 | 0 | 4 | 14 | 26 |
| $2^{t-1} - N_{\mathrm{L}}(t, t - 1)$ | 0 | 8 | 8 | 16 | 26 | | | | |
| $2^{t-3} - N_{\mathrm{L}}(t, t - 3)$ | | | | | | | 0 | 0 | 0 |

So $N_{\mathrm{L}}(t, k) = 2^k$ for $k \le t - 2$ and $t \le 17$, and for $k \le t - 3$ and $t \le 20$; the deficit at
$k = t - 2$ is at most 26 of $2^{18}$ for $t \le 20$.

## Where it fails

Call a prefix a *stripe to $w$* when its cells alternate from $x_{-t}$ to a black cell $x_w$ ($x_w = 1$, $x_{w-1} = 0$,
...). `stripe_fixes` evolves a stripe to $w$ with every cell right of $w$ free, bit-sliced:

| wall $w$ | $-1$ | $-2$ | $-3$ | $-4$ | $-5$ | $-6$ |
|---|---:|---:|---:|---:|---:|---:|
| $c_t$ fixed for | $9 \le t \le 22$ (white) | $9 \le t \le 22$ (black) | $18 \le t \le 22$ (white) | $18 \le t \le 22$ (black) | no $t \le 22$ | no $t \le 22$ |

and for no smaller $t$. Flipping $x_{-t}$ flips $c_t$ on every row (`flip_center`), so the stripe to $-3$, the stripe to
$-4$ with $x_{-t}$ flipped and either value of $x_{-3}$, are three prefixes of $t - 2$ cells that all fix the center
white, and their three flips fix it black. At $t = 18$ these two classes are the only merges: the deficit is exactly 4.
The kernel checks the two stripes at $t = 18$ over all $2^{21}$ completions (`stripe_three_18`, `stripe_four_18`).

At $t = 19$ and $20$ the merged classes at $k = t - 2$ are of two kinds (`--family-count` prints them with the
lengths of the alternating runs that end black at $-3$ and at $-4$). Two classes fix the center, one white and one black:
the three stripes above and 3 further prefixes each at $t = 19$, and 8 further prefixes each at $t = 20$ (stripes ending
further left with a fixed tail, and runs ending black at $-3$ after a few other cells). The other classes do not fix the center, and every prefix in them ends in an
alternating run ending black at $-3$: 4 pairs at $t = 19$, with runs of 12 to 15 cells, and 2 classes of 4 at
$t = 20$, with runs of 9 to 15 cells.

At $k = t - 1$ (the cut at $-1$, $t = 13, \dots, 16$) every merged prefix ends in the 8 cells
$x_{-9}, \dots, x_{-2} = 0, 1, 0, 1, 0, 1, 0, 1$. For these the cells right of $-2$ never see the prefix before time 8:
the stripe shrinks by one cell a step from the left and keeps $x_{-2}$ black up to time 7, so up to time 8 the cells
from $-1$ on depend only on the completion and the cells up to $-2$ only on the prefix, and $c_t$ is $c_{t-8}$ of the row
at time 8, with the free cells of the prefix entering through a bijection (each cell flips its front, `front_xor`) and
the completion through the evolution beside a black wall. Since $N_{\mathrm{L}}(t', t' - 1) = 2^{t'-1}$ for $t' \le 12$,
two such prefixes can merge only because the image of that evolution misses every completion that separates their
images; this places the exception set but does not count it.

## The completion families

The completions with any $x_{-2}, x_{-1}$ and a right half with at most one black cell, $4(t + 2)$ of them, separate every
prefix for $t \le 12$ and leave 2, 12, 30, 48 and 172 pairs unseparated at $t = 13, \dots, 17$; with at most two black
cells, $4(1 + (t + 1) + \binom{t+1}{2})$ completions, they separate every prefix for $t \le 17$. A greedy order of these
families gives the kernel certificates of [LeftCut](../../Rule30Open/Complexity/LeftCut.md): at most 32 completions for
$t \le 17$. So an explicit family of $O(t^2)$ completions exists exactly as far as $L(t)$ holds, and the decoding proof
that such a family suggests has no target past $t = 17$.

## What it means

The exact distinguishability of the left cells fails the way the full left half fails in
[cone screening](../../findings/complexity/cone-screening.md): an alternating stripe ending in a black wall fixes the
center whatever lies right of it: for every $t \ge 9$ with the wall at $-1$ (`screening_odd` of ConeScreening), and in
the range computed, $9 \le t \le 22$, with the wall at $-2$ and $18 \le t \le 22$ with the walls at $-3$ and $-4$. The
thresholds 9, 9, 18, 18 for the walls at $-1, -2, -3, -4$ suggest (a heuristic extrapolation from four walls, not a
computed fact) that a wall at $-(2m - 1)$ or $-2m$ fixes the center from about $t = 9m$; if so, for each fixed $c$ the statement
$N_{\mathrm{L}}(t, t - c) = 2^{t-c}$ fails for large $t$, and the largest $k$ with $N_{\mathrm{L}}(t, k) = 2^k$ for every
$t$ is about $7t/9$. The deficits stay tiny: 26 of $2^{18}$ at $t = 20$. A lower bound of the form
$N_{\mathrm{L}}(t, t - 2) \ge 2^{t-3}$, or $N_{\mathrm{L}}(t, \lfloor 7t/9 \rfloor) = 2^{\lfloor 7t/9 \rfloor}$, is
consistent with every count here and is open; it would still give left-to-right decision diagrams exponential width,
and a proof would have to exclude stripe prefixes explicitly.

All of this is about arbitrary rows. None of it bounds the cost of the center column of the single black cell, the
row of the prize.

**What would change this.** A proof that the stripes to $-3$ and $-4$ fix the center for every $t \ge 18$ (the
analog of `screening_odd`, open because the center is the third cell right of the wall and the pair recursion of
[ConeScreening](../../Rule30Open/Complexity/ConeScreening.md) does not close on it); or a corrected statement, as above,
proved for every $t$.

**Reproduce.**

```bash
python -m computations.left_cut --t 17 --k 15 --black 2       # N_L(17, 15) and both families, streamed (200 s)
python -m computations.left_cut --t 15 --k 14 --merges         # the merged prefixes at the cut -1 (10 s)
python -m computations.left_cut --t 18 --k 16 --family-count 2 # N_L(18, 16) = 65532, the classes (10 s)
python -m computations.left_cut --t 20 --k 18 --family-count 2 # N_L(20, 18) = 262118 (5 min)
python -m computations.left_cut --t 22 --stripes               # the stripes to -1 .. -6, t <= 22 (1 min, 1.5 GB)
python -m computations.left_cut --t 17 --lean                  # the certificates of LeftCut (15 s)
```
