---
title: Whatever the center column, the left half it drives allows a black run from time t of at most 0.13t to 0.18t and a white run of at most 0.15t to 0.28t for t from 75 to 175, far below the kit's slopes 3/5 and 1
category: diagonals
problems: [2]
status: conjecture
formalization: wanted
evidence: [computations/run_mechanism.py]
---

# Whatever the center column, the left half it drives allows a black run from time t of at most 0.13t to 0.18t and a white run of at most 0.15t to 0.28t for t from 75 to 175, far below the kit's slopes 3/5 and 1

**Conjecture (driven runs).** There are $\beta < 3/5$ and $\omega < 1$, and constants, such that for every sequence
$c(0) = 1, c(1), c(2), \ldots$ the left half driven by $c$ from a white start (defined below) allows a black run of
column 0 from time $t$ of length at most $\beta t + O(1)$ and a white run of length at most $\omega t + O(1)$. The data
below suggest $\beta \approx 0.15$ and $\omega \le 0.28$, with the white ratio still falling. Since the single cell's left half is the one its own center
column drives, the conjecture would cut the kit's run slopes (black $3/5$ in kit pull request #46, white $1$) to
$\beta$ and $\omega$, and with them the counts: a white run bound of slope $\omega$ puts a black cell in every window
$[a, (1 + \omega) a]$, so at least $\log n / \log(1 + \omega)$ black cells before $n$, about $2.8 \log_2 n$ at
$\omega = 0.28$, against the kit's $\log_2 n$. It would not give a positive density, and the data say the driven left
half alone cannot give a bound sublinear in $t$ (see [what it means](#what-it-means)).

## The reduction (paper, every step a kit lemma)

Take any configuration whose cells left of column 0 are white at time 0. Its left half (cells $-1, -2, \ldots$) at
every time is a function of column 0 alone: one step is
$x'_{-k} = x_{-k-1} \oplus (x_{-k} \lor x_{-k+1})$ with $x_0 = c(t)$ (the kit's `Rule30DrivenLeft`, `cell_eq_L` with
the start at time 0). Write $\mathcal{L}_t$ for the set of left halves at time $t$ over all drivers with $c(0) = 1$, and
$N(t) = |\mathcal{L}_t|$.

- **Black runs.** A black run of column 0 from time $a$ of length $L$ makes row $a$ alternate on $-(L-1) .. 0$ (cell
  $-k$ black exactly for even $k$; the kit's `black_triangle`). So $L \le R_B(a) := 1 + \max_{x \in \mathcal{L}_a}$
  (length of the alternating right end of $x$ with $x_{-1}$ white). Conversely, a row alternating there with a black
  center keeps the center black for exactly that long: the right end of an alternating block ending black is never
  eroded (the `or` sees the black cell), and the left end moves right one cell per step.
- **White runs.** During a white run the center is $x_{-1}(t) \oplus x_1(t)$, the left half is driven by white cells,
  and column 1 can only turn from white to black ($x_1' = x_1 \lor x_2$ while the center is white; the kit's
  `front_moves`, `black_stays`, `col_one`). So the run lasts while column $-1$ under the white driver reads
  $0^{\ell} 1^{(\cdot)}$ for the time $\ell$ at which column 1 turns black, and $L \le R_W(a) := 1 + \max_{x \in
  \mathcal{L}_a} (z + o)$, where column $-1$ of $x$ under the white driver starts with $0^z 1^o$.

Every bound valid for all drivers holds for the single cell. The relaxation is not tight for every $a$: over the
configurations themselves (cells $1 .. a$ free, enumerated) the longest black run from time $a$ is smaller than
$R_B(a)$ at $a = 5, 6, 7, 13 .. 17, 21, 22, 25, 26$, and equal at the other $a \le 26$ (`class_black_max`).

## Evidence

$\mathcal{L}_t$ is computed exactly by breadth-first search with one driver kept per row (`driven_rows`; checked
against cell-by-cell evolution of every driver for $t \le 9$, and against direct simulation of every configuration
with the left half white for $a = 4, 6$). The single cell's left half lies in $\mathcal{L}_t$ (checked at $t = 15, 30,
45, 60$).

| $t$ | $N(t)$ | $\log_2 N(t)$ | $R_B(t)$ | $R_B(t)/t$ | $R_W(t)$ | $R_W(t)/t$ |
|---:|---:|---:|---:|---:|---:|---:|
| 25 | 84 | 6.39 | 8 | 0.320 | 11 | 0.440 |
| 50 | 1,067 | 10.06 | 9 | 0.180 | 17 | 0.340 |
| 75 | 11,567 | 13.50 | 12 | 0.160 | 21 | 0.280 |
| 100 | 89,070 | 16.44 | 16 | 0.160 | 24 | 0.240 |
| 125 | 478,145 | 18.87 | 17 | 0.136 | 25 | 0.200 |
| 150 | 2,268,163 | 21.11 | 21 | 0.140 | 25 | 0.167 |
| 175 | 10,778,684 | 23.36 | 25 | 0.143 | 27 | 0.154 |

Over $75 \le t \le 175$ in steps of 5 the ratio $R_B(t)/t$ lies between 0.129 and 0.178 and $R_W(t)/t$ between 0.154
and 0.280, falling from 0.20 to 0.24 near $t = 100$ to 0.15 to 0.18 near $t = 170$. For comparison the kit's bounds at $t = 175$ are $L \le 175 - 2 \lfloor 174/5 \rfloor = 107$ (black,
`black_run_le_erosion` in the kit's main branch) and $L \le 172$ (white, `white_run_le_three`), and the single cell's
longest runs up to $2^{20}$ are 22 (black) and 19 (white).

Two regularities, both measured and not proved:

- $R_B(t)$ tracks $\log_2 N(t)$ within 2.5 (16 against 16.4 at $t = 100$, 21 against 21.1 at 150, 25 against 23.4
  at 175), and $R_W(t)$ exceeds it by 2.9 to 9.1: the right ends of the reachable rows behave like $\log_2 N(t)$ fair bits,
  so the longest alternating one has about that length. This is a heuristic.
- $N(t)$ is tiny against the $2^{t-1}$ drivers. A driver value $c(j)$ reaches the left half only through the `or` with
  $x_{-1}(j)$, so only when column $-1$ is white, and different drivers then merge. The growth rate of $\log_2 N(t)$ per
  step falls from 0.18 near $t = 50$ to 0.09 near $t = 150$ and is 0.090 per step from $t = 125$ to 175, so on this
  range it looks linear with a slope near 0.09, not sublinear.

## How the single cell's long runs end

`mechanism` follows the cells $-64 .. 64$ of the single cell to $t = 2^{20}$ (262,429 black and 262,429 white maximal
runs).

- **Black runs are alternating domains.** For every black run, its length is exactly the length of the alternating
  stretch of row $a$ ending at the center. The run ends when the domain's left end, which moves right exactly one cell
  per step, reaches the center. Followed back in time, the domain of each of the 124 black runs of length at least 12
  is, at row $a - s$, the alternating stretch starting at $-(L - 1) - s$; its right end is at $-4s$ (exactly the forced
  trapezoid of `black_block_back`) at every $s$ for 40 of them and within 2 cells for 27 more. The domain keeps at
  least two cells for exactly as many steps back as the trapezoid does in 44 of the 124 runs and for at most 3 more in
  88; its lifetime over $L$ has median 0.42 (range 0.31 to 2.33), and in at least half of the runs the domain is never
  longer than $L$ (at most $1.58 L$). So a long black run is born as a short alternating seed near
  $(a - L/3, -4L/3)$ that grows rightward four cells per step and reaches the center at time $a$; the forced cone of
  the run is in a third of the cases its whole history, and an argument that only uses that cone cannot do better.
- **Long white runs end through the left.** For every white run with $\ell < 64$, the length is read off column $-1$
  and the number $\ell$ of white cells right of the center at row $a$, as in the reduction. All 128 white runs of length at least 12
  have $\ell = z$ (column 1 turns black when column $-1$ does) and then last while column $-1$ stays black; $\ell / L$
  has median 0.08 and maximum 0.58. So a long white run is a short white block followed by the alternating tail of the
  kit's `row_at_start`, and its length is set by the same kind of alternating domain as a black run, through the tail
  erosion `white_run_le_erosion` of the kit's main branch ($L + 2 \lfloor (a - \ell - 3)/5 \rfloor \le a$, so
  $L \le (3a + 2\ell + 14)/5$).

## Why the kit's methods stop where they do

- **Black.** The cells of row $a - s$ that every preimage of an alternating word shares are exactly the trapezoid
  (right end 4 cells further left per step, left end one cell further left), by enumeration of every preimage for words
  of 40 cells and $s \le 5$ (`forced_cells`; brute force agrees for 10 cells, $s \le 2$). Colliding it with the rigid
  left diagonals $D_0, D_1$ gives the slope $3/5$ and nothing below
  ([fixed-depth strips](../../negative-results/diagonals/fixed-depth-strips.md)).
- **White.** A black or a white block has no forced cell at all in any earlier row ($s \le 5$, 40 cells). With the
  center's own value $c(a - 1) = 1$, the white cells $0 .. \ell$ of row $a$ force cells $-1 .. \ell - 1$ of row $a - 1$
  black (one step of the rule, solved cell by cell). Given the tail erosion above, the white slope is below 1 if the
  white block of row $a$ reaches at most $\theta a$ cells right of the center for some $\theta < 1$: then $L \le \max(\theta a + 1, (3 + 2\theta) a/5 + 3)$.
  The preimages of a black block are a family of $4^s$ rows, not a cone: the third of each preimage farthest from the
  right end is periodic with period 3 for $s \le 2$ and 6 for $3 \le s \le 8$ (`far_periods`, 120 cells), with the
  phase set by the boundary values, so direct comparison stops at row $a - 1$ and the white slope stays 1.
- **The transfer inequalities** of [ColumnTransfer](../../Rule30Open/Columns/ColumnTransfer.md) move density bounds
  left and give nothing here: the bounds above come from the left half's reachable set, not from counts.

## What it means

- **Slope.** The conjecture is a statement about one explicit, driver-independent object, $\mathcal{L}_t$, with no
  reference to the chaotic band of the single cell. A proof would describe $\mathcal{L}_t$ well enough to bound its
  alternating right ends (black) and the readings $0^z 1^o$ of column $-1$ under the white driver (white). Unlike
  [linear settling](settled-runs.md), it does not need the left diagonals of the single cell to settle.
- **Barrier to sublinear bounds from the left half alone.** For each $t \le 175$ the table's $R_B(t)$ is attained by a
  driver (`driven_table` returns one), so no argument that holds for every driver proves a black run bound below
  $R_B(t)$, which grows like $0.14 t$ on the range. A bound $o(a)$, or $O(\log a)$ as the data for the single cell
  suggest, has to use that the driver is the center column itself, a statement about the right half's dynamics, which
  is the same kind of statement as the problem. Whether the maximizing drivers are center columns of some
  configuration is open past $a = 26$; for $3 \le a \le 26$ they are at 12 of the 24 values of $a$. The relaxation
  also drops a constraint that needs no right half: a black center cell fixes the next one, $c(t + 1) = \lnot
  x_{-1}(t)$ when $c(t) = 1$ (so $c(1) = 1$). How much that constraint lowers $R_B$ and $R_W$ is not measured here.

## Reproduce

```bash
python -m computations.run_mechanism driven --steps 175 --every 5   # the table, about 20 min, 3 GB of memory
python -m computations.run_mechanism class --steps 26               # configurations against drivers, about 1 min
python -m computations.run_mechanism mechanism --steps 1048576      # the single cell's runs, about 2 min
python -m computations.run_mechanism forced                         # forced cells and far periods, about 1 s
```
