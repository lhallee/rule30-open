---
title: An eventual period of the center column needs T + P of at least 65,518
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.LongWindow
headline: [center_eq_big, factor_new, transient_add_period_ge_65518]
kit: refines
kit_modules: [Rule30Window, Rule30FactorWindow]
evidence: [computations/long_window.py]
---

# An eventual period of the center column needs T + P of at least 65,518

The kit proves in Lean that an eventual period $P$ of the center column after a transient $T$ needs $T + P \ge 16{,}359$,
from its first 16,384 cells. The same argument needs only one factor of the column that is new, and the kernel can
check four times as many cells in four parts.

## Statement

Let $c(t)$ be the center column of Rule 30 from a single black cell.

1. **The first 65,536 cells** (`center_eq_big`). For $t < 65{,}536$, $c(t)$ is bit $t$ of the number `bigBits`.
2. **A new factor** (`factor_new`). The 19 cells $c(65{,}517), \dots, c(65{,}535)$ occur at no earlier time: for every
   $j < 65{,}517$ some $k < 19$ has $c(j + k) \ne c(65{,}517 + k)$.
3. **The bound** (`transient_add_period_ge_65518`). If $P > 0$ and $c(t + P) = c(t)$ for every $t \ge T$, then
   $T + P \ge 65{,}518$.

## Argument

1. The kit packs row $t$ into one number with the seed at bit $K$ (`Rule30Window.row`), reads cell $(t, k - K)$ as
   bit $k$ while $t \le K$ (`row_testBit`), and collects bit $K$ of $n$ consecutive rows with `centerLoop`
   (`centerLoop_spec`). With $K = 65{,}536$ the kernel runs the 65,536 steps in four parts of 16,384. The rows at times
   16,384, 32,768 and 49,152 are literals, each checked by stepping the one before (`steps16384_0` to `steps16384_2`,
   `rowAt16384_eq` and the others), and each part's center cells are checked against 16,384 bits of `bigBits`
   (`chunk0` to `chunk3`). No single kernel computation holds the whole run.
2. The kernel compares the factor at 65,517 with the factor at each earlier time (`factor_new`).
3. Suppose $T + P \le 65{,}517$. Then $j = 65{,}517 - P \ge T$, so $c(j + k + P) = c(j + k)$ for every $k$, and the
   factor at $j$ is the factor at 65,517, against statement 2.

## What it covers

Every eventual period with $T + P \le 65{,}517$ is excluded: a period from time 0 of at most 65,517, or a period
$P \le 65{,}517 - T$ after any transient $T$. The factor of length 18 at 65,518 does occur earlier, so 19 is the least
length that works at the end of this window. As a heuristic, a column that looks random gives a bound a little below
$N - \log_2 N$ from a window of $N$ cells. The bound is a computation, made formal. Published computations go much
further: the first billion cells show no period ([the literature](../../literature/rule-30.md)). A window of $2^{20}$
cells would need 16 times as many kernel steps on rows 16 times as wide, with checkpoint literals of up to 512 KB.

## Relation to the kit

The kit's
[`Rule30FactorWindow`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30FactorWindow.lean)
proves $T + P \ge 16{,}359$: all 16,359 factors of length 26 in its first 16,384 cells (`Rule30Window.centerBits`) are
distinct, which it certifies by the factors' sorted order. Here a single new factor, the last, gives the bound, so no
sorting certificate is needed, and the packed rows, `centerLoop` and its spec are the kit's
([`Rule30Window`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Window.lean)).
The kit's `no_small_eventual_period` excludes $P \le 4{,}096$ with $T \le 8{,}192$.

## Lean

`Rule30Open.Columns.LongWindow`: `steps` and `steps_row` for stepping packed rows; the literals `rowAt16384`,
`rowAt32768`, `rowAt49152` and `bigBits`, from
[computations/long_window.py](../../computations/long_window.py) (`--lean`); the kernel checks `steps16384_0` to
`steps16384_2` and `chunk0` to `chunk3`; `chunk_bit`, `center_eq_big`, `lastFactor`, `factor_new` and
`transient_add_period_ge_65518`. With sequential elaboration the module builds in about a minute with a peak near
2 GB.
