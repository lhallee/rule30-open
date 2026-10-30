---
title: An eventual period of the center column needs T + P of at least 262,125
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.WideWindow
headline: [runRel_fst, runRel_snd, center_eq_wide, wideFactor_new, transient_add_period_ge_262125]
kit: refines
kit_modules: [Rule30Window, Rule30FactorWindow]
evidence: [computations/long_window.py]
---

# An eventual period of the center column needs T + P of at least 262,125

[LongWindow](LongWindow.md) proves that an eventual period $P$ of the center column after a transient $T$ needs
$T + P \ge 65{,}518$, from its first 65,536 cells. The same argument on the first 262,144 cells gives
$T + P \ge 262{,}125$, four times the bound and sixteen times the kit's 16,359.

## Statement

Let $c(t)$ be the center column of Rule 30 from a single black cell.

1. **The first 262,144 cells** (`center_eq_wide`). For $t < 262{,}144$, $c(t)$ is bit $t$ of the number `wideBits`.
2. **A new factor** (`wideFactor_new`). The 20 cells $c(262{,}124), \dots, c(262{,}143)$ occur at no earlier time: for
   every $j < 262{,}124$ the factor of length 20 at $j$ differs from them.
3. **The bound** (`transient_add_period_ge_262125`). If $P > 0$ and $c(t + P) = c(t)$ for every $t \ge T$, then
   $T + P \ge 262{,}125$.

## Argument

1. **The run in sixteen parts.** The kit packs row $t$ into one number with the seed at bit $K$ (`Rule30Window.row`),
   whose bit $K$ is the center cell while $t \le K$ (`row_testBit`). Here $K = 262{,}144$, and `runRel` steps a packed
   row $n$ times while it collects bit $K$ of each row, returning both the last row and the collected cells
   (`runRel_fst`, `runRel_snd`). Each of the sixteen kernel checks `wideRun0` to `wideRun15` runs 16,384 steps from a
   given row, the seed's at time 0 and the literal `wideAt<t>` after, to the next literal and the part's 16,384 center
   cells, read off `wideBits`. So the literals are the rows (`wideRow1` to `wideRow15`) and `wideBits` holds the
   center cells (`row_of_run`, `bit_of_run`).
2. **The factor in sixteen parts.** Part $q$ compares the last factor with the factor at every position
   $16{,}384\,q + j$, reading only the 16,404 cells from $16{,}384\,q$ on (`wideSeg`, `seg_factor`,
   `wideFactor0` to `wideFactor15`).
3. **The bound.** Suppose $T + P \le 262{,}124$. Then $j = 262{,}124 - P \ge T$, so $c(j + k + P) = c(j + k)$ for every
   $k$, and the factor at $j$ is the last factor, against statement 2.

## What it covers

Every eventual period with $T + P \le 262{,}124$ is excluded. The factor of length 19 at the end of this window occurs
earlier, so 20 is the least length that works there (`python -m computations.long_window --wide`). As in LongWindow,
the bound is a computation made formal, a little below $N - \log_2 N$ for a window of $N$ cells; published
computations go much further without a proof ([the literature](../../literature/rule-30.md)). No part of the run
holds more than 16,384 steps, and the last, on the widest rows, sets the peak of 5.3 GB; a window of $2^{20}$ cells
would need parts of a quarter the length, or rows packed without the white cells below the seed's light cone.

## Relation to the kit

The kit's
[`Rule30FactorWindow`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30FactorWindow.lean)
proves $T + P \ge 16{,}359$ from its first 16,384 cells. The packed rows, `stepRow` and `row_testBit` are the kit's
([`Rule30Window`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Window.lean));
`runRel` is the kit's `centerLoop` with the cells collected from bit 0 and the last row returned, so that one kernel
computation checks both the next checkpoint and the part's center cells.

## Lean

`Rule30Open.Columns.WideWindow`: `runRel`, `runRel_fst`, `runRel_snd`, `row_of_run` and `bit_of_run`; the literals
`wideAt16384` to `wideAt245760` and `wideBits` from [computations/long_window.py](../../computations/long_window.py)
(`--wide --lean`); the kernel checks `wideRun0` to `wideRun15` and `wideFactor0` to `wideFactor15`; `wideRow1` to
`wideRow15`, `center_eq_wide`, `wideLast`, `wideSeg`, `seg_factor`, `wideFactor_new` and
`transient_add_period_ge_262125`. With sequential elaboration the module builds in about five minutes with a peak near
5.3 GB.
