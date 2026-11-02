---
title: The binary separator BinaryCTS is the kit's Q01, so BWH alone, or WeakBWH with any horizon, excludes an eventual period two of the center column
category: period-two
problems: [1]
status: proved
lean: Rule30Open.PeriodTwo.WedgeLadderQ01
headline: [binaryCTS_iff_Q01, binaryCTS_Q01, q01_binaryCTS, q01_iff_horizon, q01_constantTailSeparator, bwh_Q01, weakBWH_Q01, center_not_eventually_period_two_of_bwh, center_not_eventually_period_two_of_weakBWH]
kit: new
kit_modules: [Rule30PeriodTwo, Rule30DrivenLeft, Rule30SEPToPeriodTwo]
evidence: [computations/wedge_ladder.py]
---

# The binary separator BinaryCTS is the kit's Q01, so BWH alone, or WeakBWH with any horizon, excludes an eventual period two of the center column

The pinned kit reduces period two of the center column to `Rule30PeriodTwo.Q01`: no start $s$ of the zero-driven left
half, rule 30 on the columns $p < 0$ with column 0 held white (`Rule30DrivenLeft.L (fun _ => false) s`), whose leftmost
black cell is at $-m$, $m \ge 1$, keeps column $-1$ black at every even step; `not_eventually_period_two_of_Q01`. The
kit's main branch charts a row with an alternating center into streams over four symbols
(`Rule30SEPToPeriodTwo.actual_cone_chart`) and states that no implication between its wedge hypotheses and `Q01` is
proved, because its chart takes the hard-core property of the stream from the row's right half
(`actual_endpoint_hardcore`, through `right_no11`). [WedgeLadder](WedgeLadder.md) defines `BinaryCTS`, the separator
for binary streams, which needs no hard-core property.

## Results

- **`binaryCTS_iff_Q01`**: `BinaryCTS` $\Leftrightarrow$ `Q01`. **`q01_iff_horizon`**: `Q01` $\Leftrightarrow$ some
  horizon function $L$ has `WeakBWH` at every depth. **`q01_constantTailSeparator`**: `Q01` implies the kit's
  `ConstantTailSeparator`, so the kit's `SEP`.
- **`bwh_Q01`**, **`weakBWH_Q01`**: `BWH` implies `Q01`, and so does `WeakBWH S L` for every infinite $S$ and every $L$.
- **`center_not_eventually_period_two_of_bwh`**, **`center_not_eventually_period_two_of_weakBWH`**: under `BWH`, or
  under `WeakBWH` on an infinite set with any horizon, the official center column `Rule30Prize.center` is not eventually
  of period two, whatever the transient. Neither needs `SmallRW` or `RW`.

## The chart

Write $H(t, p)$ for the cell at step $t$ and column $p < 0$, $H(t, 0) = 0$, and $\langle a, b \rangle = 2a + b$ for the
kit's encoding of a pair of cells (`encodePair`). Let $Z(t, i) = \langle H(t, i), H(t, i - 1) \rangle$ (`zpair`) and let
the endpoint be $e_j = Z(2j + 1, -1)$ (`zend`), the pair of columns $-1, -2$ at the odd steps.

1. **The backward step** (`zpair_backward`). For $i \le 0$, $\varphi(Z(t, i), Z(t+1, i-1)) = Z(t, i-2)$. The cells
   $H(t+1, i-1)$ and $H(t+1, i-2)$ are rule 30 of $H(t, i), \dots, H(t, i-3)$, and the kit's `pair_inverse_table` (a
   table over 16 cases) says that this is the backward step. Only columns $\le -1$ are updated.
2. **The pin** (`zend_boundary`). If $H(2j, -1) = 1$, then $H(2j+1, -1) = \lnot H(2j, -2)$ and
   $H(2j+1, -2) = \lnot H(2j, -3)$, because the OR in each update contains the black cell $H(2j, -1)$. So
   $\partial e_j = 3 - e_j = Z(2j, -2)$. The kit pins with the center cell; here column $-1$ black at the even steps,
   which is the hypothesis of `Q01`, does it.
3. **The cone and peel charts** (`zcone_chart`, `zpeel_chart`). By induction along the cone's recursion with items 1
   and 2, $C_e(n, j) = Z(2j + n, -(n + 2))$, and $P^d I_e(t) = Z(t, -(2d + t + 2))$.
4. **Binary** (`zend_binary`). $H(2j + 2, -1) = H(2j+1, -2) \oplus (H(2j+1, -1) \lor H(2j+1, 0))$ and column 0 is
   white, so column $-1$ black at step $2j + 2$ says that the two cells of $e_j$ differ: $e_j \in \{1, 2\}$. The
   hard-core property is not needed and not claimed.
5. **Finite rank** (`zend_finite_rank`). With the leftmost black cell at $-m$, the kit's `edge` puts every black cell of
   step $t$ at $-(m + t)$ or to its right, so $P^m I_e(t) = Z(t, -(2m + t + 2)) = \langle 0, 0 \rangle = 0$ for all $t$.

`BinaryCTS` excludes a binary stream with a finite peel rank ([WedgeLadder](WedgeLadder.md),
`binaryCTS_excludes_finite_peel_rank`), which proves `binaryCTS_Q01`.

## The converse: a history from a stream

Let $e$ be binary with $I_e(t) = c \in \{2, 3\}$ for $t \ge N$. The history (`hpair`) puts, at step $t$ and for
$m \equiv t \pmod 2$, the pair of columns $-m, -(m+1)$: $\langle 0, 1 \rangle$ at $m = 0$ (column 0 white over column
$-1$ black), $e_{\lfloor t/2 \rfloor}$ at $m = 1$, the cone entry $C_e(m - 2, (t + 2 - m)/2)$ for $2 \le m \le t + 2$,
and $\langle 0, 0 \rangle$ beyond. The cells (`hcell`) are read off these pairs. From step $N$ on the history obeys
$\varphi(\text{pair}(t, m), \text{pair}(t + 1, m + 1)) = \text{pair}(t, m + 2)$ (`hpair_rel`): at $m = 0$ because
$\varphi(1, x) = \partial x$, at $m = 1$ and inside the cone by the cone's recursion, on the cone's edge $m = t + 2$
because $\varphi(c, c) = 0$, and beyond because $\varphi(0, 0) = 0$. Since $\varphi(\langle a, b\rangle, \cdot)$ is a
bijection whose inverse is rule 30 (`pair_forward`, over 64 cases), the cells obey rule 30 at every column $\le -1$
(`hcell_rule`); at column $-1$ after an odd step this is the binary property of $e$. So the row at step $2N$, read as a
start (`hstart`), runs as the zero-driven left half through the history (`zl_hstart`), keeps column $-1$ black at every
even step, and has its leftmost black cell at $-(2N + 2)$ if $c = 2$ and at $-(2N + 3)$ if $c = 3$: a counterexample to
`Q01`. That proves `q01_binaryCTS`. With [WedgeLadder](WedgeLadder.md)'s `binaryCTS_iff_horizon` it gives
`q01_iff_horizon`.

So the chart is exact both ways: a counterexample to `Q01` is a binary stream with an eventually constant inverse, and
the vacuum $\varphi(c, c) = \varphi(0, 0) = 0$ ([WedgeLadder](WedgeLadder.md), `wedge_vacuum`) is the white region left
of the start's leftmost black cell. `BWH` asks that the forced runs at depth $n$ die within $n + 2$ steps, and `Q01`
asks only that they die; [WedgeLadder](WedgeLadder.md) records the finite form, `BWH` as `Q01` for starts of width $m$
with time horizon $2m$, checked by simulation for $n \le 12$ (`wedge_ladder.py`).

## What the kit has

The definitions `encodePair`, `pair_inverse_table` and `encode_xor_binary` are restated verbatim from the kit's main
branch (`Rule30SEPToPeriodTwo`, [93d98bb](https://github.com/WolframInstitute/Rule30PrizeKit/commit/93d98bb)), and the
chart follows the kit's `pair_backward`, `actual_boundary`, `actual_cone_chart`, `actual_peel_chart`,
`actual_endpoint_binary` and `actual_endpoint_finite_rank`, moved from the kit's full row with an alternating center to
the pinned kit's zero-driven left half. The kit's docstring states that no implication in either direction is proved
between `SEP`, `RW` or `BWH` and `Q01`. Here `BWH` $\Rightarrow$ `Q01` and `Q01` $\Rightarrow$ `SEP` are proved, and
`BinaryCTS` $\Leftrightarrow$ `Q01` is the exact stream form of `Q01`; none of these is in the kit's main branch or the
pinned kit. Nothing here proves `BWH`, `BinaryCTS` or `Q01`.
