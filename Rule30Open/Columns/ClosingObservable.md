---
title: A periodic column and any observable that closes the strip to its right
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ClosingObservable
headline: [closing_observable, affine_observable, center_xor, center_masked_two, center_parity]
kit: refines
kit_modules: [Rule30Jen, Rule30MaskedJen]
---

# A periodic column and any observable that closes the strip to its right

If column $j$ of the single-cell orbit is eventually periodic, then no sequence $h$ that, together with the cells
$j+1, \dots, j+w$, determines $a_t(j+w) \lor a_t(j+w+1)$ is eventually periodic. Special cases: the center column and
$a(1) \oplus a(2)$; the center column and $\lnot a(1) \land a(2)$; the center column and the parity of columns
$1, \dots, k$ for every $k \ge 1$; Jen's theorem for every pair of columns at distance at least 2 ($h$ the far column,
$w \ge 1$); the kit's `orCol` form ($w = 0$).

## Statement

Let $S_t = (a_t(j+1), \dots, a_t(j+w))$, $w \ge 0$. If $a_t(j+w) \lor a_t(j+w+1) = F(S_t, h_t)$ for all $t$, for some
$F$, then column $j$ and $h$ are not both eventually periodic (`closing_observable`). For $k > j$ and
$h_t = a_t(k) \oplus G(\text{cells strictly between } j \text{ and } k)$ this is `affine_observable`.

## Argument

1. Rule 30 updates cell $p$ from $a_t(p-1)$ and $a_t(p) \lor a_t(p+1)$. So $S_{t+1}$ is a function of $a_t(j)$, $S_t$
   and $a_t(j+w) \lor a_t(j+w+1) = F(S_t, h_t)$: the strip is a finite-state system driven by $(a(j), h)$.
2. Give column $j$ and $h$ a common start $T$ and period $P$. Among the $2^w + 1$ states $S_{T+mP}$,
   $0 \le m \le 2^w$, two agree, at $m < n$. The inputs agree at $T+mP+r$ and $T+nP+r$ for every $r$, so by step 1
   and induction on $r$ the strips agree too: every column $j, \dots, j+w$ repeats with period $(n-m)P$ from $T+mP$.
3. If $w \ge 1$, columns $j$ and $j+1$ both repeat, against Jen's adjacent theorem. If $w = 0$, $F(S_t, h_t)$ with
   empty $S$ repeats, so $a(j) \lor a(j+1)$ repeats; then
   $a_t(j-1) = a_{t+1}(j) \oplus (a_t(j) \lor a_t(j+1))$ repeats, and columns $j-1, j$ contradict the same theorem.
4. Corollaries choose $F$: $x \lor (x \oplus h)$ for $h = x \oplus y$; $x \lor h$ for $h = \lnot x \land y$;
   $s_{\text{last}} \lor (h \oplus G(s))$ for the affine form with $k \ge j + 2$ ($w \ge 1$, so $s_{\text{last}}$
   exists); for $k = j + 1$ the strip is empty, $G$ is a constant $g$, column $j+1$ is $h \oplus g$, and Jen's
   adjacent theorem applies directly. Parity is affine, since
   $\operatorname{par}(1..k) = a(k) \oplus \operatorname{par}(1..k-1)$.

## In Lean

`closed_agree` is steps 1 and 2: it shows by induction on $r$ that two times with equal strips (`strip`) and equal
inputs keep equal cells $j, \dots, j+w$, using `strip_get` to read a cell from the strip and `strip_ext` to rebuild
the strip from its cells. `closing_observable` takes the common period (`common_period`), applies the kit's
`pigeonhole` to the $2^w + 1$ strip states and then `closed_agree`; its two branches are step 3. For $w \ge 1$ it
applies `not_adjacent` to columns $j, j+1$. For $w = 0$, `hor` shows that $a(j) \lor a(j+1)$ repeats and `hleft`
derives column $j-1$ from it through `cell_left`, before `not_adjacent` applies to columns $j-1, j$. Step 4 is
`affine_observable`, which handles $k = j + 1$ separately through `not_adjacent` and otherwise calls
`closing_observable`; `center_xor` and `center_masked_two`, which call `closing_observable` with $j = 0$, $w = 1$; and
`center_parity`, which reduces to `affine_observable` through `lpar_append` and `strip_succ`.

The module states every result for the single-cell orbit (`Rule30Jen.cell`) only, and the center corollaries have no
`Rule30Prize.center` form. The argument itself uses only left permutivity, the pigeonhole on the strip and the
adjacent-column theorem, which holds for every row with a leftmost 1 (the kit's `Rule30FiniteConfigs.not_adjacent`,
and [AdjacentColumns](AdjacentColumns.md) here), so it should carry over to those rows; that form is not in the
module.

## What the kit has

The method is the kit's strip pigeonhole (`Rule30Jen.between_periodic`, which `jen` uses for columns at distance at
least 2), and it ends in the adjacent-column theorem `Rule30Jen.not_adjacent`. The case $w = 0$ is the kit's `orCol_not_eventuallyPeriodic` (`Rule30MaskedJen`). The kit states none of the observables
above: $a(1) \oplus a(2)$, $\lnot a(1) \land a(2)$, the parity of columns $1, \dots, k$, or the general closing and
affine forms. The same proof allows $F$ to read $a_t(j)$ as well; that form is not in the module.

## Limits

The theorem rules out only the pair: it excludes a periodic center column only if some $h$ satisfying the closing
hypothesis is already known to be eventually periodic, and none is.
