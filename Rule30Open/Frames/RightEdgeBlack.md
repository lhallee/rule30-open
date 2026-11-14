---
title: Over one period of the single cell's first N + 1 right diagonals, the doubling diagonals force at least L (2 + e_N)/2 black cells and L e_N/2 white cells, L = 2^(e_N)
category: frames
problems: [2]
status: proved
lean: Rule30Open.Frames.RightEdgeBlack
headline: [doubling_black, strip_black, strip_white]
kit: refines
kit_modules: [Rule30RightPeriods, Rule30Diagonals]
evidence: [computations/right_edge_density.py]
---

# Over one period of the single cell's first N + 1 right diagonals, the doubling diagonals force at least L (2 + e_N)/2 black cells and L e_N/2 white cells, L = 2^(e_N)

Let $R_j(t) = \mathrm{cell}(t, t - j)$ be the single cell's right diagonal $j$ and $e_j$ the least $e$ with
$R_j$ of period $2^e$ (the kit's `Rule30Diagonals.R` and `Rule30RightPeriods.leastExp`). Let $L = 2^{e_N}$ be the
common period of diagonals $0, \dots, N$. Let $B_J$ and $W_J$ be the black and white cells of diagonals
$0, \dots, J$ at times $0, \dots, L - 1$ (`stripBlack`, `stripWhite`, sums over diagonals of the kit's `cnt`).

## Statement (Lean)

- `doubling_black`: if $e_{j+1} = e_j + 1$, then for every start $a$ and every $m$, diagonal $j + 1$ has exactly
  $2^{e_j} m$ black cells at times $a, \dots, a + 2^{e_{j+1}} m - 1$: half of any multiple of its period.
- `leastExp_mono`: $e_i \le e_j$ for $i \le j$.
- `strip_black`: for every $J \le N$, $L\,(2 + e_J) \le 2 B_J$. For $J = N$: **the black density of the first $N + 1$
  right diagonals over their common period is at least $(2 + e_N) / (2(N + 1))$.**
- `strip_white`: for every $J \le N$, $L\, e_J \le 2 W_J$.

`#print axioms` gives propext, Classical.choice and Quot.sound. Classical.choice enters through the kit's
`leastExp`, which is defined with `Classical.choose`; the module adds no axiom.

## Argument

1. **One doubling diagonal** (`doubling_black`). The kit's `e_step` says $e_{j+1} = e_j + [R_{j+1}(2^{e_j}) = 1]$, so
   at a doubling diagonal that cell is black, and then `half_black` says every window of one period $2^{e_{j+1}}$ is
   exactly half black. Adding $m$ windows (`cnt_add`) gives $2^{e_j} m$.
2. **The strip, by induction on $J$** (`strip_black`). Diagonal 0 is the edge, black at every time (`R_zero`), and
   $e_0 = 0$: $2B_0 = 2L$. Going from $J$ to $J + 1$: if $e_{J+1} = e_J$, nothing is lost, since counts are
   nonnegative. If $e_{J+1} = e_J + 1$, then $L$ is the multiple $2^{e_{J+1}} \cdot 2^{e_N - e_{J+1}}$ of the period
   of diagonal $J + 1$ (by monotonicity), and that diagonal adds exactly $L/2$ black cells while $e$ grows by one.
   `strip_white` is the same induction with the complement (`cnt_not`), starting from $0$.

## What it means

Combined with [RightEdgeDensity](RightEdgeDensity.md) (white density at least $(2J - 2)/(5J)$ on the first $J$ right
diagonals over a period, any code), this gives a two-sided statement on the right-edge strip of the single cell.
White is at least about $2/5$. Black is at least $(2 + e_N)/(2(N+1))$, which is positive in the limit exactly when
$e_N \ge cN$. The kit's `per_bound` gives only $e_N \ge \log_2(N + 2) - 1$, so unconditionally the black bound tends
to 0. `per_upper_half` ($e_N \le N/2 + O(\log^* N)$) caps it at about $1/4$. The non-doubling diagonals contribute
nothing to the bound; controlling them is what a positive black density would need. In the computed range
(`right_edge_density`, $N + 1 \le 22$) the strip is about half black: 2,867 of 5,632 cells at $N + 1 = 22$, against
the bound 1,280.

## Relation to the kit

A consequence of `Rule30RightPeriods.half_black`, `e_step`, `e_mono`, `leastExp_spec`, `leastExp_zero`, `cnt_add` and
`Rule30Diagonals.R_zero`. The kit states the half-black property one period of one diagonal at a time. The lift to any
multiple of the period and the sum over the strip are this module.

## In Lean

`Rule30Open/Frames/RightEdgeBlack.lean` imports `Ruliology.CellularAutomata.Rule30RightPeriods`; the proofs are
induction and `omega`.
