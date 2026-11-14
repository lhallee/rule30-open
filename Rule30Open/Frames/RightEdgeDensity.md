---
title: On the right edge, 3 W + 2 W' >= 2J - 2 for the white bits among the first J of every code and its image, so over one period at least (2J - 2)/5 of the single cell's first J right diagonals are white; the doubling diagonals force black density at least (2 + e_{J-1})/(2J), which is positive only if the exponents grow linearly
category: frames
problems: [2]
status: proved
lean: Rule30Open.Frames.RightEdgeDensity
headline: [RightEdgeDensity.local_ineq, RightEdgeDensity.two_black_le, RightEdgeDensity.white_step, RightEdgeDensity.orbit_white, RightEdgeDensity.periodic_white]
kit: new
kit_modules: [Rule30RightPeriods]
evidence: [computations/right_edge_density.py]
---

# On the right edge, 3 W + 2 W' >= 2J - 2 for the white bits among the first J of every code and its image, so over one period at least (2J - 2)/5 of the single cell's first J right diagonals are white; the doubling diagonals force black density at least (2 + e_{J-1})/(2J), which is positive only if the exponents grow linearly

In the frame of the right edge a row is a code $y$: bit $e$ is the cell $e$ places left of the edge. One step of rule
30 is $T(y)_e = y_e \oplus (y_{e-1} \lor y_{e-2})$ with $y_{-1} = y_{-2} = 0$ (`codeStep`, the same definition as the
kit's `Rule30Equivalents.Odometer.G`). The single cell's code at time $t$ is $T^t(1)$, and bit $e$ of it is the right
diagonal $R_e(t) = \mathrm{cell}(t, t - e)$, purely periodic with period $2^{e_e}$ (`Rule30RightPeriods`). Let
$W_J(y)$ be the number of white bits among $0, \dots, J - 1$, and $L_J = 2^{e_{J-1}}$ the period of the first $J$
diagonals.

## Statement

**Proved in Lean** (`Rule30Open.Frames.RightEdgeDensity`):

- `local_ineq`: with $\psi(0,0) = 0$, $\psi(0,1) = 1$, $\psi(1,\cdot) = 2$,
  $2[a \oplus (b \lor c) = 1] + \psi(b, c) \le 3[a = 0] + \psi(a, b)$ (the potential of
  [RowWhiteDensity](../Foundations/RowWhiteDensity.md)).
- `two_black_le`, `white_step`: for every code $y$ and every $J$, $2\,\mathrm{black}_J(Ty) \le 3W_J(y) + 2$, so
  $3W_J(y) + 2W_J(Ty) \ge 2J - 2$.
- `orbit_white`: along any orbit $f_{i+1} = T f_i$,
  $2JP + 2W_J(f_0) \le 5\sum_{i<P} W_J(f_i) + 2W_J(f_P) + 2P$.
- `periodic_white`: if the first $J$ bits return after $P$ steps, $5\sum_{i<P} W_J(f_i) \ge (2J - 2)P$. For the single
  cell with $P = L_J$: **over one period, at least $(2J - 2)/5$ of its first $J$ right diagonals are white on average.**

**On paper, from the kit** (`Rule30RightPeriods.half_black`, `e_step`, `per_bound`):

- **Black cells from the doublings.** Over one period $L_J$, the first $J$ right diagonals of the single cell hold at
  least $L_J (1 + e_{J-1}/2)$ black cells and at least $L_J\, e_{J-1}/2$ white cells. So the black density of the strip
  is at least $(2 + e_{J-1})/(2J)$.

## Argument

1. **Telescoping along the code.** Pad the code with two white bits below bit 0. Then
   $T(y)_e = a \oplus (b \lor c)$ with $(a, b, c) = (y_e, y_{e-1}, y_{e-2})$, which is the rule 30 step read in row
   order. Summing `local_ineq` over $e = 0, \dots, n - 1$, the $\psi$ terms telescope from
   $\psi(y_{-1}, y_{-2}) = 0$ to $\psi(y_{n-1}, y_{n-2}) \le 2$ (`telescope`). With $\mathrm{black} + \mathrm{white} = J$
   this gives `white_step`. Summing over $P$ steps gives `orbit_white`, and a returning orbit cancels the boundary
   terms.
2. **The doubling diagonals.** By `e_step` the exponent grows by one exactly at the doubling diagonals, so among
   diagonals $1, \dots, J - 1$ there are exactly $e_{J-1}$ of them ($e_0 = 0$). At a doubling diagonal $m$,
   `half_black` says every window of one period $2^{e_m}$ is exactly half black. $L_J$ is a multiple of $2^{e_m}$, so
   over $L_J$ times diagonal $m$ has $L_J/2$ black and $L_J/2$ white cells. Diagonal 0, the edge, is black. The other
   diagonals contribute at least 0.

## Numbers (computed)

`right_edge_density`:

- **The constant 2 is attained.** Over all codes of $J$ bits, the least value of $3W_J(y) + 2W_J(Ty) - 2J$ is $-2$
  for every $J \le 12$.
- **The strip of the single cell over one period,** $J \le 22$:

| $J$ | 4 | 8 | 12 | 16 | 17 | 22 |
|---|---:|---:|---:|---:|---:|---:|
| $L_J$ | 4 | 32 | 64 | 128 | 256 | 256 |
| $e_{J-1}$ | 2 | 5 | 6 | 7 | 8 | 8 |
| black cells | 10 | 140 | 407 | 1,056 | 2,240 | 2,867 |
| bound $L_J(1 + e_{J-1}/2)$ | 8 | 112 | 256 | 576 | 1,280 | 1,280 |
| black density | 0.625 | 0.547 | 0.530 | 0.516 | 0.515 | 0.509 |
| white cells | 6 | 116 | 361 | 992 | 2,112 | 2,765 |
| bound $(2J - 2)L_J/5$ | 4.8 | 89.6 | 281.6 | 768 | 1,638.4 | 2,150.4 |

Both strips are close to half black, against bounds of about $2/5$ white and $(2 + e_{J-1})/(2J)$ black.

## What it means

- **White cells.** The white bound is unconditional and uniform in $J$: density at least $2/5 - 2/(5J)$ on the first
  $J$ right diagonals over a period, and by `orbit_white` over any time window up to a boundary term of $2J/5$. It is
  the right-edge companion of [SkeletonWhiteDensity](../Diagonals/SkeletonWhiteDensity.md), with constant 2 instead
  of 4 because the telescope starts at the edge, where both missing bits are white.
- **Black cells.** The doubling diagonals give black density at least $(2 + e_{J-1})/(2J)$. The kit's `per_bound`
  gives only $e_j \ge \log_2(j + 2) - 1$, so this tends to 0. A positive lower black density on the right-edge strip
  follows from this route exactly when $e_J \ge cJ$ for some $c > 0$. Then the bound is at least about $c/2$, and the
  kit's `per_upper_half` ($e_j \le j/2 + O(\log^* j)$) caps what it can give at about $1/4$. The other diagonals, those
  that do not double, are where the black cells are not controlled. In the computed range $e_{21} = 8$ (table above), and
  [right-edge cycles](../../findings/complexity/right-edge-cycles.md) finds 36 doublings at the levels $n \le 84$,
  about $0.43n$; if that rate held (a heuristic), the bound would be about $0.21$.
- Neither statement reaches the center column, which reads diagonal $t$ at time $t$, inside its first period.

## Relation to the kit

The kit proves `half_black` (every period of a doubling diagonal is half black) and the bounds on $e_j$; summing it
over the doubling diagonals of a strip is a two-line corollary that neither the kit nor
[right-edge cycles](../../findings/complexity/right-edge-cycles.md) states (a search for "half", "antiperiod" and
"density" in both finds `half_black`, `antiperiod`, `leastExp_antiperiod` and their uses, not the strip count). The
white bound and its Lean proof are new. The potential is [RowWhiteDensity](../Foundations/RowWhiteDensity.md)'s,
applied along the code.

## In Lean

`Rule30Open/Frames/RightEdgeDensity.lean`, core Lean with no imports: the code step, the eight-case `decide` for the
local inequality, and induction with `omega`. The bridge from codes to the single cell's diagonals is the kit's
(`Rule30Equivalents.Odometer.row`, `TFunction.testBit_orbit`); it is not restated here, and the black-cell corollary
is not formalized.

## Reproduce

```bash
python -m computations.right_edge_density   # about 5 s
```

`tests/test_right_edge_density.py` checks the codes against a direct rule 30 run of the single cell, the slack constant
for $J \le 9$, and both bounds of the strip for $J \le 12$.
