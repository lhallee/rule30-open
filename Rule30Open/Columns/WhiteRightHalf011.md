---
title: Against a white right half, no left half within depth 32,751 keeps the center on 011 through 16 steps past its width
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.WhiteRightHalf011
headline: [white_right_leaves_011, psi011_gaps, leaves_by_lc, left_eq_lc, psiBitsC_spec, colC_testBit, rh_white]
kit: refines
kit_modules: [Rule30Realization, Rule30Coupled, Rule30PeriodTwoSideways, Rule30EtherThreeReach, Rule30Ether]
evidence: [computations/white_right_011.py, computations/finite_onset.py, computations/coupled.py]
---

# Against a white right half, no left half within depth 32,751 keeps the center on 011 through 16 steps past its width

An eventually periodic center column of a finite configuration repeats its block from time 0 in the row at its onset
([the finite-onset census](../../findings/columns/finite-onset-census.md)), and the first case of that question for a
block is the white right half. For $01$ it is the kit's open milestone `CQ01Empty`, settled for left halves within
depth 32,754 in [WhiteRightHalf](../PeriodTwo/WhiteRightHalf.md); for $001$ it is settled in
[EmptyRight](EmptyRight.md) through the trap `t001`. For $011$ the right half never settles next to the center
([the word 011](../../negative-results/columns/period-three-011.md)), so no trap is available. This module does for
$011$ what WhiteRightHalf does for $01$: the kernel computes the one row that keeps the center on $011$ to depth 32,768
in each phase and checks its gaps.

## Statement

Write $c_\varphi(t)$ for the column repeating $011$ from phase $\varphi$: white exactly when $t + \varphi$ is a
multiple of 3 (`col011 φ t`).

1. `white_right_leaves_011`. Let $x$ be a row whose cells right of the center are white and whose cells left of $-W$
   are white, with $W < 32{,}752$. Then for every phase $\varphi$ the center of its orbit differs from $c_\varphi$ at
   some time $t \le W + 16$.
2. `psi011_gaps`. For $\varphi < 3$ and every $W < 32{,}752$ some depth $d$ with $W < d \le W + 16$ is black in the
   row $\Psi_\varphi$ = `lc whiteRight (col011 φ) · 0` that keeps the center on $c_\varphi$.
3. `leaves_by_lc`, for every center column $c$: whenever the row $\Psi_c$ = `lc whiteRight c · 0` has a black depth
   in $(W, W + G]$, every row as in statement 1 leaves $c$ by time $W + G$.
4. `left_eq_lc`, for every row $x$ white right of the center: its cell at depth $d$ is cell $d$ of the row rebuilt for
   its own center column.
5. `rh_white`, `colC_testBit`, `psiBitsC_spec`: the computed number `psiBitsC c N` has bit $d$ equal to $\Psi_c$ at
   depth $d$, for $d \le N$.

## Argument

1. **The one candidate, for any center column** (the kit). The kit's `Rule30Realization` builds, for a right half $R$
   and a column $c$, the configuration `conf R c`: the right half driven by $c$ (`rh`), column $-1$ forced by the
   center's update (`ycol`), and every column to the left by left-permutivity (`lc`). A configuration is determined
   by its right half and its center column (`unique`), and column $-m$ at time $t$ reads $c$ only up to time $m + t$
   (`lc_congr`).
2. **A row determines its own candidate** (`left_eq_lc`). A row $x$ white right of the center is `conf` of the white
   right half and its own center column, by `unique` and `realize`, so its cell at depth $d$ is
   `lc whiteRight c' d 0` for $c'$ its center column.
3. **The death bound** (`leaves_by_lc`). If the center of $x$ followed $c$ through time $W + G$, then for the black
   depth $d \in (W, W + G]$ of $\Psi_c$, `lc_congr` gives `lc whiteRight c' d 0 = lc whiteRight c d 0`, which is black,
   so $x$ is black at depth $d > W$, against its left half lying within depth $W$. This is the half of the kit's exact
   death (`Rule30PeriodTwoSideways.exact_death_center`, for the alternating column) that the bound needs, for every
   column $c$.
4. **The candidate as numbers.** The white right half driven by $c$ is the kit's `drv` (`rh_white`), so the kit's
   `rowN` steps it as bit masks. `collectBits` collects one bit per time: column 1 at times below $N$ (`colOneN`) and
   the center at times up to $N$ (`centerN`), as the bits of two numbers (`collectBits_spec`). The left-permutive
   recurrence $x(t, -k-1) = x(t+1, -k) \oplus (x(t, -k) \lor x(t, -k+1))$, started at $k = 0$ with column 1 in the place
   of $x(t, 1)$, rebuilds the columns as numbers over time: `colC A B (m + 1)` is column $-m$, the kit's
   `lc whiteRight c m` at the times $t$ with $t + m \le N$ (`colC_testBit`). `WhiteRightHalf.psiLoop` collects bit 0 of
   each (`psiLoop_colC`), and `psiBitsC c N` is the row at depths $0, \dots, N$ (`psiBitsC_spec`).
5. **Gaps** (`gaps011_0`, `gaps011_1`, `gaps011_2`). `WhiteRightHalf.gapsCheck` marks the starts of 16 white depths in
   a row; the kernel finds none among the starts $1, \dots, 32{,}752$ of `psiBitsC (col011 φ) 32768`, for $\varphi =
   0, 1, 2$. A phase $\varphi \ge 3$ is the phase $\varphi \bmod 3$.

## The numbers

`python -m computations.white_right_011` runs the same loops in Python:

| phase | black cells at depths 1 to 32,768 | last black depth | longest white run |
|---|---|---|---|
| 0 | 16,434 | 32,768 | 15 |
| 1 | 16,371 | 32,764 | 13 |
| 2 | 16,392 | 32,768 | 13 |

These are the runs and last black depths that `python -m computations.finite_onset empty 011 --depth 32768` reports. The
longest run, 15, sets the gap 16 for all three phases; phases 1 and 2 alone would pass with 14. Each kernel check runs,
in one declaration, the loops of WhiteRightHalf's three checks (the driven column, the reconstruction and the gaps) and
the collection of the center, on numbers of up to 32,769 bits, so the three checks cost about three times its build
(about 40 seconds with a peak below 2 GB there); this is an estimate, not a run of this module, and one declaration
holds what WhiteRightHalf splits over three, so the peak may be higher.

```bash
python -m computations.white_right_011           # the table above, about a second
python -m computations.white_right_011 --lean    # the census section of the module
lake build Rule30Open.Columns.WhiteRightHalf011
```

`tests/test_white_right_011.py` checks the loops against `coupled.drive_column`, `coupled.center` and the big-integer
`coupled.psi` for $011$ and words of periods 2, 4 and 5, the gap check against a scan of every window, the theorem
against direct runs of whole finite rows (the truncation of the row at width $W$ leaves $011$ exactly at its first
black depth beyond $W$, and random left halves within depth $W$ leave by time $W + 16$), and the census section
against the module.

## What it covers

The open statement for $011$ against the white right half is that $\Psi_\varphi$ has infinitely many black cells in each
phase, the analog of `CQ01Empty` and the case of the white right half of the kit's `Rule30Coupled.CQ` for the column
$c_\varphi$; the bound here grows with the depth computed, and the white runs grow like those of a random sequence, so a
computation settles bounded cases only. The route the kit leaves for $011$ is its left-only statement `C3w` ([the
roadmap](../../ROADMAP.md)), which covers every right half; this module covers the white right half only. Statements 3
and 4 hold for every center column, so the same module, with a different column and depth, settles the white right half
for any block whose candidate row has bounded gaps to that depth.

## The kit

The kit's `Rule30Realization` has the candidate row for every right half and every column (`conf`, `lc`) with
`unique` and `lc_congr`; its `Rule30PeriodTwoSideways` has the exact death identity for the alternating column
(`exact_death_center`) and the milestone `CQ01Empty`. It states nothing about $011$ against the white right half:
its period-three results are the ether reductions of `Rule30EtherThree` and the trap `t001` for $001$.
