---
title: Constraining the free bits of column -1 by the right half lowers the entropy of the left-half statements for 001 and 011, and no finite left game closes
category: columns
problems: [1]
status: negative
kind: dead-end
evidence: [computations/constrained_left.py, computations/gap_traps.py, computations/three_runs.py]
---

# Constraining the free bits of column -1 by the right half lowers the entropy of the left-half statements for 001 and 011, and no finite left game closes

**Question.** Beside a center that repeats $001$ or $011$, the right half constrains column 1 at the white steps
([reading constraints](../../findings/columns/reading-constraints.md)), and column $-1$ there is column 1 xor the next
center cell. So the free bits of the kit's left-only statements, `C3s001` for $001$ and `C3w w011` for $011$, are
constrained: for $001$ their complements avoid $010$, $101$ and $1001$ ([ThreeRuns](../../Rule30Open/Columns/ThreeRuns.md),
in Lean), and for $011$ they avoid $11$ unless they are eventually black (computed at width 14). Does the constraint,
together with the finiteness of the left half, close the left side: a finite game with no surviving play, a search that
terminates, or a proof for a class of halves?

**Outcome.** The constraint lowers the entropy of the allowed column $-1$ from $1/3$ bit per step to 0.2042 for $001$
and 0.2314 for $011$, and the search reaches 1.4 to 1.5 times deeper for the same work, but it changes nothing in kind.
The halves that keep the constrained condition forever are in bijection with the allowed free bits, a set of positive
entropy, and the ones with periodic free bits are dense among them and eventually periodic in space, so every finite test that
does not see the left edge has a surviving play. Finiteness enters only as "white beyond depth $M$", and the halves to
kill at depth $M$ number about $2^{hM}$; past their width they die roughly as fair coins predict. Settled for restricted
classes: halves with eventually periodic free bits (Jen's theorem) and, by computation, every half of at most 92 cells
for $001$ and 85 for $011$, in every phase. The reduction of $001$ to the constrained statement is in Lean
([ConstrainedLeft001](../../Rule30Open/Columns/ConstrainedLeft001.md)).

## The conditions

The left half runs as Rule 30 on the cells left of the center, with column 0 replaced by the kit's effective boundary
$c'(t) = c(t) \land c(t + 1)$: white for $001$, $010$ for $011$. The *reading* at a white step is column 1, and column
$-1$ is the reading xor the next center cell (the kit's `col_m1_001`, `col_m1_011`). Write $b_i$ for the reading at the
free white step of period $i$.

| condition | block | column $-1$ at phases 0, 1, 2 | constraint on the readings | source | bits per step |
|---|---|---|---|---|---|
| `001-kit` | $001$ | $0, \lnot b_i, 1$ | none (`C3s001`) | kit, Lean | 1/3 |
| `001-runs` | $001$ | $0, \lnot b_i, 1$ | $b$ avoids $010$, $101$, $1001$ | ThreeRuns, Lean | 0.2042 |
| `011-kit` | $011$ | $\lnot b_i, 0, 1$ | none (`C3w w011`) | kit, Lean | 1/3 |
| `011-no00` | $011$ | $\lnot b_i, 0, 1$ | $b$ avoids $00$ | computed, width 14 | 0.2314 |
| `011-trap` | $011$ | $\lnot b_i, 0, 1$ | $b$ avoids $00$, $010$, $01110$, $011110$ | entered by halves of up to 16 cells, not forced | 0.1475 |

For $011$ the computed list $00$ is forced except for right halves whose readings are eventually white; then column
$-1$ is eventually $(1, 0, 1)$, periodic beside a periodic center, which the kit's `Rule30FiniteConfigs.jen` excludes in
a finite row. The bits per step are $\log_2$ of the spectral radius of the condition's automaton (`entropy`): for
`001-runs`, $\frac{1}{3}\log_2 \lambda$ with $1/\lambda$ the root of $x^5 = (1 - x)^2$; for `011-no00`, a third of
$\log_2$ of the golden ratio.

## 1. The columns as functions of the readings

Column $j - 1$ at step $t$ is column $j$ at step $t + 1$ xor (column $j$ or column $j + 1$ at step $t$), so the
readings fix every column, and column $-k$ at period $i$ depends on $b_i, \dots, b_{i + \lceil k/3 \rceil}$. Over
GF(2), with $b_0, b_1, \dots$ the readings of periods $i, i + 1, \dots$ (`column_anf`):

| column | $001$, phases 0, 1, 2 | $011$, phases 0, 1, 2 |
|---|---|---|
| $-1$ | $0$; $1 + b_0$; $1$ | $1 + b_0$; $0$; $1$ |
| $-2$ | $1 + b_0$; $b_0$; $1$ | $1 + b_0$; $0$; $b_1$ |
| $-3$ | $1$; $0$; $b_1$ | $1 + b_0$; $b_1$; $b_1$ |
| $-4$ | $1$; $b_0 + b_1$; $0$ | $1 + b_0 + b_1$; $0$; $1$ |
| $-5$ | $1 + b_0 + b_1$; $b_0 + b_1$; $1 + b_1$ | $1 + b_0 + b_0 b_1$; $1 + b_1$; $b_1 + b_2$ |
| $-6$ | $1 + b_0 + b_1$; $1 + b_0$; $b_2$ | $b_0 + b_1 + b_0 b_1$; $1 + b_2$; $b_1 + b_1 b_2$ |

The cells that take one value on every allowed sequence (`forced_cells`, over every allowed sequence of 14 periods,
columns $-1$ to $-36$):

- $001$, with or without the constraint: columns $-1$ to $-4$ as above and column $-8$ white at phase 2; none in
  columns $-9$ to $-36$. The constraint fixes no cell.
- $011$ without the constraint: columns $-1$, $-2$, $-4$ as above and column $-8$ black at phase 1; none in $-9$ to
  $-36$. With $00$ forbidden it adds column $-6$ black at phase 0 and column $-9$ white at phase 0, and none in $-10$ to
  $-36$; the trap's words fix cells as far as column $-13$ and none in $-14$ to $-36$.

So past column $-9$ (or $-13$) every cell of the half is a non-constant function of the readings. A forced black cell
in arbitrarily deep columns would have contradicted the white region left of a finite half; there is none.

## 2. The search, with and without the constraint

Cell $-1$ at step $t$ is bit $t$ of the starting half xor a function of its lower bits, so the halves of at most $M$
cells that keep the condition through step $M - 1$ are exactly as many as the allowed words of $M$ values of column
$-1$, $N(M) \approx 2^{hM}$ (`count_words`; the tests check the equality against a cell-by-cell run of every half of
up to 9 cells). `tree_failures` follows each of them with white cells beyond $-M$ until it fails, as
[the C3 search](../../findings/columns/left-half-c3.md) does. Every half of at most $M$ cells fails, in each of the three
phases:

| condition | $M$ | $N(M)$, all phases | margin past $M$ at $M$ = 20, 40, 60, (80) | largest margin | fair coins at $M$ |
|---|---|---|---|---|---|
| `001-kit` | 60 | 3,145,728 | 11, 22, 27 | 35, at $M = 56$ | 30.0 |
| `001-runs` | 92 | 2,273,205 | 7, 17, 17, 21 | 24, at $M = 90$ | 23.6 |
| `011-kit` | 60 | 3,145,728 | 12, 19, 24 | 26, at $M = 52$ | 30.0 |
| `011-no00` | 85 | 3,010,349 | 12, 11, 17, 19 | 24, at $M = 81$ | 25.6 |
| `011-trap` | 120 | 1,037,067 | 8, 10, 12, 14 | 25, at $M = 87$ | 20.8 |

The fair-coin margin is $hM/(1 - h)$, where the longest of $2^{hM}$ coin sequences fails. The survivors of the halves
of at most $M$ cells through step $M - 1 + j$, against $N(M + j)/2^j$, what fair coins past step $M - 1$ give:

| condition, $M$ | $j = 0$ | 10 | 20 | 30 |
|---|---|---|---|---|
| `001-kit`, 60 | 3,145,728 | 32,510 (coins 32,768) | 322 (320) | 3 (3.0) |
| `001-runs`, 92 | 2,273,205 | 8,430 (8,969) | 70 (36.8) | 0 (0.1) |
| `011-kit`, 60 | 3,145,728 | 33,370 (32,768) | 136 (320) | 0 (3.0) |
| `011-no00`, 85 | 3,010,349 | 14,724 (14,580) | 26 (69.1) | 0 (0.3) |
| `011-trap`, 120 | 1,037,067 | 2,906 (2,845) | 12 (7.7) | 0 (0.0) |

The number of surviving halves grows with depth as $2^{hM}$ exactly, and past the width they thin out at the coin rate,
$2^{-(1 - h)}$ per step. The constraint lowers $h$, so at a fixed budget of about $2^{21}$ halves the search reaches
$M = 92$ for $001$ and $85$ for $011$ instead of 60, and the coin model predicts margins growing as $hM/(1 - h)$,
0.26 and 0.30 per cell of width instead of 0.5 (the measured largest margins are in the table). That is the whole gain: a smaller exponent, not a terminating search.

## 3. Why no finite left game closes

Let $X$ be the allowed sequences of readings and $Y$ the left halves, finite or not, that keep the condition forever.

1. **$Y$ is a copy of $X$.** The triangular structure of step 2 makes the map from a half to its column $-1$ a
   bijection from $Y$ onto the sequences that $X$ allows, continuous both ways (cell $-k$ depends on the first $k$
   values of column $-1$, and the reverse). This is the conjugacy of [the period-two shift
   model](../../findings/period-two/shift-model.md) and of the kit's `Rule30ZeroBoundary` for the white boundary, with
   the boundary $010$ entering for $011$ as a known input. So $Y$ is uncountable for every condition here.
2. **Periodic free bits give halves periodic in space.** If the readings repeat with period $q$, column $-1$ and the
   boundary repeat with period $3q$, the sideways map runs on pairs of cyclic words of length $3q$, a finite set, and
   the columns repeat: the half is eventually periodic in space (`periodic_half`). By Jen's argument it is never
   finitely supported: two adjacent columns that repeat from step 0 make every column to the left repeat from step 0,
   and a column far left of a finite half is white for more than a period. Spatial periods, with the number of
   readings of period dividing $q$ in parentheses:

   | $q$ | `001-kit` | `001-runs` | `011-kit` | `011-no00` |
   |---|---|---|---|---|
   | 1 | 12 (2) | 12 (2) | 12 (2) | 12 (1) |
   | 2 | 12 (2), 84 (2) | 12 (2) | 12 (2), 84 (2) | 12 (1), 84 (2) |
   | 3 | 12 (2), 135 (6) | 12 (2) | 12 (2), 135 (6) | 12 (1), 135 (3) |
   | 4 | 12 (2), 84 (2), 100 (8), 138 (4) | 12 (2) | 12 (2), 84 (2), 138 (12) | 12 (1), 84 (2), 138 (4) |
   | 5 | 12 (2), 105 (5), 540 (5), 795 (10), 2145 (10) | 12 (2), 2145 (5) | 12 (2), 540 (5), 795 (5), 2145 (20) | 12 (1), 540 (5), 2145 (5) |
   | 6 | 12 (2), 84 (2), 135 (6), 1962 (24), 8370 (30) | 12 (2), 1962 (12) | 12 (2), 84 (2), 135 (6), 342 (6), 1962 (12), 8370 (36) | 12 (1), 84 (2), 135 (3), 342 (6), 8370 (6) |

   The halves of spatial period 12 are the period-three ether's left parts (the kit's `C3w_011_ether` is one for
   $011$); forbidding $00$ removes one of the two for $011$ and keeps the other.
3. **They are dense.** The shifts $X$ here are irreducible shifts of finite type, whose periodic points are dense; by 1
   their halves are dense in $Y$. So a test that looks at the half within any bounded distance of column $-1$, over any
   bounded time, passes some half that is eventually periodic in space, and any finite game on windows next to column $-1$ (with
   the constraint automaton in its state, at any width) has a surviving play. This is [the barrier of the
   presheaf](sheaf-sections.md), on the left side and with constrained free bits.
4. **Finiteness is a condition at the far end.** A finite half differs from those in item 2 only in its tail, white
   from some depth on. The left edge moves away from column $-1$ at one cell per step, its diagonals are eventually
   periodic (the kit's `Rule30Diagonals.D_periodic`) but reach column $-1$ only through a bulk that grows with time,
   and the sideways map's property that only white maps to white is the light cone again. The only finite use of
   finiteness found is the depth-$M$ search of step 2, one $M$ at a time.

## 4. What is proved for restricted classes

- **Eventually periodic free bits:** no finite half, for every block (Jen's argument, section 3, item 2; in a row, the kit's
  `Rule30FiniteConfigs.jen` or masked Jen).
- **Bounded width:** every half of at most 92 cells for `001-runs` and 85 for `011-no00` fails, from every phase
  (computation); with the trap's words for $011$, which are not forced, every half of at most 120 cells. In a row
  whose center repeats $001$ from time $T$, this covers the rows whose left half is within depth
  92 at the time from which the kit's skeleton and the 14th reading of ThreeRuns both hold. Without the constraint the
  kit's C search reaches width 70 for `C3s001` and this one 60.
- **The reduction for $001$** ([ConstrainedLeft001](../../Rule30Open/Columns/ConstrainedLeft001.md), Lean):
  `C3r001`, the kit's `C3s001` with the free bits constrained as above, excludes $001^\infty$ as a tail of the center
  column.

No statement for unbounded width was found, with or without the constraint, and the counts above give no reason to
expect a finite certificate: the constrained statement is still a finite object avoiding a set of positive entropy.

## Formalization

The reduction is in Lean. The bounded-width result can be checked by the kernel the way
[LeftHalf0001](../../Rule30Open/Columns/LeftHalf0001.md) checks `C3 w0001` at depth 88: run the kit's lane checker
(`Rule30ZeroBoundaryLanes`, the white boundary of $001$) with the run-length state of the free bits carried per lane,
and let a lane die when a run ends too short. The lanes still enumerate every word of free bits, so the kernel's work
is that of the unconstrained check at the same depth; reaching depth 92 cheaply would need lanes indexed by the allowed
words only. For $011$ the constraint itself is computed, not proved, and would first need a certificate like
ThreeRuns at width 14.

## Reproduce

```bash
python -m computations.constrained_left --columns 6 --forced 36 --periodic 6   # about 1 min
python -m computations.constrained_left --tree 60 --conditions 001-kit,011-kit   # about 2 min
python -m computations.constrained_left --tree 92 --conditions 001-runs          # about 1 min
python -m computations.constrained_left --tree 85 --conditions 011-no00          # about 2 min
python -m computations.constrained_left --tree 120 --conditions 011-trap         # about 1 min
```

The times are on a loaded machine with four cores. `tests/test_constrained_left.py` checks the search, its branch counts
and the survivor histograms against a cell-by-cell run of every half of up to 9 cells for each condition and phase, the
entropies against the closed forms above, the sideways columns against a forward run of the half that the readings
determine, the column formulas of $001$ worked by hand, and that the periodic halves return to themselves after a
period.
