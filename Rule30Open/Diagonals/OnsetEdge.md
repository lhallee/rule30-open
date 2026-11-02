---
title: The edge where two Rule 30 histories first differ moves by a three-case law, and for the single cell against its translate by P it passes diagonal j exactly when every diagonal up to j repeats with period P; an edge that gains depth at rate 2/3 gives black center runs of slope 3/13
category: diagonals
problems: [2]
status: proved
lean: Rule30Open.Diagonals.OnsetEdge
headline: [diffEdge_left, diffEdge_stay, diffEdge_retreat, agree_below_add, edge_right_iff, settling_of_edgeBound, black_run_le_of_edgeBound]
kit: new
kit_modules: [Rule30Jen, Rule30Diagonals, Rule30CenterRuns]
evidence: [computations/onset_edge.py]
---

# The edge where two Rule 30 histories first differ moves by a three-case law, and for the single cell against its translate by P it passes diagonal j exactly when every diagonal up to j repeats with period P; an edge that gains depth at rate 2/3 gives black center runs of slope 3/13

[SettledSlope](SettledSlope.md) turns onsets $T_j \le \lceil 3j/2 \rceil + \delta$ of the left diagonals
$D_j(t) = \mathrm{cell}(t, j - t)$ into black center runs of slope $3/13$, and
[linear settling leads](../../negative-results/diagonals/linear-settling-leads.md) locates the onsets at the left edge
of the chaotic region. This module makes that edge exact. It is the leftmost cell where the single cell's pattern and
its own translate by $P$ steps and $P$ cells differ, it moves by a local law, and the running maximum of the onsets
is the time it passes each diagonal. Linear settling becomes one inequality about one moving point.

## Statement

Let $a, b$ be any two rows and $X = $ `evolve a`, $Y = $ `evolve b` their Rule 30 histories. Say they have their
*edge* at $L$ at time $t$ if $X(t, x) = Y(t, x)$ for every $x < L$ and $X(t, L) \ne Y(t, L)$.

- `agree_below_succ`, `agree_below_add`: if $X(t, x) = Y(t, x)$ for $x < L$, then $X(t + n, x) = Y(t + n, x)$ for
  $x < L - n$. The edge moves left by at most one cell per step.
- `diffEdge_left`: if the edge is at $L$ and the shared cell $L - 1$ is white, the edge is at $L - 1$ at time
  $t + 1$.
- `diffEdge_stay`: if the shared cell $L - 1$ is black and the copy that is white at $L$ is also white at $L + 1$,
  the edge is at $L$ at time $t + 1$.
- `diffEdge_retreat`: if the shared cell $L - 1$ is black and the copy that is white at $L$ is black at $L + 1$, the
  copies agree left of $L + 1$ at time $t + 1$, and they differ at $L + 1$ exactly when the other copy is black at
  $L + 1$ or $L + 2$.

(The two theorems with a white copy name it $a$; the hypotheses are symmetric in $a$ and $b$, so they apply to either
copy.) Now let $X$ be the single cell and $Y(t, x) = X(t + P, x - P)$, its translate, which is the history of the row
$X(P, \cdot - P)$ (`evolve_translate`). On the left diagonal $j$, $Y(t, j - t) = D_j(t + P)$.

- `edge_right_iff`: $X(t, x) = Y(t, x)$ for every $x \le j - t$ if and only if every diagonal $i \le j$ repeats with
  period $P$ from time $t$: $D_i(s + P) = D_i(s)$ for all $s \ge t$.

So with $d(t) = L(t) + t$ the diagonal of the edge, $d$ never decreases, and the least $t$ with $d(t) > j$ is
$\max_{i \le j} T_i^P$, where $T_i^P$ is the onset of $D_i$ with respect to $P$. The edge hypothesis is
$$\mathrm{EdgeBound}(c):\quad \text{for every } t \text{ there is } P > 0 \text{ with } X(t, x) = X(t + P, x - P)
\text{ whenever } 3(x + t) + c < 2t,$$
that is, $d(t) \ge (2t - c)/3$ for the translate by some period $P$ that may depend on $t$. It is open.

- `repeats_of_edgeBound`, `settling_of_edgeBound`: under $\mathrm{EdgeBound}(c)$ every diagonal $i \le j$ repeats
  with one period from time $\lfloor (3j + c)/2 \rfloor + 1$, so $D_j$ repeats from
  $\lceil 3j/2 \rceil + \lceil c/2 \rceil + 1$.
- `black_run_le_of_edgeBound`: under $\mathrm{EdgeBound}(c)$, if the antiphase alternations of every settled pair
  $j \le J$ are eventually bounded by $A$ (`AltBound` of SettledSlope), a black run of the center column of length $L$
  from time $a \ge 1$ with $\lfloor 8a/13 \rfloor \le J$ has
  $$13 L \le 3a + 130 A + 130 (\lceil c/2 \rceil + 1) + 260.$$

## Argument

1. **The law.** Rule 30 is $x'_i = x_{i-1} \oplus (x_i \lor x_{i+1})$. Cells $i < L - 1$ of the next row read only
   cells left of $L$, so they agree. Cell $L - 1$ reads $x_{L-2}$ and $x_{L-1}$, which are shared, and $x_L$: if
   $x_{L-1} = 0$ the OR is $x_L$, which differs, so the copies differ at $L - 1$; if $x_{L-1} = 1$ the OR is 1 in both
   and they agree. Cell $L$ is then $1 \oplus (x_L \lor x_{L+1})$: the copy black at $L$ gives 0, and the copy white at
   $L$ gives $\lnot x_{L+1}$, so the copies differ at $L$ exactly when the white copy is white at $L + 1$. In the last
   case cell $L + 1$ is $x_L \oplus (x_{L+1} \lor x_{L+2})$, which is $0 \oplus 1 = 1$ in the white copy and
   $1 \oplus (x_{L+1} \lor x_{L+2})$ in the black copy. Each theorem rewrites the three cells and checks the Boolean
   cases.
2. **Diagonals left of the edge stay left.** A cell of diagonal $j$ moves left one cell per step, and the edge at most
   one (`agree_below_add`), so a diagonal strictly left of the edge at time $t$ is so at every later time.
3. **The characterization** (`edge_right_iff`). If the copies agree on $x \le j - t$ at time $t$, they agree on
   $x \le j - s$ at every $s \ge t$ (step 2), and the cell $x = i - s$ of diagonal $i \le j$ gives
   $D_i(s) = D_i(s + P)$. Conversely, if every $D_i$, $i \le j$, repeats from $t$, each cell $x \le j - t$ with
   $x + t \ge 0$ is on such a diagonal, and every cell with $x < -t$ is white in both copies, left of the seed's light
   cone (`cell_eq_false_of_lt`).
4. **The bridge.** At $t = \lfloor (3j + c)/2 \rfloor + 1$ every $x \le j - t$ has $3(x + t) + c \le 3j + c < 2t$, so
   $\mathrm{EdgeBound}(c)$ gives the agreement of step 3, and every diagonal $i \le j$ repeats from $t$, which is at
   most $\lceil 3j/2 \rceil + \lceil c/2 \rceil + 1$ (`omega`). `black_run_le_of_settling` of SettledSlope with
   $\delta = \lceil c/2 \rceil + 1$ gives the run bound.

## The range of the hypothesis

`onset_edge single` runs the vector of diagonals of `settled_slope.stream` and reads $d(t)$ as the lowest set bit of
$v_t \oplus v_{t+P}$, with the law checked at every step:

- With $P = 32$, diagonals $j \le 200{,}000$ and 300,600 steps: no step violates the law, the least $t$ with
  $d(t) > j$ equals $\max_{i \le j} T_i^{32}$ from `settled_slope.stream` at every depth $j \le 200{,}000$, and
  $3 d(t) \ge 2t$ for every $t \le 300{,}001$ (past that time the edge is beyond the computed diagonals), so
  $\mathrm{EdgeBound}(0)$ holds there with $P = 32$; past $t = 1{,}000$ the margin $3d(t) - 2t$ is at least 332. With
  $P = 16$ the same holds for $j \le 87{,}866$ and $t \le 131{,}800$; the first diagonal of period 32 stops that
  edge.
- The edge gains $0.7519$ depth per step past depth 400 (batch-means standard error 0.0019), against the $2/3$ that
  $\mathrm{EdgeBound}$ needs; its moves and their comparison with random rows are in
  [onset edge](../../findings/diagonals/onset-edge.md).

So the theorems apply only to the computed range, where computation already bounds the runs. Asymptotic content needs
$\mathrm{EdgeBound}(c)$ for all $t$ and a sublinear alternation bound, both open.

## What it means

**The onset front is a single point that moves by a local law.** The leads of
[linear settling leads](../../negative-results/diagonals/linear-settling-leads.md) stop at the transient, the defect
bits that the settled side does not determine. Here the defect bits are the edge's moves: a left move reads only the
settled side (the shared cell $L - 1$ is white), and a stay or a retreat reads the two copies at $L$, $L + 1$ and
$L + 2$, which are in the transient. A slope below $3/2$ for the onsets is exactly a long-run depth gain above $2/3$
for this point.

**What it does not give.** $\mathrm{EdgeBound}$ is a law of large numbers for the edge, as the front walk's mean step
is in [FrontWalker](FrontWalker.md); the law reduces it to the frequencies of local cases at the edge, and does not
bound them. A fixed $P$ fails at the first diagonal of larger period, which is why $\mathrm{EdgeBound}$ lets $P$
depend on $t$.

## In Lean

`onsetEdge_step` unfolds one step of `evolve`. The three law theorems rewrite the cells of the next row with the
agreement hypothesis and close the Boolean cases by `decide`. `agree_below_add` is an induction on $n$.
`evolve_translate` is an induction on $n$ with `omega` for the positions. `edge_right_iff` goes through `D_eq_evolve`
(`evolve_single_eq_cell` of [Official](../Foundations/Official.md)) and the kit's `cell_eq_false_of_lt`. The axioms are
`propext`, `Classical.choice` and `Quot.sound`.

## Relation to the kit

The pinned kit's `Rule30Diagonals` defines the left diagonals and proves them eventually periodic; `Rule30CenterRuns`
gives $L \le a$, which SettledSlope uses. On the kit's main branch, after the pinned revision, `Rule30FrontLaw` has the
law of one diagonal given the two before it settled (`D_front_law`), which says when the edge leaves a diagonal whose
two predecessors are settled: it stays on it while the shared cell is white and leaves at the first black one, without
saying how far; `Rule30FrozenRuler` keeps the lowest difference of two right-edge codes, and
`Rule30DividedDifference` (`Front.mode_left_edge`) keeps the left edge of a linear mode when both backgrounds are white
below it. The three-case law for two arbitrary rows, the characterization of the running maximum of the onsets as the
edge of the seed against its translate, and the conditional slope from an edge rate are in neither revision.

## Reproduce

```bash
python -m computations.onset_edge single --depth 200000 --period 32   # law, running maximum, EdgeBound(0), about 2.5 min
python -m computations.onset_edge single --depth 87866 --period 16    # the same for period 16, about 30 s
```
