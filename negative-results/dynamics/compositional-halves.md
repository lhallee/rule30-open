---
title: A compositional proof through the center needs both halves' own dynamics, the left half's from a finite start; either half can be replaced by a causal adversary that makes the center eventually periodic, and at period one the left half alone forbids only the black tail, which Jen's theorem forbids
category: dynamics
problems: [1]
status: negative
kind: dead-end
---

# A compositional proof through the center needs both halves' own dynamics, the left half's from a finite start; either half can be replaced by a causal adversary that makes the center eventually periodic, and at period one the left half alone forbids only the black tail, which Jen's theorem forbids

**Question.** The center column is the one solution of a feedback loop between the two halves, each driven by the
center (the kit's
[`CoupledHalves`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/equivalents/Rule30Equivalents/CoupledHalves.lean)).
Can Problem 1 be proved compositionally, from a property of the left half and a property of the right half, each
stated for that half alone and joined at the center?

**Outcome.** Only through properties as hard as the problem. Either half can be replaced by a causal adversary that
makes the center eventually periodic: the left half by a Rule 30 left half from another start (the kit's realization
theorem), the right half by a free column that holds the center at $1, 1, 0, 0, 0, \ldots$ against the single cell's
own left half. So a proof must use that the left half starts finite, which is Jen's hypothesis, and the update rule of
the right half, beyond causality and beyond its triangular, invertible form. At period one these two settle the
question: Jen's theorem excludes the black tail, and the OR latch of column 1 with Jen's theorem the white tail. For a
word with both colors, an eventual period needs the right half to emit at its white times a signal that never becomes
periodic and the finite left half to match it cell for cell. Where the right half's output provably locks, Jen's theorem
closes the case, which is how blocks are excluded one by one; for the other words the two sides of the match, the left
half's check and the right half's channel, are open statements of the kit and of this repository. This is where the
route stops.

## The coupled system

Write $x_j(t)$ for cell $j$ at time $t$ and $c(t) = x_0(t)$; one step is
$x_j(t + 1) = x_{j-1}(t) \oplus (x_j(t) \lor x_{j+1}(t))$. The cells $j \le -1$ evolve as the left half driven by
column 0 from its start $s$ (the kit's `Rule30DrivenLeft.L`), the cells $j \ge 1$ as the right half driven by column 0
from its start $r$ (`Rule30Ether.drv`). Column $-1$ at time $t$ reads the driver only at times before $t$, and so does
column 1 (the kit's causality lemmas `CoupledHalves.L_causal` and `drv_causal`).

Call a map $G$ from sequences to sequences a *behavior* when $G(c)(t)$ depends only on $c(0), \ldots, c(t - 1)$. The
halves give the behaviors $F_L^s(c)$, column $-1$, and $F_R^r(c)$, column 1; write $F_L$ and $F_R$ for the white
starts of the single cell. For behaviors $G_L$ and $G_R$ the coupled system

$$u(0) = 1, \qquad u(t + 1) = G_L(u)(t) \oplus \bigl(u(t) \lor G_R(u)(t)\bigr)$$

has exactly one solution, built one step at a time, since the right side reads $u$ only up to time $t$. For
$G_L = F_L$ and $G_R = F_R$ it is the single cell's center column, and Problem 1 says that it is not eventually periodic
(`CoupledHalves.center_solves`, `eq_center_of_solves`, `problem1_iff_coupled_halves`). An *adversary* is a behavior put
in place of $F_L$ or $F_R$. The *black tail* and the *white tail* are a center that is eventually black and one that is
eventually white.

## The left half under a periodic driver

**Exact arrival.** Two left starts that agree on the cells $-1, \ldots, -(k - 1)$ and differ at $-k$, driven by one
driver, give the same column $-1$ at times $0, \ldots, k - 2$ and different values at time $k - 1$: the rightmost
difference moves right one cell per step and never cancels (left permutivity). So two left halves driven by one driver
that emit the same column $-1$ from some time on are equal at that time.

**Jen's theorem for driven left halves.** Let the driver $c$ be eventually periodic and let the start $s$ have finitely
many black cells, with $s$ or $c$ not all white. Then column $-1$ of the driven left half is not eventually periodic.
If both are white, the half stays white.

*Proof.* If $s$ is white, let $t_0$ be the first black time of $c$. At time $t_0 + 1$ cell $-1$ is
$0 \oplus (0 \lor 1) = 1$ and every cell left of it is white, so from then on the half runs from a nonzero finite start
under a driver that is still eventually periodic. So let the leftmost black cell of $s$ be at $-m$, $m \ge 1$. It is at
$-(m + t)$ at time $t$, whatever the driver: the cell left of it sees $0 \oplus (0 \lor 1)$ and the cells further left
see only white cells. Suppose column $-1$ is eventually periodic; then it and $c$ repeat with one period $P$ from one
time $T$. The halves at times $T$ and $T + P$ are driven by one sequence, $c(T + i) = c(T + P + i)$ for $i \ge 0$, and
emit the same column $-1$, so by exact arrival they are equal. But their leftmost black cells are at $-(m + T)$ and
$-(m + T + P)$. $\square$

**Masked form.** At a black time the system reads $u(t + 1) = \lnot G_L(u)(t)$, so column $-1$ is pinned to
$\lnot u(t + 1)$ there. Let $G_L = F_L^s$ with $s$ finite. If the solution has period $P$ from $T$, column $-1$ repeats
with period $P$ at the black times from $T$ on; by Jen's theorem it does not repeat with period $P$ at the white times
from $T$ on, and neither does column 1, which differs from it there by $u(t + 1)$.

## Either half can be replaced

**The right half.** Fix a left behavior $G_L$, and call a sequence $u$ with $u(0) = 1$ *left admissible* when
$G_L(u)(t) = \lnot u(t + 1)$ at every $t$ with $u(t) = 1$. Then $u$ is the solution for some right behavior if and only
if it is left admissible. At a black time the system reads $u(t + 1) = G_L(u)(t) \oplus 1$, which gives the condition.
Conversely, take the free column $G_R(v)(t) = G_L(u)(t) \oplus u(t + 1)$, which ignores $v$, or the adversary of the
same form as the right half of Rule 30,

$$G_R(v)(0) = 0, \qquad G_R(v)(t + 1) = v(t) \oplus g(t + 1),$$

with $g(t) = u(t - 1) \oplus G_L(u)(t) \oplus u(t + 1)$ at each white time $t \ge 1$ of $u$ and $g(t) = 0$ at the
others. If the solution agrees with $u$ up to time $t$, both behaviors read the same prefix, so at a black time
$u(t + 1) = \lnot G_L(u)(t)$ by admissibility, and at a white time $G_L(u)(t) \oplus G_R(u)(t) = u(t + 1)$ by the
choice of $G_R$. The right half of Rule 30 has column 1 at time $t + 1$ equal to $c(t) \oplus (x_1(t) \lor x_2(t))$,
with $x_1(t)$ and $x_2(t)$ functions of $c(0), \ldots, c(t - 1)$; the second adversary puts $g(t + 1)$ in place of the
OR. In both, column 1 at time $t + 1$ is $c(t)$ XOR a function of the earlier driver, so the map from the driver to
column 1 from time 1 on is a bijection that preserves the length of agreeing prefixes, and that structure of the right
half excludes nothing the left half allows. For the single cell's left half the left-admissible sequences are the set
$\Lambda_L$ of [the driver density](../../findings/diagonals/driver-density.md), the left-only constraint of
[driven left runs](../../findings/diagonals/driven-left-runs.md#the-left-only-constraint), and the free column is level
0 of [the right ladder](../../findings/diagonals/right-ladder.md).

**The white tail is left admissible.** The sequence $1, 1, 0, 0, 0, \ldots$ is left admissible for $F_L$: column $-1$
reads 0 at time 0, the start being white, and $0 \oplus (0 \lor u(0)) = 1$ at time 1, so the black times 0 and 1 force
$u(1) = 1$ and $u(2) = 0$, and no black time follows. So against a causal adversary on the right the single cell's own
left half lets the center be white from time 2 on: the left half alone does not imply Problem 1, not even at period
one. At the white times the adversary emits column $-1$ itself, which is not eventually periodic by Jen's theorem.

Every finite left start allows the white tail. If the leftmost black cell of $s$ is at $-n$, the kit's
`Rule30DrivenLeft.ones_fails` makes column $-1$ black at some step $k \le n + 1$ under the all-black driver. With $k$
the first such step, $u = 1^{k+1}$ followed by white is left admissible: column $-1$ at step $j \le k$ reads only
$u(0), \ldots, u(j - 1)$, all black, so the black times $0, \ldots, k$ force $u(1) = \cdots = u(k) = 1$ and
$u(k + 1) = 0$. So the black run that a finite start forces before the white tail has length at most $n + 2$; from the
white start it has length 2. For even $n$ the alternating start, black at $-2, -4, \ldots, -n$, attains $n + 2$: it
agrees on the cells $-1, \ldots, -(n + 1)$ with the kit's alternating half `alt`, which the all-black driver keeps
fixed with column $-1$ white (`alt_fixed`), and differs at $-(n + 2)$, so by exact arrival its column $-1$ is white at
the steps $0, \ldots, n$ and black at step $n + 1$.

**The black tail is not.** If $u$ is black from time $T$ on, admissibility makes column $-1$ white from $T$ on, against
Jen's theorem when the start is finite. So against every right behavior a finite left half forbids the black tail and
allows the white tail: at period one it forbids exactly what Jen's theorem forbids.

**What excludes the white tail is the right half's update.** While the center is white,
$x_1(t + 1) = x_1(t) \lor x_2(t)$: column 1 never falls from 1 to 0, so it is eventually constant, and column $-1$,
equal to it at the white times, is eventually constant, against Jen's theorem for a finite left start. This uses only
the update of cell 1, whatever cell 2 holds ([AdjacentColumns](../../Rule30Open/Columns/AdjacentColumns.md), step 3),
so it holds for a right half of Rule 30 from any start, finite or not, and at level 1 of
[the right ladder](../../findings/diagonals/right-ladder.md). The second adversary above differs from the right half of
Rule 30 exactly in this OR.

**The left half.** Fix a right behavior $G_R$. For every $u$ with $u(0) = 1$ the free column
$G_L(v)(t) = u(t + 1) \oplus (u(t) \lor G_R(u)(t))$ makes $u$ the solution. The adversary can even be a left half of
Rule 30: by the kit's realization theorem, for every right half and every column there is exactly one row with that
right half and that center column, so against the single cell's white right half every $u$ with $u(0) = 1$ is the
solution for $F_L^s$ with exactly one start $s$. For the black tail the alternating half `alt` serves against
every right behavior, since under the all-black driver it keeps column $-1$ white. So the left half's Rule 30 dynamics
exclude nothing without its finite start, the left edge that Jen's theorem uses.

**Beyond period one.** For a word with both colors the check, column $-1$ pinned to $\lnot u(t + 1)$ at the black
phases, leaves the white phases free, and Jen's theorem asks only that column $-1$ not be eventually periodic, which the
white phases can provide. So the two are compatible, and whether some finite left half meets the check of the word
forever is open: for $01$ it is the kit's `Q01`, for $001$, $011$ and $0111$ the kit's `Q001`, `C3w` and `C3`, and for
$0^{P-1}1$ the main branch's `QP`. These statements concern the left half alone, so if they hold, a finite left half
forbids those words against every right behavior (for `Q01` and the right halves of Rule 30 the kit states this as
`Rule30PeriodTwoSideways.Q01_no_leftfinite_alternating`). For no word with both colors is a finite left start known
that meets its check forever, so the white tail is the only eventually periodic center known to need the right half.
None exists in the ranges searched: for $01$ the kit proves in Lean that no start of at most 52 cells meets the check
(`Rule30ZeroBoundaryWidth52`), and no start of at most 63 cells does, by computation
([the shift model](../../findings/period-two/shift-model.md)); for every block of period 3, 5, 6, 7 or 9 with a black
phase no left half of at most $M$ cells meets its checks, with $M$ from 18 to 100 by the block
([every block](../../findings/columns/left-half-every-block.md)).

## What an eventual period asks of the two halves

Suppose the single cell's center column has period $P$ from time $T$.

1. **The left half is a function of the right half.** For $t \ge T$, column $-1$ from time $t$ on is
   $\lnot c(t' + 1)$ at the black times $t'$ and column 1 $\oplus\, c(t' + 1)$ at the white times; column 1 from time
   $t$ on is fixed by the right half at time $t$ and the periodic driver; and column $-1$ from time $t$ on fixes the
   left half at time $t$ (exact arrival). So the left half at time $t$ is a function of the right half at time $t$ and
   of $t \bmod P$: the strobed form $\Psi_w$ of [the reformulations](reformulations.md), for period two the kit's
   `Rule30PeriodTwoSideways.Psi` with `Psi_unique`.
2. **The right half emits a signal that never repeats.** For $T \le t < t'$ with $P$ dividing $t' - t$, the right
   halves at times $t$ and $t'$ are driven by one periodic word, and column 1 at time $t + i$ differs from column 1 at
   time $t' + i$ for infinitely many $i$ with $t + i$ a white time. Otherwise, from some $i_0$ on, the left halves at
   times $t + i_0$ and $t' + i_0$, driven by one sequence, would emit the same column $-1$ (item 1), so they would be
   equal by exact arrival; but their leftmost black cells are at $-(t + i_0)$ and $-(t' + i_0)$. This is the masked
   form for the period $t' - t$.

So an eventual period needs the right half to emit at its white times a signal that never becomes periodic, and a
finite left half to match it cell for cell: a left-permutive half whose column $-1$ carries its whole start, against a
half that reaches the center only through the OR, at the center's white times
([the one-way valve](../../findings/dynamics/one-way-valve.md)). Both signals come from finite data, so no entropy
count separates them, and a complexity argument needs a lower bound on the complexity of every finite driven left
half, a statement of the same kind as the problem ([left-half complexity](left-half-complexity.md)).

## Where it stops

The adversaries show what a proof must use: the left half from its finite start, and the right half's update. Jen's
theorem and the OR latch of column 1 are those two, and they settle period one
([AdjacentColumns](../../Rule30Open/Columns/AdjacentColumns.md)). For a word with both colors the match of the last
section has two sides:

- **the right half's channel**, what column 1 can emit at the white times. Where it provably locks, column 1 becoming
  periodic at the white times, the masked form excludes the word: this is how the kit's absorbing words and the finite
  game of this repository exclude blocks, and how the traps reduce others to entry
  ([the coverage](../../findings/columns/coverage.md)). For the other words it is open: the kit's `Absorption`
  statements, which keep the right half (`Rule30Ether`), the kit's `CQ01` for period two, which keeps both, and
  [`Q01Right(W)`](../../Rule30Open/PeriodTwo/ChannelLanguage.md), the check against the language of the right half's
  windows of $W$ columns;
- **the left half's check**, that no finite left half meets the pins at the black phases forever: the kit's `Q01`,
  `Q001`, `C3w`, `C3` and `QP`, and with the latch of cell 1 added, [LeftLatch](../../Rule30Open/Columns/LeftLatch.md),
  which keeps from the right half exactly the update of cell 1, as level 1 of the right ladder does. A proof of the
  check for a word proves `LeftLatch` for it, which is open for every block but the black one, so the check is open
  for every word with both colors.

The kit's `Rule30Coupled` describes this split: its word-by-word reductions keep one half of the coupled system. The
searches settle bounded cases only, finite left halves failing the checks about as late as fair coins would let them
([every block](../../findings/columns/left-half-every-block.md)). The compositional view adds no handle: its two
necessary ingredients settle period one, and beyond it the route returns to these statements.

## In the kit and the repository

- **Exact arrival** is the kit's `Rule30DrivenLeft.light_cone` and `permutive`. The kit's main branch (at commit
  368d1c7) adds `init_prefix_eq_iff_col_neg1_prefix_eq`: the first $k$ cells of a start and the first $k$ values of
  its column $-1$ determine each other.
- **Jen's theorem for driven left halves** is the kit's, in Lean, by Jen's argument, which spreads the period left
  until it meets the edge: `col_neg_one_not_periodic` and `no_periodic_column` (every column $q < 0$) in
  [`Rule30DrivenLeft`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30DrivenLeft.lean)
  for a nonzero finite start, and on the main branch `no_periodic_column_of_all_white` and
  `no_periodic_column_of_bounded` for every finite start with a black cell in the start or the driver, the condition
  above. The proof here, through exact arrival, is the reconstruction behind the kit's window form
  `Rule30MaskedJen.window_jen`, run inside the half.
- **The masked form** and item 2 are the kit's masked Jen: `Rule30MaskedJen.masked_jen` for the single cell,
  `Rule30FiniteMaskedJen.masked_jen` for every row with a leftmost black cell, and `Rule30MaskedJen.periodic_window`,
  which puts a white time at which column 1 breaks the period $P$ in every interval $[n, 2n)$ with $n \ge T + P$. The
  main branch's `Rule30DrivenLeft.not_eventuallyPeriodic_free_phase_of_bounded` is the same inside the driven left half
  for one free phase of column $-1$.
- **The left adversary** is the kit's: `column_realizable_unique` in
  [`Rule30Realization`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Realization.lean),
  whose docstring draws the same conclusion (a proof that a column is aperiodic must use the left half, for the single
  cell its left edge), `seed_perturbation`, and `Realization.problem1_iff_realization` among the equivalent forms. On
  the main branch `Rule30CoupledEmptyRight.lc_infinite_of_eventually_all_black` says that the left start realizing an
  eventually black column is infinite, whatever the right half. The kit's `Rule30Realization.barrier` (Rules 90, 150
  and 210 meet left permutivity, the left edge and Jen's theorem, and their center columns are eventually constant)
  draws the matching conclusion for the rule, that a proof must use Rule 30's OR;
  [Rule 210](../../Rule30Open/Analogs/Rule210.md) shows the same for the check of period two.
- **The right adversary**, its description by left admissibility, the triangular adversary, and the bound $n + 2$ on
  the forced black run, attained for even $n$, are proved here on paper; neither the pinned kit nor its main branch
  puts an arbitrary behavior in place of the right half. That $1, 1, 0, 0, 0, \ldots$ lies in $\Lambda_L$ is noted in
  [the driver density](../../findings/diagonals/driver-density.md), and that level 0 of
  [the right ladder](../../findings/diagonals/right-ladder.md) allows an all-white center after time 1 is noted there.
- **Item 1** is the strobed form of [the reformulations](reformulations.md), and the decoupling of the halves under an
  eventual period is the last item of [left-half complexity](left-half-complexity.md).
