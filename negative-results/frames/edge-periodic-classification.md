---
title: The classification of the right-edge map's periodic points for every period stops at reachability; the period-4 mechanism holds only for period 4, a column of least period 2^j is not always complemented by half its period, and no potential independent of the right edge can work since the full column graph has 99 and 13,875 live states at periods 4 and 8 against the 5 reachable from the edge
category: frames
problems: [3]
status: negative
kind: dead-end
evidence: [computations/edge_periodic_full.py, tests/test_edge_periodic_full.py, computations/edge_periodic_points.py, tests/test_edge_periodic_points.py]
---

# The classification of the right-edge map's periodic points for every period stops at reachability; the period-4 mechanism holds only for period 4, a column of least period 2^j is not always complemented by half its period, and no potential independent of the right edge can work since the full column graph has 99 and 13,875 live states at periods 4 and 8 against the 5 reachable from the edge

**Question.** [Edge periodic points](../../findings/frames/edge-periodic-points.md) shows that, apart from 0, the only
2-adic integers $y$ with $\Phi^L(y) = y$, $\Phi(y) = y \oplus (2y \lor 4y)$, are $2^m(\pm 1/3)$ when $128 \nmid L$
(exact computation of the column graph $G_L$; period 4 in Lean, [EdgePeriodFour](../../Rule30Open/Frames/EdgePeriodFour.md)),
and conjectures it for every $L$. A proof for every $L = 2^k$ would say that no row white to the right of some cell,
other than the white row and the rain rows, ever comes back moved at the speed of light. This entry records three
attempts at that proof and where each stops.

Notation: for $L = 2^k$, $W_e$ is the cyclic time word of diagonal $e$ (bit $e$ of $\Phi^t(y)$, $t \in \mathbb{Z}/L$);
the walk continues from $(W_{e-2}, W_{e-1})$ exactly when $|W_{e-1} \lor W_{e-2}|$ is even, with two complementary
choices of $W_e$ solving $\Delta W_e = W_{e-1} \lor W_{e-2}$. The start is $W_{-1} = 0$, $W_0 = 1^L$.

## What holds (paper)

1. **The problem is a reachability problem.** In the *full* graph on all pairs of $L$-bit words, call a state live when
   it has an infinite forward walk. The classification at $L$ is equivalent to: the only live states reachable from the
   start are the start and the four rain states. (An infinite walk from the start exists exactly when a reachable state
   is live, by König's lemma in a finite graph; two walks that differ give two periodic points.) A live state is a pair
   of $L$-periodic adjacent diagonals from which a light-like periodic half-row continues to the left without end.
2. **The first doubling column is antiperiodic.** If $W_0, \dots, W_{j-1}$ have period $H = L/2$ and $W_j$ does not,
   then $D(t) = W_j(t + H) \oplus W_j(t)$ has $\Delta D = g(t + H) \oplus g(t) = 0$, $g = W_{j-1} \lor W_{j-2}$, so $D$ is
   constant and equal to 1: $W_j(t + H) = \overline{W_j(t)}$, and $|W_j| = H$ exactly. This is the T-function form of
   the kit's `Rule30RightPeriods.antiperiod`, valid for every seed.
3. **The period-4 mechanism.** In $G_4$ every non-rain branch passes through a state $(u, u)$ with $u$ alternating, and
   it dies at the next step because the input after it has weight 3 ([EdgePeriodFour](../../Rule30Open/Frames/EdgePeriodFour.md)).
   For general $L$ the same state gives the successor word $w$ with $w(t + 1) = w(t) \oplus u(t)$, which has period 4
   ($w = a, \bar a, \bar a, a$ on each block of four steps when $u = 1010\dots$), and the next input $w \lor u$ has
   exactly 3 black cells in each block of four: weight $3L/4$.

## Where each route stops

**Route 1: induct on the period through the half-period structure.** The hoped-for lemma was: a column of least period
exactly $2^j$ has its two half periods complementary, so its weight is $2^{j-1}$, and the parities of the inputs are
then computable by induction on $k$. Item 2 proves this for the column where the cycle first doubles. It fails for later
columns: the reachable column $W = 10101000$ of $G_8$ has least period 8, weight 3, and $W(4) = W(0) = 1$ (reading the word from
$t = 0$), so $W(t + 4) \ne \overline{W(t)}$. $G_8$ and $G_{16}$ each have 16 reachable columns of least period above 1 that are not antiperiodic, and $G_{32}$
has 2,000 (`non_antiperiodic_columns`; $G_4$ has none, which is why the period-4 proof closes). The step where it stops:
above the first doubling column, $D_e = W_e(\cdot + H) \oplus W_e$ obeys $\Delta D_e = g_e(\cdot + H) \oplus g_e$, and
because $g_e$ is an or, $g_e(\cdot + H) \oplus g_e$ is not a function of $D_{e-1}, D_{e-2}$ alone; the differences do
not form a closed system. This is also why the planner's third route, through $z = y \oplus \Phi^{H}(y)$, has no
equation in $z$ alone: the bits of $z$ are the $D_e(0)$, the lowest one is the first doubling level (item 2), and
nothing above it is forced.

**Route 2: copy the period-4 death.** The dead state $(u, u)$ dies at the next step only when $3L/4$ is odd, that is
only for $L = 4$ (`dead_square_weight`: weights 3, 6, 12, 24 for $L = 4, 8, 16, 32$). For $L \ge 8$ the branch lives on,
which is where the escape depths $T_3 = 3$, $T_5 = 14$, $T_6 = 103$ of the finding come from. A proof for every $k$
needs the death of an unbounded and growing family of transients, not of one state.

**Route 3: a potential.** A quantity that strictly decreases, or decreases in a well-founded order, along every walk of
$G_L$ would kill every infinite walk, including those from states that the start never reaches. But the full graph has
many: 9, 99 and 13,875 live states for $L = 2, 4, 8$, against 5 live states reachable from the start in each
(`full_live_count`). So a potential, if one exists, must be defined only on the reachable states, that is it must
carry the information of the right edge (the white half to the right). No such quantity was found; the least period
of the pair $(W_{e-1}, W_e)$ never decreases along a walk, but it is the cycle length modulo $2^{e+1}$ and is bounded by
$L$, so it cannot separate rain from the other walks.

## What it means

Every argument that would classify the periodic points for all periods has to use the start of the walk, the white
half to the right of the edge, and not only the local rule, because the local rule alone admits many light-like
periodic half-rows of every period $L \ge 4$ (item 1 and the counts). Within that, the period-4 proof uses a single dead
state, and its weight $3L/4$ shows why it does not generalize. The half-period structure holds at the first doubling
column and fails above it. That leaves a precise target: describe the reachable set of $G_{2^k}$ well enough to show
it meets the live set of the full graph only in rain. Its size grows fast (7, 11, 35, 67, 2,115, 171,779 for $k = 1,
\dots, 6$), so the description has to be structural. The classification for every $k$ stays a conjecture, proved for
$k \le 6$ by exact computation.

## Reproduce

```
python -m computations.edge_periodic_full       # full live counts for L <= 8, the weights 3L/4, the columns: under a second
python -m pytest tests/test_edge_periodic_full.py
```
