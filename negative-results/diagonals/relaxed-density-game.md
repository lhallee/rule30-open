---
title: The relaxed driver game G has value about 0.63 T to T = 180, its lemmas reduce a black density below 1 to a charging property, and every such bound contains a positive density for one explicit orbit, Rule 30 beside a cell held black
category: diagonals
problems: [2]
status: negative
kind: dead-end
evidence: [computations/relaxed_game.py, computations/relaxed_game.c, tests/test_relaxed_game.py]
---

# The relaxed driver game G has value about 0.63 T to T = 180, its lemmas reduce a black density below 1 to a charging property, and every such bound contains a positive density for one explicit orbit, Rule 30 beside a cell held black

**Question.** The conjecture $S_B$ of [driver density](../../findings/diagonals/driver-density.md) bounds the black
cells of every center column that the single cell's left half allows by $\rho T + C$ with $\rho < 1$. Can it be
proved through a simpler game in which the controller harvests black pairs, and if not, where does the proof stop?

**The game.** The left half $x$ (cells $-1, -2, \dots$) starts white. At each time $t$ the controller picks
$e(t) \in \{0, 1\}$, with $e(t) = 1$ allowed only when $x_{-1}(t) = 0$, and the left half takes one Rule 30 step with
cell 0 equal to $e(t)$. The payoff of a play of $T$ moves is $\#\{t < T : e(t) = 1\}$, and $E(T)$ is its largest value.
Conjecture $S_G$: $E(T) \le \rho T + C$ for some $\rho < 1$.

**The reduction.** For a driver $c$ of $\Lambda_L$ put $e(t) = c(t) \land c(t + 1)$. The left half sees $c(t)$ only
through $x_{-1}(t) \lor c(t)$, and $x_{-1} \lor c = x_{-1} \lor e$ in both cases ($c(t) = 0$ gives $e(t) = 0$;
$c(t) = 1$ gives $c(t + 1) = \lnot x_{-1}(t)$, so $e(t) = \lnot x_{-1}(t)$ and both ORs are 1). So $e$ is a play of G
that drives the same left half, and $e(t) = 1$ exactly at the black pairs of $c$. A black run of length $L$ holds
$L - 1$ black pairs and the runs are separated by white cells, so the black cells $B$ among $c(0), \dots, c(T - 1)$
satisfy $B \le (E + T + 1)/2$. Hence $S_G$ implies $S_B$, and gives the single cell's center column white cells of
lower density at least $(1 - \rho)/2$. Proposition 3(e) of [the first moment](../../findings/diagonals/driver-first-moment.md)
is the converse direction over $\Lambda_L$ alone: $S_B$ holds exactly when the black pairs of every driver of
$\Lambda_L$ number at most $\rho' T + C'$; G lets the controller choose them freely.

## Outcome

**Exact values** (`relaxed_game values`; a dynamic program over the reachable left halves in C, each state cut at time
$t$ to its cells $-1, \dots, -(T - t)$, the only cells that later moves can read, which keeps every value exact):

| $T$ | 20 | 40 | 60 | 80 | 100 | 120 | 140 | 160 | 180 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $E(T)$ | 10 | 24 | 38 | 49 | 62 | 76 | 89 | 102 | 114 |
| $E(T)/T$ | 0.500 | 0.600 | 0.633 | 0.613 | 0.620 | 0.633 | 0.636 | 0.638 | 0.633 |

A beam that keeps the 20,000 best states equals $E(T)$ at every even $T \le 180$; with 60,000 states it gives the lower
bound $E(3{,}000) \ge 1{,}994$ (0.6647). The greedy play, $e = 1$ whenever allowed, has payoff 9,959 at $T = 20{,}000$
(0.4980), so the best plays are greedy between a few skips.

**Lemmas** (proved on paper, each checked exhaustively on all rows or words of the width stated, `relaxed_game
lemmas`). Write $m(x)$ for the length of the longest prefix of cells $-1, -2, \dots$ that reads $0, 1, 0, 1, \dots$
(phase A).

- **L1 (runs).** From a left half $x$, $e = 1$ can be played $k$ times in a row exactly when $m(x) \ge k$, and $m$
  drops by exactly one at each such step. (All rows of width 16.)
- **L2, L3 (erosion and the right end).** An alternating stretch loses its left end cell at every step, whatever lies
  beyond, and its rightmost black cell advances by 0, 2 or 4 cells, by 4 exactly over $0\,0\,0\,1$. (All 262,208
  stretches in words of 18 cells.)
- **L4 (moving frame).** Index cell $-k$ at time $t$ by $n = k + t$ and put
  $P_n(t) = x_{-k}(t) \oplus [k \text{ even}]$. Then $P_n(t + 1) = P_n(t) \oplus [\text{cells } n - 1 \text{ and }
  n - 2 \text{ are white at time } t]$ for $n \ge t + 2$: in the frame moving right at speed one, a cell changes only
  behind two white cells.
- **L5 (shielding).** While an alternating stretch of length at least 3 lies between a region and cell 0, the region
  evolves independently of the controller. (By L4, no cell of a stretch is preceded by two white cells.)
- **L6, L7 (backward trapezoid and slope 3/5).** If a row alternates on the cells $p, \dots, q$ with $q - p \ge 4$, it
  alternated on $p - 1, \dots, q - 4$ one step earlier, so a long prefix was born long before, far from cell 0, inside
  the light cone, and $m(x(a)) \le (3a + 9)/5$ in every play: the kit's black-run slope 3/5 (its main branch) in the
  language of G. (All words of 16 cells; every state reachable at $t \le 100$, where the largest prefix
  is 12 at $t = 60$ and 16 at $t = 100$.)
- **L8 (accounting).** For every play,
  $$\#\{t < T : e(t) = 0\} = \#\{t \le T - 2 : x_{-2}(t) = 0\} + 2W + [x_{-1}(T - 1) = 0 = e(T - 1)],$$
  with $W$ the number of times $t \le T - 2$ with $x_{-1}(t) = e(t) = 0$ and $x_{-2}(t) = 1$. *Proof.* From
  $x_{-1}(t + 1) = x_{-2}(t) \oplus (x_{-1}(t) \lor e(t))$, cell $-1$ at $t + 1$ is $\lnot x_{-2}(t)$ except after a
  skip ($x_{-1}(t) = e(t) = 0$), where it is $x_{-2}(t)$; the zeros of $e$ are the forced ones ($x_{-1} = 1$) and the
  skips; count. $\square$ So $S_G$ says that in every play cell $-2$ is white a positive fraction of the time, up to
  skips that only lower the payoff.
- **L9 (covering).** If in a play every maximal run of ones of length $k \ge K$ has at least $\varepsilon k - C$ zeros
  in the window of $\lambda k$ moves on each side of it, then the play has at most $K'(Z + 1)$ ones, where $Z$ counts
  its zeros and $K' = (6\lambda + 4)(1 + C)/\varepsilon + K - 1$. So if every play has this two-sided charging property,
  $S_G$ holds with $\rho = K'/(K' + 1)$. *Proof.* Select long runs in decreasing order of length while their windows
  are disjoint; the selected runs are paid for by their zeros, and every other long run lies in a window three times as
  long around a selected one (a Vitali covering). $\square$ On the best play found for $T = 3{,}000$ the smallest
  charging ratio over runs of length at least 4 is 0.625 with $\lambda = 2$: one play, not a proof.

## Where it stops

- **(B1) Every bound contains an explicit orbit.** Under the greedy play $x_{-1}(t) \lor e(t) = 1$ at every step, so
  the left half is Rule 30 on the cells $\le -1$ beside a cell 0 held black, from white, and the payoff is the number of
  white cells of its column $-1$. So $S_G$ with constant $\rho$ implies that column $-1$ of this one explicit orbit has
  black cells of lower density at least $1 - \rho$ (`relaxed_game greedy`: 10,041 black among its first 20,000 cells,
  19,997 among 40,000, 0.4999, and no period up to 5,000 in the last 20,000). The same holds for $S_B$ and the greedy
  driver of $\Lambda_L$, black whenever the next value is free: 2,014 black cells among $c(0), \dots, c(3{,}000)$
  (0.6711) and 13,346 among $c(0), \dots, c(20{,}000)$ (0.6673). Nothing in the kit or this repository proves a
  positive density of a color in a column of any explicit Rule 30 orbit; the kit's density results hold for almost
  every row. For this orbit column $-1$ is not eventually constant (Jen's theorem for driven left halves, the kit's
  `Rule30DrivenLeft`), and each color occurs at least about $\log_{8/5} T$ times by L7.
- **(B2) The kinematics allow density 1.** A schedule of harvests whose far ends grow by the factor $8/5$, each run
  born inside the light cone and brought to cell $-1$ at the front speed of L3, satisfies the conclusions of L1 to L7
  and has a density of ones $1 - O(\log T / T)$. So a proof must use what the dynamics do behind a stretch (which L5
  says nothing about), not only how fast things move.
- **(B3) Charging over windows proportional to the run weakens with time.** The fewest zeros in the $2k$ moves before a
  prefix of length $k$, from a state reachable at time $s$ (`relaxed_game costs`): for $k = 14$, 14, 10 and 5 at
  $s = 60$, 100 and 120; for $k = 10$, 8, 5 and 3. Read heuristically, a charging argument has to reach arbitrarily far
  back, as the windows of [driver density](../../findings/diagonals/driver-density.md) already suggest; the potential
  route stops at the same point ([driver-density potentials](driver-density-potential.md)).

**What it means.** G is a clean relaxation with exact laws (L1 to L9), and its best plays sit at about 0.665 per move,
well below 1; but no argument that bounds every play can avoid bounding the greedy play, which is one deterministic
orbit of Rule 30 on a half line. So a proof of $S_G$ or $S_B$ is at least a proof that one explicit orbit has a column
with a positive density of a color, a statement of the kind Problem 2 asks for.

## Reproduce

```bash
python -m computations.relaxed_game values                                  # E(t) to t = 150: about 15 s
python -m computations.relaxed_game values --steps 180                      # to t = 180: about 4 min, 2 GB
python -m computations.relaxed_game beam --steps 3000 --width 60000         # the lower bound at 3,000: about 6 min
python -m computations.relaxed_game beam --steps 180 --width 20000 --check  # the beam against E(t) to 180: about 1 min
python -m computations.relaxed_game greedy                                  # B1's orbit to 40,000: a few seconds
python -m computations.relaxed_game lemmas                                  # L1 to L7: a few seconds
python -m computations.relaxed_game costs --times 100 --width 44 --cells 64 # B3 at s = 100: about 2 min
python -m computations.relaxed_game costs --times 120 --width 32 --cells 48 # B3 at s = 120: about 4 min, 2 GB
```

`tests/test_relaxed_game.py` checks the dynamic program against every play enumerated with the rule applied cell by
cell, the beam against the exact values, the accounting identity L8 on random plays against direct simulation, the
greedy play against the half line beside a held black cell run with the full rule, and the lemmas on small widths.
