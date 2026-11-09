---
title: A white rate below 1 at the first rung of the right ladder needs a linear cost bound for one explicit orbit, the half line beside a cell held white started from one black cell, which a positive density of black cells in its column -2 would give, as a bound on the relaxed driver game needs a positive density beside a cell held black
category: diagonals
problems: [2]
status: negative
kind: dead-end
---

# A white rate below 1 at the first rung of the right ladder needs a linear cost bound for one explicit orbit, the half line beside a cell held white started from one black cell, which a positive density of black cells in its column -2 would give, as a bound on the relaxed driver game needs a positive density beside a cell held black

**Question.** At level 1 of [the right ladder](../../findings/diagonals/right-ladder.md) the left half (cells $-1, -2,
\dots$) runs exactly from white, driven by the center $c$, cell 1 runs exactly, $x_1(t + 1) = c(t) \oplus (x_1(t) \lor
f(t))$, and cell 2 is a free word $f$. Let $M_0(1, T)$ be the most white cells among $c(1), \dots, c(T)$ over all free
words. The statement $S_W(1)$, that $M_0(1, T) \le \rho T + C$ for some $\rho < 1$, would give the single cell's center
column a positive lower density of black cells. Can it be proved from the structure of the left half?

**Notation.** $y(t) = x_{-1}(t)$. A *kick* is a time $t$ with $c(t) = 1$ and $y(t) = 0$, that is, with $c(t) = c(t + 1)
= 1$; a *fall* is a pair $(t - 1, t)$ with $y(t - 1) = 1$ and $y(t) = 0$. The *zero-boundary half line* is Rule 30 on
the cells $\le -1$ with cell 0 held white (the kit's `Rule30ZeroBoundary.zrow`). The left half sees the center only
through its kicks, and between kicks it runs as the zero-boundary half line (the kit's
`Rule30DrivenLeft.cell_eq_L_effective`, `Rule30ZeroBoundary.left_half_is_zbl`).

## Outcome

- **Falls and kicks pay for black cells** (proved). In every play, at every level $k \ge 1$ of the ladder and for the single cell itself, the black cells $B$, kicks $E$
  and falls $K$ up to time $T$ satisfy $2B \ge K + E$, so the white cells number at most $T + 1 - (K + E)/2$. At level
  0, where cell 1 is free, it fails: a free word can keep the center white from time 2 on while column $-1$ keeps
  falling. *Proof.* At a fall $(t - 1, t)$ with $c(t - 1) = c(t) = 0$, the center rule gives
  $x_1(t - 1) = 1$, cell 1 stays black after a white center, and then $c(t + 1) = y(t) \oplus (c(t) \lor x_1(t)) = 1$; so
  a black cell lies among $t - 1, t, t + 1$. Assign each fall to the first such black cell: a kick receives at most one fall and any other black cell at most
  two. The kick $c(0)$ receives no fall, and the black cell $c(1)$, which is not a kick since $y(1) = 1$, receives at
  most the fall $(1, 2)$. This leaves room for a last fall $(T - 1, T)$ whose black cell is $c(T + 1)$. $\square$ This is the white side of the bound $B \le (E + T + 1)/2$ of
  [the relaxed game](relaxed-density-game.md).
- **Without kicks the left half is one orbit** (proved). In a play with no kick after time 0, the left half at every
  time $t \ge 1$ is the zero-boundary half line started from the single black cell at $-1$, the same for every such
  play. The plays are then the runs of a four-state automaton on the states $(c(t), x_1(t))$ reading its column $-1$,
  $y$, and the most white cells over them is $T - \mathrm{cost}(y_{1..T})$, where $\mathrm{cost}$ counts the fewest black
  states of a run.
- **So $S_W(1)$ needs a positive-density statement for one sequence** (proved). If $M_0(1, T) \le \rho T + C$ for every $T$,
  then $\mathrm{cost}(y_{1..T}) \ge (1 - \rho)T - C$ for the column $y$ of that one orbit. Under the zero-boundary rule
  $y(t + 1) = y(t) \oplus x_{-2}(t)$, so the falls of $y$ are half of the black cells of column $-2$, and with the bound
  above a positive density of black cells in column $-2$ of that orbit implies this cost bound. Conversely, if every play has $K + aE \ge vT - C'$ for some $v > 0$ and some $a \ge 1$ (kicks remove falls at an
  amortized rate of at most $a$), then $S_W(1)$ holds with $\rho = 1 - v/(a + 1)$: kicks are black cells, and either they are many or the falls are.
- **Numbers** (computed by code that is not in this repository: an exact dynamic program over the reachable states,
  checked against every free word for $T \le 14$ and against the repository's right ladder at $T = 150$). $M_0(1, T)$ is
  157, 173, 189, 206, 221 and 237 at $T = 200, 220, \dots, 300$. In the kick-free sub-game the most white cells are
  750,504 among $10^6$ (0.7505), and column $-1$ of the half line beside the held white cell has 0.2501 falls per step to
  $10^6$, as fair coins have 0.25. The fewest kicks after time 0 that a play can get away with are 0, 2 and 6 at levels
  1, 2 and 3 to $T = 150$: from level 3 on, the word $0010000$ in column $-1$ forces a kick from every state of cells 1 to
  3, so the reduction to one sequence is a level-1 phenomenon, and $S_W(k)$ for $k \ge 3$ is a statement about a family
  of kicked orbits.

## What it means

The two density routes of the driver game both stop at a statement about one explicit orbit. A bound below 1 on the
relaxed game G, which would give a black rate below 1, needs a positive density of black cells in column $-1$ of the
half line beside a cell held black, started white. The black rate itself needs a positive density of white cells in the
greedy driver of $\Lambda_L$ ([the relaxed game](relaxed-density-game.md)). A white rate below 1 at the first rung of
the right ladder needs $\mathrm{cost}(y_{1..T}) \ge (1 - \rho)T - C$ for column $-1$ of the half line beside a cell held
white, started from one black cell. A positive density of black cells in its column $-2$ would give this bound, but the
bound does not need that density: a fall followed by $0\,0$ forces a black center at the last 1, and under $y = 1$ the
state $(0, 1)$ is absorbing, so on $y = (1^m 0 0)^\infty$ the cost is $\lceil m/2 \rceil$ per block of $m + 2$ letters
while the falls are one per block (a paper count). Both are explicit deterministic orbits of Rule 30 on a half line with
a frozen boundary cell; for almost every start the columns are fair coins (a random start gives columns of independent
fair bits: beside a cell held white by the kit's `Rule30ZeroBoundary.zrow_light_cone` and `pivot`, beside a cell held
black by `Rule30DrivenLeft.light_cone` and `permutive`), and for these starts nothing in the kit or this repository
proves a positive density, beyond logarithmic counts (`Rule30ZeroBoundary.jen_clock` beside a cell held white;
`Rule30DrivenLeft.ones_fails` and L6, L7 of [the relaxed game](relaxed-density-game.md) beside a cell held black). These
are two explicit orbits on which a statement of the kind Problem 2 asks for is needed.
