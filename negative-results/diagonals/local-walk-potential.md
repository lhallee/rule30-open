---
title: No potential that reads the white run ahead of the front walk and a window of at most three cells of the pair that holds the phase or ends just before it certifies the walk's slope 5/2 at every period; at every period from 5 to 10, states with equal features are joined by edges or cycles of mean above 5/2, and the slope such a potential can certify grows with the period
category: diagonals
problems: [2]
status: negative
kind: barrier
evidence: [computations/walk_eigen.py]
---

# No potential that reads the white run ahead of the front walk and a window of at most three cells of the pair that holds the phase or ends just before it certifies the walk's slope 5/2 at every period; at every period from 5 to 10, states with equal features are joined by edges or cycles of mean above 5/2, and the slope such a potential can certify grows with the period

**Question.** On every pair word of period $P \le 16$ the least front walk has largest cycle mean at most $5/2$, and
its excess over slope $5/2$ is between $4P$ and $5.6P$ for $P$ from 10 to 16 ([walk eigenvalue](../../findings/diagonals/walk-eigenvalue.md),
which defines the states $(A, B, f)$, the step and its cost). A proof for every $P$ would follow from one *local
potential*: a function $\Phi$ of a bounded description of the state, the same at every period, with
$$\mathrm{cost}(s) \le \tfrac{5}{2} + \Phi(s) - \Phi(s')$$
on every edge $s \to s'$ that stays in period $P$. Summed along a regime, it gives
$w_i - w_\ell \le \frac{5}{2}(i - \ell) + \max \Phi - \min \Phi$, and with $\Phi = k\,d + \mathrm{table}$ the range is
at most $k P$ plus a constant per doubling. The candidate was
$$\Phi(s) = k \cdot d(s) + \mathrm{table}(\text{the } h \le 3 \text{ cells of } A \text{ and } B \text{ at the times } f + o, \dots, f + o + h - 1) + z\,[A = 0] + y\,[B = 0],$$
with $d(s)$ the white run of $A$ ahead of the phase $f$ and an offset $o \in \{-h, \dots, 0\}$.

**What was done.** `walk_eigen --features` builds the graph of every state of period $P$ and its quotient by the
features (white run, window, the two white flags): one node per feature value, one edge per distinct (features of $s$,
features of $s'$, cost). Any function of the features with the inequality on every edge exists exactly when the
quotient has no cycle of mean above $5/2$ (Karp's theorem gives the largest mean), and the linear program of
`fit_potential` asks for the form $k d + \mathrm{table}$ with one $(k, \mathrm{table}, z, y)$. It also tries features
that look ahead instead: the costs of the next $k$ steps of the walk.

## The outcome

Largest cycle mean of the quotient by $d$, the window of $h$ cells at offset $o$, and the two white flags, against
$\mu_P$ of the graph itself:

| $P$ | $\mu_P$ | $h = 0$ | $h = 1, o = -1$ | $h = 2, o = -1$ | $h = 3, o = 0$ | $h = 3, o = -1$ | $h = 3, o = -2$ | $h = 3, o = -3$ |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 4 | 7/3 | 7/2 | 11/4 | 8/3 | 3 | 8/3 | 8/3 | 7/3 |
| 5 | 15/8 | 9/2 | 7/2 | 10/3 | 11/3 | 10/3 | 10/3 | 3 |
| 6 | 5/2 | 11/2 | 17/4 | 4 | 5 | 4 | 4 | 15/4 |
| 7 | 5/2 | 13/2 | 5 | 19/4 | 6 | 19/4 | 14/3 | 9/2 |
| 8 | 7/3 | 15/2 | 23/4 | 11/2 | 7 | 11/2 | 16/3 | 21/4 |
| 9 | 1006/493 | | 13/2 | | 8 | 25/4 | 6 | 6 |
| 10 | 89/41 | | 29/4 | | 9 | 7 | 27/4 | 27/4 |

The linear program is infeasible at $5/2$ for every width and offset at every $P$ from 4 to 10 (widths 0 to 3 for
$P \le 8$, widths 1 and 3 at $P = 9$ and 10) but one
($h = 3$, $o = -3$ at $P = 4$, where the window and the run see the whole word). The largest mean grows by $2/3$ to 1
per unit of $P$ at every width and offset: what a potential of these features can certify is a slope that grows with the
period, not $5/2$.

**Two families, checkable on paper.** Write $e_r$ for the word with one black cell, at time $r$.

1. *Windows ahead of the phase.* From $(e_0, e_{P-1}, 2)$ the walk crosses $d = P - 2$ white cells and lands at phase 1
   on the pair $(e_{P-1}, C)$, where $C(0) = \lnot e_0(P - 1) = 1$ and then $C(t + 1) = e_0(t) \oplus C(t)$ gives
   $C = e_0$. The step costs $P - 1$, both states have $d = P - 2$, and every cell of $A$ and of $B$ at the times
   $f, \dots, f + P - 4$ is white in both. So a potential that reads $d$ and at most $P - 3$ cells from the phase on
   takes the same value at both ends of an edge of cost $P - 1$, and needs $\gamma \ge P - 1$. (The step after it costs
   $P - 1$ again: this is a real path of excess about $2P$, not an artifact of the quotient.)
2. *Windows that start one cell behind the phase.* For even $P$, from $(e_0, e_{P/2}, P/2 + 1)$ the walk crosses
   $d = P/2 - 1$ white cells and lands at phase 1 on $(e_{P/2}, C)$ with $C$ black at 0 and at $P/2 + 1, \dots, P - 1$.
   Both states have $d = P/2 - 1$; at the times $f - 1, \dots, f + h - 2$ the first has $A$ white and $B$ black then
   white, and so has the second, for $h \le P/2$. The step costs $P/2$. At $o = -1$ and $h = 3$ these are the
   costliest edges between equal features that `walk_eigen --features` finds for even $P$ from 6 to 10; at odd $P$ the
   costliest cost $\lfloor P/2 \rfloor$.

**Looking ahead does not help either.** Features made of the costs of the next $k$ steps give quotients of largest
mean $8/3$, $7/3$, $7/3$ at $P = 4$ and $k = 2, 3, 4$, but $10/3$, $17/6$, $8/3$ at $P = 5$, and $16/3$, $13/3$, 4 at
$P = 8$: each further step of lookahead lowers the mean, and the mean at fixed $k$ rises with $P$.

## What it means

The features above see a bounded part of the word, and the costly steps are the ones where the walk crosses a long white
run of $A$ and lands where $B$ has its own long white run: whether that happens depends on where the black cells of $B$
sit relative to those of $A$ across about $P/2$ cells. Among the features tested here, a window that starts at the phase
or one cell behind it and sees fewer than about $P/2$ cells has edges of cost about $P/2$ or $P$ between states it
cannot tell apart (the two families), so a potential of this kind that proves $\mu_P \le 5/2$ for every $P$ must read a
part of the word that grows with the period. The exact excess $E$ of the finding reads the whole pair word, period by
period. This is the walk's version of the stop in [white-run potential](white-run-potential.md) (a certificate that
knows only white runs needs slope $7/3$) and in [seed finite certificate](seed-finite-certificate.md): a local
description of the settled words does not bound the cost of crossing them. The route stops at the potential: the cycle
means and excesses are computed and well behaved for $P \le 16$, and there is no local potential to carry them to every
$P$, so no Lean statement of a slope-$5/2$ walk follows.

## Reproduce

```bash
python -m computations.walk_eigen --features 4-8 --widths 0,1,2,3   # the table and the families, about 15 s
python -m computations.walk_eigen --features 9-10 --widths 1,3 --lookahead 1  # P = 9 and 10, about 2.5 min
```
