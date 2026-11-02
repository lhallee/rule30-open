---
title: Over every pair word of period P at most 16, the front walk's largest cycle mean is at most 5/2, reached only by pairs of least period 6 and 7; from the start of a regime after a doubling it exceeds slope 5/2 by at most 21.5, its largest excess anywhere is at most 88.5, between 4P and 5.6P for P from 10 to 16, and the single cell's walk to depth 87,866 is a path of these graphs
category: diagonals
problems: [2]
status: computed
formalization: wanted
evidence: [computations/walk_eigen.py]
---

# Over every pair word of period P at most 16, the front walk's largest cycle mean is at most 5/2, reached only by pairs of least period 6 and 7; from the start of a regime after a doubling it exceeds slope 5/2 by at most 21.5, its largest excess anywhere is at most 88.5, between 4P and 5.6P for P from 10 to 16, and the single cell's walk to depth 87,866 is a path of these graphs

[FrontWalker](../../Rule30Open/Diagonals/FrontWalker.md) proves that a front walk $w$ of slope $\gamma$ (with
$w_{j+1} \le \gamma j + \delta$) bounds when the left diagonals settle, and with it the black runs of the center
column, at slope $3(\gamma - 1)/(5\gamma - 1)$. The least walk of the single cell advances about 2.01 times per depth
to depth 200,000, but that is a measurement on one pattern. This entry asks for the worst case: over every pair of
words of a period $P$ and every phase, how fast can the walk go?

## The walk on pair words (paper)

Between two white diagonals the aligned settled words $A = D_i$ and $B = D_{i+1}$ have a common period $P$ (bit $t$ is
the cell at time $t \bmod P$), and the next word is $C = D_{i+2}$ with $F(A, B) = (B, C)$, the bijection of
[settled words](settled-words.md). The least walk is then a map on *states* $(A, B, f)$ with $f = w_i \bmod P$:

- $A$ not white: let $d$ be the white run of $A$ ahead of $f$ (the least $d \ge 0$ with $A(f + d) = 1$). The step costs
  $w_{i+1} - w_i = d + 1$ and the phase becomes $f + d + 1$. The next pair is $F(A, B)$ if $B$ is not white. If $B$ is
  white, $D_{i+2}$ accumulates $D_i$ (`D_shift_of_white` of [LeftMemory](../../Rule30Open/Diagonals/LeftMemory.md)):
  $Y(t + 1) = Y(t) \oplus A(t)$ with either integration constant $Y(0)$. If $A$ has even weight, $Y$ has period $P$ and
  the next pair is $(0, Y)$, for both constants; if $A$ has odd weight the period doubles and the walk *exits* period
  $P$.
- $A$ white: the crossing of a white diagonal, FrontWalk's first disjunct with $w_{i+1} = w_i$: cost 0, the same phase,
  next pair $F(0, B)$.

Every step moves one depth. The *excess* of a state at slope $\gamma$ is
$E(s) = \max(0, \mathrm{cost}(s) - \gamma + \max_{s'} E(s'))$ over its successors $s'$: the largest
$(w_{i} - w_{\mathrm{start}}) - \gamma (i - \mathrm{start})$ along any path from $s$ that stays in period $P$, counting
an exit step. It is an optimal potential: $\mathrm{cost}(s) - \gamma \le E(s) - E(s')$ on every edge. It is finite
exactly when no cycle has a mean cost above $\gamma$; $\mu_P$ is the largest cycle mean, the max-plus eigenvalue of
the graph.

Since $F$ is injective, the $4^P$ pairs split into *chains*, one from each $(0, Y)$ with $Y \ne 0$ to an end $(X, 0)$,
and *cycles of $F$*, which contain no white word. A regime of the single cell, from a white diagonal to the next one, is
a stretch of a chain, and a regime that starts after a doubling starts at $(0, Y)$ with $Y$ anti-periodic
($Y(t + P/2) = \lnot Y(t)$). So the quantities that matter are, at $\gamma = 5/2$:

- $R_{\mathrm{all}}$, the largest $E$ over every state; $R_{\mathrm{chain}}$, over the states of chains (they are equal
  at every $P$ computed);
- $R_{\mathrm{start}}$, over the chain starts $(0, Y, f)$; $R_{\mathrm{double}}$, over the starts with $Y$
  anti-periodic, the start of a regime after a doubling ($P$ even).

Cycles of the state graph lie inside cycles of $F$, or pass from chain to chain through white crossings that keep the
period. `walk_eigen.c` walks every chain and every cycle of $F$ once with all $P$ phases at a time: the cycles of the
phase map once around a cycle of $F$ give the cycle means there, the chain summaries (cost, length and end phase from
each start phase) give the graph of chain starts, on which Howard's policy iteration finds the cycle means through
crossings, and one backward pass per chain or cycle gives $E$ at every state.

## The worst case for each period (computed, $P \le 16$)

| $P$ | $\mu_P$ | in cycles of $F$ | pairs of least period $P$ | through crossings | $R_{\mathrm{all}}$ | $R_{\mathrm{start}}$ | $R_{\mathrm{double}}$ |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 2 | 1 | 1 | 1 | none | 0 | 0 | 0 |
| 3 | 7/6 | none | none | 7/6 | 1 | 0 | |
| 4 | 7/3 | 7/3 | 7/3 | 9/7 | 3 | 0 | 0 |
| 5 | 15/8 | 19/11 | 19/11 | 15/8 | 5 | 0 | |
| 6 | **5/2** | 5/2 | 5/2 | 164/83 | 10.5 | 5 | 0 |
| 7 | **5/2** | 5/2 | 5/2 | 73/35 | 18.5 | 4 | |
| 8 | 7/3 | 7/3 | 94/41 = 2.293 | 37/16 | 22.5 | 8 | 3 |
| 9 | 1006/493 = 2.041 | 9/7 | 9/7 | 1006/493 | 29.5 | 9 | |
| 10 | 89/41 = 2.171 | 89/41 | 89/41 | 12181/6033 = 2.019 | 48.5 | 13 | 6 |
| 11 | 59/26 = 2.269 | 59/26 | 59/26 | 831/397 = 2.093 | 44 | 19 | |
| 12 | **5/2** | 5/2 | 36/17 = 2.118 | 10719/5210 = 2.057 | 59.5 | 19 | 11.5 |
| 13 | 2051/1007 = 2.037 | 2051/1007 | 2051/1007 | 21707/10719 = 2.025 | 61 | 32.5 | |
| 14 | **5/2** | 5/2 | 31/14 = 2.214 | 73/35 | 70.5 | 25.5 | 15 |
| 15 | 25/12 | 25/12 | 25/12 | 238686/118621 = 2.012 | 82.5 | 27 | |
| 16 | 7/3 | 7/3 | 130/59 = 2.203 | 37/16 | 88.5 | 28 | 21.5 |

- **No cycle is faster than 5/2.** For every $P \le 16$, $\mu_P \le 5/2$, and the value $5/2$ is reached only by
  cycles of pairs of least period 6 or 7 (at $P = 12$ and 14 by those pairs; the cycles of pairs of least period 12
  and 14 have means $36/17$ and $31/14$). At $P = 7$ the cycle has 14 steps of costs $4, 1, 4, 1, \dots$ on words
  with three adjacent black cells, alone or with one more black cell; at $P = 6$ it has 60 steps, ten costs
  $6, 2, 1, 2, 3, 2, 1, 3, 2, 3$ repeated. The means of the new cycles, those of pairs of least period $P$, are 2.29,
  1.29, 2.17, 2.27, 2.12, 2.04, 2.21, 2.08 and 2.20 for $P = 8$ to 16: no upward trend. The cycles through white
  crossings stay at or below $37/16 = 2.3125$.
- **The excess grows about linearly.** $R_{\mathrm{all}}/P$ is 4.85, 4.00, 4.96, 4.69, 5.04, 5.50 and 5.53 for $P = 10$
  to 16. In this range that is consistent with $R_P = O(P)$, and it cannot tell $P$ from $P \log P$ or from a slowly
  bending curve; the ratio stays between 4 and 5.6. The worst states are deep inside long chains (the longest has
  638,072 pairs at $P = 16$).
- **From the start of a regime the excess is small.** $R_{\mathrm{double}}$, the largest excess from the start of a
  regime after a doubling, is 0, 0, 3, 6, 11.5, 15 and 21.5 at $P = 4$ to 16 (even): it grows by about 2.3 per unit of $P$
  from 8 to 16, too few values to tell a line from a faster curve. From any chain start it is at most $32.5$ for
  $P \le 16$.

The single cell's walk never visits a cycle of $F$: each of its regimes starts at a white diagonal, so it is a
stretch of a chain. The means of the cycles of $F$ bound that walk only through the long chains that pass near them,
which is how $R_{\mathrm{chain}}$ sees them.

## The single cell's walk is a path of these graphs (computed)

`replay` reads the settled words of the single cell (aligned at the first of the last 256 rows of 132,405 steps) and
its least walk (`front_walker.walk_from_tail`), and checks every step of every regime between doublings as an edge:
the cost $w_{i+1} - w_i$, the next pair and the next phase.

| Period | Depths | Steps | Crossings inside the period | Exit (odd weight before a white diagonal) | Steps not edges | Largest excess over $5/2$ from the start |
|---:|---|---:|---|---:|---:|---:|
| 2 | 2 to 6 | 5 | 2 | 6 | 0 | 0 |
| 4 | 7 to 27 | 21 | 7 | 27 | 0 | 0 |
| 8 | 28 to 398 | 371 | 28 | 398 | 0 | 0 |
| 16 | 399 to 87,865 | 87,467 | 399, 53,207, 58,286 | 87,865 | 0 | 0 |

So the conventions of the graph (the alignment, the phase, the integration constants at a white diagonal, the exit at
odd weight) are those of the pattern, including the two white diagonals 53,207 and 58,286 that keep the period 16. The
last column is the largest $(w_i - w_\ell) - \frac{5}{2}(i - \ell)$ over the regime from its start $\ell$: the single
cell's walk never runs ahead of slope $5/2$ from the start of a regime.

## What it gives

**A bound by regimes (paper, given the table).** Along a regime of period $P$ that starts at a white diagonal $\ell$
after a doubling, the walk's states form a path of the graph from a start $(0, Y)$ with $Y$ anti-periodic, so for every
depth $i$ of the regime, and for the depth just after its exit,
$$w_i \le w_\ell + \tfrac{5}{2}(i - \ell) + R_{\mathrm{double}}(P).$$
Summed over the regimes, $w_j \le \frac{5}{2} j + \sum_k R_{\mathrm{double}}(P_k) + c$, the sum over the doublings
before $j$. For the single cell the periods are powers of two and $R_{\mathrm{double}}$ is 0, 0, 3 and 21.5 at $P = 2$, 4,
8 and 16; with $w_2 = 2$ this gives $w_j \le \frac{5}{2} j + 21.5$ for every $2 \le j \le 87{,}866$, using only
that each regime starts after a doubling and has period at most 16, whatever its words are. The kit's main branch bounds the same least walk by
$\mathrm{frontBound}\,k \le 1 + k f(k)$ when every period is at most $f$ (`Rule30FrontLaw.frontBound_le_linear`): a
slope proportional to the period. The table replaces the factor $P$ by the cycle mean $5/2$ and an additive
$R_{\mathrm{double}}(P)$ per doubling, for $P \le 16$.

**For every period (heuristic, not proved).** If $\mu_P \le 5/2$ and $R_{\mathrm{double}}(P) \le c P$ for every power
of two $P$, then $w_j \le \frac{5}{2} j + 2c P_j + O(1)$, and with $P_j = o(j)$ (the heuristic of
[left records](left-records.md) puts the next doubling near depth $2^{33}$) the walk has slope $5/2 + o(1)$. The
window argument of FrontWalker, at $\gamma = 5/2$, would then give black center runs of slope
$3(\gamma - 1)/(5\gamma - 1) = 9/23 \approx 0.391$, against $3/5$ in the kit's main branch; it is proved in Lean at
$\gamma = 2$ and $41/20$ only, and needs the alternation bound $A_J = o(J)$ of SettledSlope as well. Neither the cycle
mean nor the excess is known for any $P$ beyond the table, and the single cell's walk, at 2.01 per depth, is far
below the worst case: the worst cycles live on cycles of $F$ that no regime visits, and on pairs of least period 6 and 7,
which the single cell does not have.

**What a proof for every $P$ would need.** A potential that certifies slope $5/2$ at every period at once. One that
reads the white run ahead of the phase and a window of up to three cells of the pair that holds the phase or ends just
before it does not exist: at every $P$ from 5 to 10, states with the same features are joined by edges or cycles of
mean above $5/2$ ([local walk potentials](../../negative-results/diagonals/local-walk-potential.md)). So the
certificate must know
where the black cells of $B$ sit across a white run of $A$, which is information that grows with the period, as in
[white-run potential](../../negative-results/diagonals/white-run-potential.md).

## Relation to the kit

Checked against the pinned kit and its main branch (`Rule30FrontLaw`, `Rule30LeftAntiPeriod`, `Rule30RightPeriods`
and the equivalents). The main branch has the least walk as `Rule30FrontLaw.frontBound`, with
`D_periodic_from_frontBound` and the period-sum bounds `frontBound_le_periodSum` and `frontBound_le_linear`;
`Rule30LeftAntiPeriod` proves the dichotomy at a white diagonal (period kept, or doubled with an anti-periodic word),
which is the crossing and the exit of the graph here; `Rule30RightPeriods` is about the right diagonals. Neither
revision has the walk on all pair words, a cycle mean or an excess over a slope.

## Reproduce

```bash
python -m computations.walk_eigen --periods 2-14     # mu_P and the excesses, about 3 min, 0.3 GB
python -m computations.walk_eigen --periods 15       # about 10 min
python -m computations.walk_eigen --periods 16       # about 52 min, 0.6 GB
python -m computations.walk_eigen --replay 87866     # the single cell's walk as a path, about 30 s
```

`tests/test_walk_eigen.py` checks the C program's cycle means at $P \le 5$ against every simple cycle of the numpy
graph and its excesses against value iteration, the single cell's walk in the regime of period 4 against the step, and
the costly edge of the negative result.
