---
title: To depth 200,000 the single cell's onset front, the edge of the pattern against its translate by the period, gains 0.752 depth per step and moves with the frequencies of the damage edge of random rows and of backgrounds of period 32, within 2.1 combined standard errors; in a game where the settled cells are fair coins, no transient that keeps four or more cells right of the edge holds the gain at 2/3
category: diagonals
problems: [2]
status: computed
formalization: partial
evidence: [computations/onset_edge.py, computations/edge_game.py]
---

# To depth 200,000 the single cell's onset front, the edge of the pattern against its translate by the period, gains 0.752 depth per step and moves with the frequencies of the damage edge of random rows and of backgrounds of period 32, within 2.1 combined standard errors; in a game where the settled cells are fair coins, no transient that keeps four or more cells right of the edge holds the gain at 2/3

[SettledSlope](../../Rule30Open/Diagonals/SettledSlope.md) gives black center runs of slope $3/13$ if the left
diagonals $D_j(t) = \mathrm{cell}(t, j - t)$ settle by $\lceil 3j/2 \rceil + o(j)$, and the onsets sit at the left edge
of the chaotic region ([linear settling leads](../../negative-results/diagonals/linear-settling-leads.md)).
[OnsetEdge](../../Rule30Open/Diagonals/OnsetEdge.md) proves in Lean that this edge is exact: with $X$ the single cell
and $Y(t, x) = X(t + P, x - P)$, both Rule 30 histories, let $L(t)$ be the leftmost cell where they differ and
$d(t) = L(t) + t$ its diagonal. Then $d$ never decreases, $\max_{i \le j} T_i^P$ is the least $t$ with $d(t) > j$, and
each step of the edge follows a law of four cells:

| Shared cell $L - 1$ | Copy white at $L$, at $L + 1$ | Other copy at $L + 1$, $L + 2$ | Move | Depth gain $d(t+1) - d(t)$ |
|---|---|---|---|---:|
| white | any | any | left to $L - 1$ | 0 |
| black | white | any | stay at $L$ | 1 |
| black | black | some black | retreat to $L + 1$ | 2 |
| black | black | both white | retreat to $L + 2$ or further | 3 or more |

A slope $\gamma$ for the onsets is a long-run gain $1/\gamma$, so $3/2$ is a gain of $2/3$
(`EdgeBound` in OnsetEdge, open). This entry measures the gain and the moves, compares them with random rows and with
periodic backgrounds, and computes the least gain an adversary can force on the transient when the settled side is
fair coins.

## The single cell

`onset_edge single` evolves the vector of diagonals $0 .. J$ of `settled_slope.stream` and reads $d(t)$ as the lowest
bit where $v_t$ and $v_{t+P}$ differ. With $P = 32$ (a multiple of every period to depth 200,000), $J = 200{,}000$ and
300,600 steps:

- no step violates the law (it is a theorem, so this checks the code);
- the least $t$ with $d(t) > j$ equals $\max_{i \le j} T_i^{32}$, computed by `settled_slope.stream` with period 32,
  at every depth $j \le 200{,}000$;
- $3d(t) \ge 2t$ at every $t \le 300{,}001$, so `EdgeBound` holds there with $c = 0$ and $P = 32$; past $t = 1{,}000$
  the margin $3d(t) - 2t$ is at least 332.

With $P = 16$ and $J = 87{,}866$ (132,399 steps), where the first diagonal of period 32 stops that edge, the same holds
to $t = 131{,}800$, and its edge agrees with that of $P = 32$ to within one step on the depths both reach (46,207
against 46,208 steps on depths 53,207 to 87,866, gain 0.7500 against 0.7501). By the depth
of the edge, with batch-means standard errors over blocks of 1,000 steps (blocks of 10,000 give 0.0019 for the whole
range, as blocks of 1,000 do):

| Depths of the edge | Steps | Left | Stay | Retreat | Retreat 1 | 2 | 3 or more | Gain | Standard error | Slope $1/\text{gain}$ |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 to 399 | 501 | 0.5549 | 0.1956 | 0.2495 | 0.2016 | 0.0200 | 0.0279 | 0.8024 | | 1.2463 |
| 400 to 53,206 (period 16) | 70,615 | 0.5926 | 0.1465 | 0.2610 | 0.2182 | 0.0214 | 0.0213 | 0.7478 | 0.0036 | 1.3373 |
| 53,207 to 87,866 (period 16) | 46,208 | 0.5890 | 0.1514 | 0.2596 | 0.2167 | 0.0220 | 0.0210 | 0.7501 | 0.0045 | 1.3332 |
| 87,867 to 200,000 (period 32) | 148,650 | 0.5884 | 0.1489 | 0.2627 | 0.2186 | 0.0228 | 0.0214 | 0.7543 | 0.0026 | 1.3257 |
| 400 to 200,000 | 265,473 | 0.5896 | 0.1487 | 0.2617 | 0.2182 | 0.0223 | 0.0213 | 0.7519 | 0.0019 | 1.3300 |

The slopes per regime are the mean onset increments of [linear settling leads](../../negative-results/diagonals/linear-settling-leads.md)
(1.3373, 1.3332, 1.3257), as they must be. Over the 265 windows of 1,000 steps past depth 400 the retreat frequency
ranges from 0.2310 to 0.2990 (standard deviation 0.0123, against 0.0139 for independent steps) and the gain from 0.677
to 0.838.

## Random rows and periodic backgrounds

`onset_edge random` runs two uniform random rows of 10,128 cells, white outside, that differ at one cell (`flip`) or
are independent from that cell on (`half`), for 4,000 steps, 400 samples each, and follows the leftmost difference;
moves and gains are taken after step 200, and the run checks that the edge never reads a cell that the ends of the
rows reach. `onset_edge background` builds a background all of whose left diagonals repeat with period $P$ (from two
random words, each next diagonal set by the reset at a black cell), sets a row equal to it up to one cell and random
beyond, and follows the edge of the row against the background, 200 samples of 3,000 steps each:

| Model | Left speed $\lambda$ | Gain | Standard error | Slope | Left | Stay | Retreat |
|---|---:|---:|---:|---:|---:|---:|---:|
| random rows, one flipped cell | 0.2441 ± 0.0007 | 0.7561 | 0.0008 | 1.3225 | 0.5890 | 0.1477 | 0.2634 |
| random rows, a half line | 0.2432 ± 0.0008 | 0.7567 | 0.0008 | 1.3215 | 0.5889 | 0.1477 | 0.2635 |
| background of period 16 | | 0.7546 | 0.0013 | 1.3251 | 0.5907 | 0.1453 | 0.2640 |
| background of period 32 | | 0.7556 | 0.0012 | 1.3234 | 0.5892 | 0.1475 | 0.2634 |
| single cell, period 32 regime | | 0.7543 | 0.0026 | 1.3257 | 0.5884 | 0.1489 | 0.2627 |

Here $\lambda = (L(0) - L(4000))/4000$ per sample, and $1/(1 - \lambda) = 1.3229 \pm 0.0013$ for one flipped cell.
The law held at every step of every model. In the backgrounds, the edge of the row against its own translate by $P$
coincided with its edge against the background at every time after step 200. Left of its edge against the background
the row is the background, which the translate leaves unchanged; so the translate's edge is never left of it, and it is
right of it only if the edge moves left at each of the next $P$ steps.

**Kill tests.**

- *The identification of the onset slope with the left speed of damage.* In the period 32 regime the single cell's gain
  0.7543 ± 0.0026 differs from the background of period 32 (0.7556 ± 0.0012) by 0.45 combined standard errors, and
  from one flipped cell in random rows (0.7561 ± 0.0008) by 0.66; the test would have killed it at 4. Over the whole
  range past depth 400 the difference from random rows is 0.0042, 2.0 combined standard errors, and in the first
  regime of period 16 the difference from the background of period 16 is 0.0068, 1.8 standard errors.
- *A transient that differs from random rows at the front.* The retreat frequency over windows of 1,000 steps never
  falls below 0.21 (its least value is 0.2310), so this test does not fire.

**What "Lyapunov exponent" means here.** Shereshevsky's left exponent (Shereshevsky 1992, in
[the literature on columns](../../literature/columns.md); Tisseur 2000 in
[measure and analogs](../../literature/measure-and-analogs.md)) is, in the form in which it is usually stated, defined
through the set of all perturbations of a half line (the text itself was not read here; see the note in that
literature file), so it bounds the left speed of every damage edge, not only that of one random perturbation. What is measured here
is the speed of the damage edge of one random perturbation, the damage-spreading speed. So the onset slope matches
$1/(1 - \lambda)$ for that speed, $\lambda = 0.244$, within the errors; whether $\lambda$ is also Shereshevsky's exponent
of the uniform measure is not settled here.

## The edge game: the worst transient against fair settled cells

`edge_game` keeps the cells of both copies on $[L - 1, L + k]$, equal at $L - 1$. Each step a fresh fair cell enters at
$L - 2$; an adversary that sees it chooses both copies' cells at $L + k + 1$; each copy steps by Rule 30 inside the
window; the edge moves by the law; on a left move a second fresh fair cell enters at the new $L - 1$, and on a retreat
the adversary chooses the cells that enter at the right end (if the copies agree on the whole window, it places the
edge at $L + k + 1$ or $L + k + 2$). The adversary minimizes the long-run mean gain. Outside the window it is free at
every step, so it can play every strategy of the game with window $k + 1$, and $v_k$ cannot decrease with $k$. The
least mean gain $v_k$, by relative value iteration (the bounds $\min(Th - h)$ and $\max(Th - h)$ agree to $10^{-8}$ at
every $k$):

| $k$ | States | $v_k$ | $1/v_k$ | Check |
|---:|---:|---:|---:|---|
| 0 | 4 | 0.5 | 2 | all 2,401 memoryless deterministic adversaries; linear program |
| 1 | 16 | 0.6 | 1.6667 | linear program |
| 2 | 64 | 0.6275 | 1.5936 | linear program |
| 3 | 256 | 0.65881 | 1.5179 | |
| 4 | 1,024 | 0.70026 | 1.4280 | |
| 5 | 4,096 | 0.71243 | 1.4036 | |
| 6 | 16,384 | 0.72266 | 1.3838 | |
| 7 | 65,536 | 0.72882 | 1.3721 | |
| 8 | 262,144 | 0.73349 | 1.3633 | |
| 9 | 1,048,576 | 0.73653 | 1.3577 | |
| 10 | 4,194,304 | 0.73875 | 1.3536 | |

The linear program, over all adversaries, is built from a separate simulation of the rows (`explicit_actions`) and
agrees with the value iteration to $10^{-7}$ at $k \le 2$; brute force over memoryless adversaries is possible only at
$k = 0$ (at $k = 1$ there are $6.4 \cdot 10^{11}$ of them).

**Local consistency pushes the worst transient past gain $2/3$.** At $k \le 1$ the adversary decides the cell $L + 1$
nearly freely and holds the gain at $1/2$ to $0.6$, slope 2 to $5/3$. From $k = 4$ Rule 30 inside the window takes that freedom away:
$v_4 = 0.700 > 2/3$, and $v_{10} = 0.739$, within 0.02 of the gain of random rows. The increments of $v_k$ shrink
(0.0047, 0.0030, 0.0022 at $k = 8, 9, 10$). The kill note does not apply: $1/v_6 = 1.384$, not above 1.6.

**Why this is not a theorem about the single cell.** The game's settled cells are fresh coins, independent of what the
adversary did. In the single cell the cells left of the edge are a fixed periodic word, made by the transient that
passed, and a transient that sees them is not playing against coins. So no bound on the onsets follows from $v_k$; it
says only that, if the settled side behaved like coins, no local strategy of the transient could hold the gain at
$2/3$.

## What it means

- The front that [linear settling leads](../../negative-results/diagonals/linear-settling-leads.md) calls the left edge
  of the chaotic region is, exactly, the edge of a difference pattern, and to depth 200,000 it moves like the edge of
  the damage of one flipped cell in random rows or in backgrounds of period 32: the same move frequencies to two or
  three decimals and the same gain within 2.1 combined standard errors. On this reading (a heuristic) the onset slope
  4/3 is $1/(1 - \lambda)$ for the damage-spreading speed $\lambda \approx 0.244$ of Rule 30.
- `EdgeBound`, the open hypothesis of [OnsetEdge](../../Rule30Open/Diagonals/OnsetEdge.md), needs a long-run gain of
  $2/3$; the measured gain is 0.752, and the least window over 1,000 steps is 0.677.
- **Where it stops.** The gain is a frequency of local cases at the edge, and the cases that decide stay against
  retreat sit in the transient. The game bounds those frequencies only against fresh settled cells. A proof needs the
  same kind of statement as the front walk's ([FrontWalker](../../Rule30Open/Diagonals/FrontWalker.md)): that the
  settled cells the edge reads are close enough to fair, along the edge, at every depth.

## Reproduce

```bash
python -m computations.onset_edge single --depth 200000 --period 32                  # about 2.5 min, 0.3 GB
python -m computations.onset_edge single --depth 87866 --period 16                   # about 30 s
python -m computations.onset_edge random --samples 400 --steps 4000                  # about 30 s
python -m computations.onset_edge background --period 32 --samples 200 --steps 3000  # about 40 s
python -m computations.onset_edge background --period 16 --samples 200 --steps 3000  # about 30 s
python -m computations.edge_game --kmax 8                                            # v_0 .. v_8 and the checks, about 15 s
python -m computations.edge_game --kmin 9 --kmax 10                                  # v_9, v_10, about 5.5 min, 1.5 GB
```
