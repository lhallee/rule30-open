---
title: If the left diagonals repeat with period 16 from time 3j/2 to depth J, black center runs have 13L at most 3a + 2400 and white blocks reach left at most (a + 100)/3
category: diagonals
problems: [2]
status: proved
lean: Rule30Open.Diagonals.SettledRuns
headline: [no_alt_pair, settled_alt_pair, no_white_pair, erode_alt, black_run_le_of_settled, white_block_le_of_settled]
kit: new
kit_modules: [Rule30Diagonals, Rule30CenterRuns]
---

# If the left diagonals repeat with period 16 from time 3j/2 to depth J, black center runs have 13L at most 3a + 2400 and white blocks reach left at most (a + 100)/3

Without any hypothesis the pinned kit bounds a black run of the center column from time $a$ by $L \le a$
(`Rule30CenterRuns.black_run_le`), and kit pull request #46 (`Rule30BlackRunErosion`, merged after the pinned revision;
see [the kit pull requests](../../literature/kit-pull-requests.md)) by $3a/5$ up to a $\log\log$ term. This module
proves a conditional bound. **The hypothesis is not proved, only checked for $8 \le j \le 7{,}999$ and
$\lceil 3j/2 \rceil \le t \le 12{,}583$.** The module has no asymptotic content: the hypothesis is false for
$J \ge 87{,}867$, and `black_run_le_of_settled` needs $\lfloor 8a/13 \rfloor + 1 \le J$, so with a true hypothesis it
applies only for $a \le 142{,}782$, where the kit's `Rule30CenterRuns` docstring reports a longest black run of 22 up to
time $10^6$. A slope statement needs the period as a parameter (see the end of the Statement).

## Statement

Let $D_j(t) = \mathrm{cell}(t, j - t)$ be the left diagonals. Say the left side is *settled to depth $J$* if every
diagonal $8 \le j \le J$ repeats with period 16 from time $3j/2$ on:

$$\text{(S}_J\text{)}\qquad D_j(t + 16) = D_j(t)\quad\text{for } 8 \le j \le J,\ 2t \ge 3j.$$

- `black_run_le_of_settled`: under (S$_J$), a black run of the center column from time $a \ge 1$ with
  $\lfloor 8a/13 \rfloor + 1 \le J$ and of length $L$ has $13 L \le 3a + 2400$.
- `white_block_le_of_settled`: under (S$_J$), if the cells $-m, \dots, \ell$ of row $a \ge 14$, with
  $\lfloor 2a/3 \rfloor \le J$, are all white, then $3m \le a + 100$.

The depth $J$ matters: the periods of the left diagonals grow, from 16 to 32 at depth 87,867
([the records](../../findings/diagonals/left-records.md)), so (S$_J$) is false for $J \ge 87{,}867$. The left-diagonal
periods are unbounded (Nersissian 2026, in [the literature](../../literature/rule-30.md)), so a fixed period cannot hold
for all $j$; a version with a period parameter $P$ in place of 16, concluding $13L \le 3a + O(P)$, is the natural
general form and is not proved here.

The two parts that need no hypothesis, and drive both:

- `no_alt_pair`: for no $j$ and $T$ do $D_j$ and $D_{j+1}$ alternate in antiphase for all $t \ge T$
  ($D_{j+1}(t) = \lnot D_j(t) = D_j(t+1)$ is false).
- `no_white_pair`: for no $j$ and $T$ are $D_j$ and $D_{j+1}$ both white from $T$ on.
- `settled_alt_pair`: if $D_j$ and $D_{j+1}$ repeat with period $P > 0$ from $T$, and from some $T' \ge T$ they are in
  antiphase at the $P + 1$ times $T', \dots, T' + P$ and $D_j$ alternates over the $P$ steps from $T'$ to $T' + P$,
  then a contradiction follows.
- `alt_forever`, `white_forever`: a sequence that repeats with period $P$ from $T$ and alternates, or stays white,
  over $P$ consecutive steps from some $T' \ge T$ does so forever.
- `erode_alt`: if row $t + 1$ reads the alternating pattern on the cells $\mathrm{lo}..\mathrm{hi}$ then row $t$ does on
  $\mathrm{lo} - 1 .. \mathrm{hi} - 4$, whatever the cells beside it are.

## Argument

1. **Alternation reaches the edge** (`altPair_down`, `no_alt_pair`). Suppose $D_{j+1}$ and $D_{j+2}$ alternate in
   antiphase from $T$. The rule $D_{j+2}(t+1) = D_j(t) \oplus (D_{j+1}(t) \lor D_{j+2}(t))$ has OR equal to 1, so
   $D_j(t) = \lnot D_{j+2}(t+1) = D_{j+1}(t) \oplus 1$ (this is `D_reset` of [LeftMemory](LeftMemory.md)), and $D_j$
   alternates in antiphase with $D_{j+1}$ too. By
   induction $D_0, D_1$ alternate; but $D_0$ is black always and $D_1$ is black from time 1.
2. **White pairs do not occur** (`no_white_pair`). If $D_{j+1}$ and $D_{j+2}$ are white from $T$, the rule gives
   $D_j(t) = D_{j+2}(t+1) = 0$, so $D_j, D_{j+1}$ are white from $T$; descending reaches $D_0$.
3. **A period turns a window into forever** (`alt_forever`, `white_forever`): for $t$ beyond the window,
   $f(t + 1) = f(t + 1 - P)$ and $f(t) = f(t - P)$, and induct.
4. **The trapezoid behind a black run** (`black_block_back`). In a black run of length $L$ from $a$, the cell $-k$ of
   row $t$ is black exactly for even $k$, for $a \le t$ and $t + k < a + L$ (the kit's `black_triangle`). If row $t + 1$ reads the
   alternating pattern $x \mapsto [x \text{ even}]$ on $\mathrm{lo}..\mathrm{hi}$, row $t$ does on $\mathrm{lo} - 1
   .. \mathrm{hi} - 4$ (`erode_alt`): put $A$ = the pattern at $\mathrm{hi}$ and $u, v$ for the unknown cells
   $\mathrm{hi}$ and $\mathrm{hi} + 1$ of row $t$; left-permutivity gives the cells down to $\mathrm{hi} - 5$ as
   functions of $A, u, v$, and the eight cases agree with the pattern at $\mathrm{hi} - 4$ and $\mathrm{hi} - 5$; the
   rest follows by induction, because two adjacent cells of the pattern make the OR 1. So row $a - s$ reads the
   pattern on the cells $-(L - 1) - s .. -4s$.
5. **Windows on the diagonals** (`black_diag`). $D_j(a - s)$ is the cell $j - a + s$ of row $a - s$, which is in the
   trapezoid when $a + 1 \le 2s + j + L$ and $5s + j \le a$. So for 17 consecutive values of $s$ both $D_j$ and
   $D_{j+1}$ read the pattern, in antiphase and alternating.
6. **Choice** (`black_run_le_of_settled`). Put $j = \lfloor 8a/13 \rfloor$ and $s_0 = \lfloor (a + 2 - j - L)/2
   \rfloor$ (or 0). If $13 L > 3a + 2400$ then $L \le a$ (the kit's `black_run_le`) gives $a > 240$, and `omega`
   checks the four inequalities: $a + 1 \le 2 s_0 + j + L$; $5(s_0 + 16) + j + 1 \le a$ (all 17 times in the
   trapezoid); $3(j + 1) \le 2(a - s_0 - 16)$ (the window starts after the settling time of $j + 1$); $j \ge 8$. Then (S$_J$) and
   `settled_alt_pair` make $D_j, D_{j+1}$ alternate in antiphase forever, which step 1 forbids.
7. **White blocks** (`white_triangle`, `white_block_le_of_settled`). White cells $-m..\ell$ of row $a$ leave a white
   triangle: cell $x$ of row $a + i$ is white for $-m + i \le x \le \ell - i$. For $j = \lfloor 2a/3 \rfloor - 1$ the
   diagonals $j$ and $j + 1$ meet it in the 16 times $a, \dots, a + 15$ when $3m > a + 100$, are settled by time $a$,
   and so are white forever; step 2 forbids that.

The slope $3/13$ is $3(\gamma - 1)/(5\gamma - 1)$ at $\gamma = 3/2$, the settling time of diagonal $j$ being
$\gamma j$: [the computation](../../findings/diagonals/settled-runs.md) gives the slope for every $\gamma$ and
$P$, and the settling constants of the true orbit. The constants 2,400 and 100 are not optimized.

## In Lean

`altPair_down` is a case analysis on three Booleans after rewriting with `D_step`. `erode_alt` is the kit's erosion
for the pattern `altPat`, proved here by the eight cases described above and a pair induction; `black_block_back`
induces on $s$ from the kit's `black_triangle` (`Rule30CenterRuns`). `black_run_le_of_settled` supplies explicit
$j$ and $s_0$ and leaves the arithmetic to `omega`. The axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Relation to the kit

The pinned kit's `Rule30CenterRuns` proves $L \le a$ for black runs, and kit pull request #46
(`Rule30BlackRunErosion`, merged after the pinned revision) proves $5L + 18\lfloor \log_2 \log_2 a \rfloor \le 3a + 51$
from the same erosion. Neither assumes or proves a linear settling time of the diagonals; the pinned kit proves each
left diagonal eventually periodic with period $2^j$ (`Rule30Diagonals.D_periodic`), without a bound on the onset in its
statement. This module proves what period 16 from time $3j/2$ to a finite depth would give.
