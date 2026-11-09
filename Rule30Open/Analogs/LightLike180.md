---
title: Rule 180's light-like map is not ergodic for the uniform measure, because each of its light lines is constant where the next one is white
category: analogs
problems: [2]
status: proved
lean: Rule30Open.Analogs.LightLike180
headline: [LightLike180.const_on_zeros, LightLike180.no_zero_between, LightLike180.pair_dichotomy, LightLike180.line_const_iff]
kit: new
kit_modules: [Rule30Equivalents.Mixing]
---

# Rule 180's light-like map is not ergodic for the uniform measure, because each of its light lines is constant where the next one is white

Rule 180, $F(x)_i = x_{i-1} \oplus (x_i \land \lnot x_{i+1})$, is permutive in its left cell like Rule 30, and its
light-like map $H = \sigma F$, $(Hy)_i = y_i \oplus (y_{i+1} \land \lnot y_{i+2})$, has the shape of Rule 30's
$y_i \oplus (y_{i+1} \lor y_{i+2})$: permutive in its own cell, nonlinear in the two cells to its right, a skew
product with fiber $\{0, 1\}$ over a copy of itself. Yet $H$ is not ergodic for the uniform measure $\lambda$: the
half-lines whose light line $0$ never changes form an invariant set of measure $2/3$. So no proof that Rule 30's
light-like map is ergodic can rest on that shape alone ([light-like mixing](../../findings/random-rows/lightlike-mixing.md)).

## Statement

Write $c^j_t = (H^t y)_j$ (`line y j t`). Line $j$ changes between $t$ and $t + 1$ exactly when
$(c^{j+1}_t, c^{j+2}_t) = (1, 0)$ (`flip_iff`).

1. **Constant on the white times of the next line** (`const_on_zeros`). For every half-line $y$, every $j$ and all
   times $a \le b$ with $c^{j+1}_a = c^{j+1}_b = 0$: $c^j_a = c^j_b$.
2. **Black between white times** (`no_zero_between`). If $c^{j+1}$ is $0$ at $a$ and $a + n$ and $1$ in between,
   then $c^{j+2}_s = 1$ for $a < s < a + n - 1$.
3. **Dichotomy** (`pair_dichotomy`). On every interval of times, lines $j + 1$ and $j + 2$ never read both $1\,0$ and
   $0\,0$; and line $j$ is constant up to $T$ exactly when they never read $1\,0$ before $T$ (`line_const_iff`).

## Consequences (paper)

Let $a_T = \lambda(c^0_t = c^0_0 \text{ for } t \le T) = \lambda(E_T)$, $E_T$ the event that lines 1 and 2 never read
$1\,0$ before $T$. Flipping $y_1$ preserves $\lambda$, commutes with $H$ on the half-lines from cell 1, complements line
1 and keeps the lines from 2 on; it maps $E_T$ to the event $E'_T$ that lines 1 and 2 never read $0\,0$ before $T$. By
item 3, $E_T \cup E'_T$ is everything, and $E_T \cap E'_T$ is the event that line 2 is black up to $T - 1$, which is
$y_2 = 1$ together with an event of lines 3, 4 independent of $y_2$, of probability $a_{T-1}$ by shift invariance. So
$2 a_T - a_{T-1}/2 = 1$, $a_0 = 1$, and

$$a_T = \tfrac{2}{3} + \tfrac{1}{3}\,4^{-T}.$$

The set $E_\infty$ of half-lines whose light line 0 never changes has $\lambda(E_\infty) = 2/3$, and
$E_\infty \subseteq H^{-1} E_\infty$ with equal measures, so it is invariant modulo $\lambda$: **$H$ is not ergodic.**
The two-sided map $\sigma F$ of Rule 180, which has $(X_0, H)$ as a factor, is not ergodic either; Rule 180 itself is
mixing (permutive in its left cell at offset $-1$, the kit's argument for Rule 30). Rule 210, its complement
conjugate, is the same. Exhaustive evolution confirms $a_T$ for $T \le 12$, and the exact law of the letter process
gives $\rho(k) = \mathbb{E}(-1)^{c_0 \oplus c_k} = 1 - 2^{-2^{v}}$, $v$ the 2-adic valuation of $k$, for $k \le 22$
([light_line.py](../../computations/light_line.py)).

## Argument

Strong induction on $n = b - a$, proving item 1 ($P_n$) and item 2 ($Q_n$) together.

- $Q_n$ from $P_m$ ($m < n$) and $Q_{n-1}$ (`Q_step`). Line $j + 1$ changes at $a$ and at $a + n - 1$ only, so lines
  $j + 2, j + 3$ read $1\,0$ at both times and never in between. A white time $s$ of line $j + 3$ strictly between would
  carry, by $P_{s-a}$ at level $j + 2$, the value $1$ of line $j + 2$ at $a$, and lines $j+2, j+3$ would read $1\,0$ at
  $s$; so line $j + 3$ is black strictly between $a$ and $a + n - 1$. Then $Q_{n-1}$ at level $j + 2$ makes line
  $j + 4$ black strictly between $a$ and $a + n - 2$, so line $j + 2$ does not change on $[a, a + n - 2)$ (at $a$ line
  $j + 3$ is white) and stays $1$.
- $P_n$ from $P_m$ ($m < n$) and $Q_n$ (`P_step`). A white time of line $j + 1$ strictly between splits the interval.
  Otherwise line $j$ changes at $s$ only if $c^{j+1}_s = 1$ and $c^{j+2}_s = 0$, which $Q_n$ excludes strictly inside
  and the change of line $j + 1$ at $a + n - 1$ excludes at the end.

## What the kit has

The kit's main branch has Rule 180's single-seed orbit (`Rule30Rule180LoneSeed`) and its wedge parity
(`Rule30WedgeParity.rule180_wedge_odd`); the light-like direction of Rule 180 is in neither the kit nor this
repository. The rigidity entry ([light-like rigidity](../../findings/random-rows/lightlike-rigidity.md), item 6) cites a
conjecture of Shirvani and Rogers that every onto automaton other than the identity and the inversion is ergodic for
$\lambda$, from search results; if it is stated so, $\sigma F$ for Rule 180 contradicts it. Its text could not be read
here, and search snippets suggest that counterexamples are known; check before citing.
