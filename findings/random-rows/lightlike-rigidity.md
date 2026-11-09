---
title: A measure invariant under the shift and Rule 30 that is ergodic for the light-like map is uniform or has zero entropy, the entropy of a cell given the cells to its right can only grow rightward, and Problem 1 holds if one limit measure of the single cell keeps that entropy positive
category: random-rows
problems: [2, 1]
status: paper
formalization: wanted
---

# A measure invariant under the shift and Rule 30 that is ergodic for the light-like map is uniform or has zero entropy, the entropy of a cell given the cells to its right can only grow rightward, and Problem 1 holds if one limit measure of the single cell keeps that entropy positive

Write $F$ for Rule 30, $F(x)_i = x_{i-1} \oplus (x_i \lor x_{i+1})$, $\sigma$ for the shift, $(\sigma x)_i = x_{i+1}$,
and $G = \sigma F$ for the *light-like map*, $(Gx)_i = x_i \oplus (x_{i+1} \lor x_{i+2})$: Rule 30 in the frame that
moves right at the speed of light. $G$ reads only the cell itself and the cells to its right, so it acts on the right
halves $X_k = \{0, 1\}^{[k, \infty)}$ too. $\lambda$ is the uniform measure, and $\mathcal{B}_{\ge k}$ the
$\sigma$-algebra of the cells $\ge k$.

## Results

1. **Monotone entropy profile** (paper). For every $F$-invariant measure $\mu$, the conditional entropy
   $a_k = H_\mu(x_{k-1} \mid \mathcal{B}_{\ge k})$ is non-decreasing in $k$, and so is the conditional entropy of each
   block $x_{[k-n, k-1]}$ given $\mathcal{B}_{\ge k}$; if $\mu$ is only $F^q$-invariant, $a_k \le a_{k+q}$.
2. **Rigidity under light-like ergodicity** (paper). Let $H$ be any automaton of the form
   $(Hx)_i = x_i \oplus \eta(x_{i+1}, \dots, x_{i+r})$, such as $G$, $G^q = \sigma^q F^q$, or Rule 90's light-like map
   $x_i \oplus x_{i+2}$. If $\mu$ is $H$-invariant and ergodic for $H$, every cell $k - 1$ is either *free*, a fair coin
   independent of $\mathcal{B}_{\ge k}$, or *determined*, a function of the cells to its right. If $\mu$ is also
   $\sigma$-invariant, all cells are of the same kind, so $\mu = \lambda$ or $\mu$ has zero entropy under $\sigma$.
3. **For Rule 30** (paper). If $\mu$ is invariant under $\sigma$ and $F$ and the light-like map is ergodic for it,
   which holds exactly when $G$ on the right halves $X_0$ is ergodic for the law of $x_{\ge 0}$, then $\mu = \lambda$
   or $x_{-1}$ is almost surely a function of $x_{\ge 0}$. The same for $\sigma$- and $F^q$-invariant measures with
   $G^q$ ergodic.
4. **The hypothesis is needed** (Lean). The rows that come back after 12 steps moved 12 cells to the right form a set of
   positive entropy ([LightLikeEntropy](../../Rule30Open/RandomRows/LightLikeEntropy.md); 12 is the least such period,
   by the kit's main branch, `Rule30MovingWaves`); it carries measures invariant
   under $\sigma$ and $F$ with positive entropy that are not uniform, and on it $G^{12}$ is the identity, so those
   measures are not ergodic for $G$.
5. **Consequences for the single cell** (paper). Every limit point $\mu$ of the averages
   $\frac{1}{N}\sum_{t < N} \delta_{F^t(\text{single cell})}$ is $F$-invariant, and the density of black cells of the
   center column along a subsequence is $\mu(x_0 = 1)$.
   - *Problem 1 from one entropy.* If the center column is eventually periodic with period $P$, then for every such
     $\mu$, $x_{-P}$ is almost surely a function of the cells $> -P$ (since $F^P(x)_0 = x_{-P} \oplus g_P(x_{-P+1}, \dots,
     x_P) = x_0$ holds $\mu$-almost surely), so $a_{-P+1} = 0$ and by item 1 $a_k = 0$ for every $k \le -P + 1$. So
     **Problem 1 holds if some limit point $\mu$ has $\inf_k H_\mu(x_{k-1} \mid x_{\ge k}) > 0$**: if, in the limit, the
     cells far left of the center are not functions of the cells to their right.
   - *Problem 2 as rigidity.* If a limit point is $\sigma$-invariant (H1), ergodic for $G$ (H2) and of positive entropy
     (H3), it is $\lambda$ by item 3, and along that subsequence the center column has density $1/2$ (under $\lambda$ the
     center column is a sequence of fair coins, the kit's `Mixing.measurePreserving_line`). If every limit point
     satisfies them, the center column is normal. All three are open for the single cell, and item 4 shows that (H2)
     cannot be dropped.
6. **Open: is $\lambda$ itself ergodic for $G$?** The positive branch of items 2 and 3 is used only if it is. On the
   right halves, $G$ is a skew product with fiber $\{0, 1\}$ over a copy of itself, $y_0 \mapsto y_0 \oplus (y_1 \lor
   y_2)$; an invariant function splits into an invariant function one cell further right and a twisted part $h$ with
   $h \circ G = (-1)^{y_0 \lor y_1} h$ (after reindexing), and since the product measure has a trivial tail, $\lambda$
   is ergodic for $G$ exactly when this twisted equation has no nonzero square-integrable solution. Not settled here.

## Proofs

**Item 1.** Let $\Phi_k : X_k \to X_{k+1}$ be $F$ on half lines, and $s_k = 2\mu(x_{k-1} = 1 \mid \mathcal{B}_{\ge k}) -
1$, a function on $X_k$. Since $F(x)_k = x_{k-1} \oplus (x_k \lor x_{k+1})$ with the OR measurable in
$\mathcal{B}_{\ge k}$, the bias of $F(x)_k$ given $\mathcal{B}_{\ge k}$ is $\omega_k s_k$, $\omega_k = (-1)^{x_k \lor x_{k+1}}$, and
conditioning on the coarser $\sigma$-algebra generated by $F(x)_{> k} = \Phi_k(x_{\ge k})$ gives, by $F$-invariance,
$s_{k+1} \circ \Phi_k = E[\omega_k s_k \mid \Phi_k^{-1}\mathcal{B}]$. Binary entropy is concave and symmetric, so by
conditional Jensen $a_{k+1} \ge a_k$, with equality exactly when $s_{k+1} \circ \Phi_k = \omega_k s_k$. For blocks, given
$x_{\ge k}$ the map $x_{[k-n, k-1]} \mapsto F(x)_{[k-n+1, k]}$ is a bijection (Rule 30 is permutive in its left cell), and
the same two steps apply; for $F^q$, $F^q(x)_k = x_{k-q} \oplus g_q(\dots)$ does the same with a shift of $q$.
$\square$

**Item 2.** $H$-invariance and $(Hx)_{k-1} = x_{k-1} \oplus \eta(x_{[k, k+r-1]})$ give, by the same computation without
conditioning on a coarser algebra, $s_k \circ H_k = E[\omega^\eta_k s_k \mid H_k^{-1}\mathcal{B}]$ with
$\omega^\eta_k = (-1)^{\eta}$; since $H_k$ preserves the law of $x_{\ge k}$, both sides have the same $L^2$ norm, so
$s_k \circ H_k = \omega^\eta_k s_k$ almost surely. So $|s_k|$ is $H_k$-invariant, hence constant, $c$, the factor
$(X_k, H_k)$ of an ergodic system being ergodic. If $c = 0$ the cell is free. If $c > 0$, $u = s_k/c$ has
$u \circ H_k = \omega^\eta_k u$, and $w(y) = (-1)^{y_{k-1}} u(y_{\ge k})$ on $X_{k-1}$ satisfies
$w \circ H_{k-1} = (-1)^{y_{k-1}} (\omega^\eta_k)^2 u = w$; by ergodicity of $(X_{k-1}, H_{k-1})$, $w$ is constant, so
$x_{k-1}$ is a function of $x_{\ge k}$ and $c = 1$. With $\sigma$-invariance all cells have the same kind; if all are
free, every cylinder has measure $2^{-\text{length}}$ by peeling off its leftmost cell, so $\mu = \lambda$; if all are
determined, $h_\mu(\sigma) = H_\mu(x_{-1} \mid \mathcal{B}_{\ge 0}) = 0$. $\square$

**Item 3.** Item 2 with $H = G$ (or $G^q$). For $\sigma$-invariant $\mu$ the shift identifies $(X_k, G)$ with
$(X_0, G)$ for every $k$; if $G$ on $X_0$ is ergodic, an invariant function on the whole line has constant conditional
expectations on every $\mathcal{B}_{\ge k}$, and these converge to it as $k \to -\infty$ (Lévy), so $(\mu, G)$ is ergodic.
The converse is a factor. $\square$

**Item 4.** [LightLikeEntropy](../../Rule30Open/RandomRows/LightLikeEntropy.md) proves the positive entropy in Lean and
builds the measures on paper; on its set $G^{12} = \sigma^{12} F^{12}$ is the identity, so a $G$-ergodic measure there is
carried by one finite orbit, and the measures of positive entropy are not $G$-ergodic. $\square$

**Item 5.** The averages converge along subsequences to $F$-invariant measures (Krylov and Bogolyubov), and
$\{x_0 = 1\}$ and $\{F^P(x)_0 \ne x_0\}$ are clopen; under the averages the second has mass at most $t_0/N$ if the
center column is periodic from $t_0$. The rest is items 1 and 3. $\square$

**Item 6.** On $X_0$, $(Gy)_0 = y_0 \oplus (y_1 \lor y_2)$ and $(Gy)_{\ge 1}$ depends on $y_{\ge 1}$ only, so writing an
invariant $f = g(y_{\ge 1}) + (-1)^{y_0} h(y_{\ge 1})$ splits the equation into $g \circ G = g$ and
$h \circ G = (-1)^{y_1 \lor y_2} h$ on $X_1$, a copy of $X_0$. Iterating, $f$ is the sum of twisted parts at each level
and a tail function, which is constant for $\lambda$. $\square$

## What it means

Problem 2 asks for $\mu(x_0 = 1) = 1/2$ at every limit point of the single cell's orbit. Item 3 turns it into three
structural properties of those limit points, none of which is a statement about fair coins, and item 5 turns Problem 1
into the positivity of one conditional entropy. Item 4 says that the light-like ergodicity cannot be dropped, because
Rule 30 has rows that travel at the speed of light in uncountable families. The obstacle is the same as everywhere in
this repository: nothing proves any of (H1) to (H3), or the positive entropy, for the single cell, whose rows have zero
spatial entropy.

## Relation to the literature and the kit

Measure rigidity is known for automata that are permutive on both sides: Host, Maass and Martínez for affine ones,
Pivato (2005) and Sablik (2007) for algebraic and bipermutative ones ([measures and analogs](../../literature/measure-and-analogs.md)).
Rule 30 is permutive only in its left cell, and its light-like map only in its own cell. A preprint of Tal
(arXiv:2604.10124, 2026), seen only as a record, states a constraint for invariant measures of bipermutative automata and
asks which other automata have $\lambda$ as their only ergodic invariant measure of positive entropy; its text was not
read, so items 1 and 2 are claimed as new only against the kit and this repository. Item 4 shows that the constraint in
the form without ergodicity fails for Rule 30. The kit's `Mixing` proves that the lines of velocity other than 1 are
fair coins under $\lambda$ and excepts velocity 1, and `PeriodicPoints` excludes recurring rows at every velocity in
$[-1, 1)$; neither treats invariant measures other than $\lambda$ or the light-like direction. The kit's main branch,
after the pinned commit, has the light-like direction in `Rule30MovingWaves`, which proves that 12 is the least period
at which the rows travelling at light speed to the right have positive entropy; it does not treat invariant measures.
