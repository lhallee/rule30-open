---
title: Uncountably many rows come back after 12, 15 or 17 steps moved as many cells to the right, so the rows that travel at the speed of light carry invariant measures of positive entropy that are not uniform
category: random-rows
problems: [2]
status: proved
lean: Rule30Open.RandomRows.LightLikeEntropy
headline: [LightLikeEntropy.lightLike_blocks, LightLikeEntropy.blocks_window_determines, LightLikeEntropy.sigma12_entropy, LightLikeEntropy.sigma15_entropy, LightLikeEntropy.sigma17_entropy]
kit: refines
kit_modules: [Rule30Equivalents.PeriodicPoints]
---

# Uncountably many rows come back after 12, 15 or 17 steps moved as many cells to the right, so the rows that travel at the speed of light carry invariant measures of positive entropy that are not uniform

The kit proves that Rule 30 has no gliders slower than light: a row that comes back after $k$ steps moved $d$ cells,
with velocity $-d/k$ in $[-1, 1)$, is spatially periodic, and at most $4^k$ rows do so. The one velocity it leaves out
is the speed of light to the right. There the picture changes completely: for $p = 12$, 15 and 17 the rows that come
back after $p$ steps moved $p$ cells to the right form a set of positive entropy, so it is uncountable, and it carries
measures invariant under the shift and under Rule 30 that have positive entropy and are not the uniform measure.

## Statement

Write $F$ for one step of Rule 30 and $\sigma$ for the shift, $(\sigma x)_i = x_{i+1}$, and let
$\Sigma_p = \{x : F^p x = \sigma^{-p} x\}$, the rows with $F^p(x)_i = x_{i-p}$ for every $i$ (`LightLike p x`). For a
block length $L$, two words $X, Y$ of $L$ cells and $s : \mathbb{Z} \to \{0, 1\}$, let `blocks L X Y s` be the row
whose block on the cells $Lq, \dots, Lq + L - 1$ is $X$ when $s(q) = 1$ and $Y$ otherwise.

1. **Rows of blocks** (`lightLike_blocks`). If $p \le L$ and the finite check `checkG p L X Y` passes, every row
   `blocks L X Y s` lies in $\Sigma_p$.
2. **The blocks can be read off** (`blocks_window_determines`). If $X$ and $Y$ differ at one cell, the cells
   $0, \dots, Ln - 1$ of `blocks L X Y s` determine $s(0), \dots, s(n - 1)$.
3. **Three instances** (`sigma12_entropy`, `sigma15_entropy`, `sigma17_entropy`). The check passes for $p = 12$ with
   $L = 34$, $X = ab$ and $Y = ba$, where $a = 11110010011110111100$ and $b = 11110010011110$, for $p = 15$ with two
   words of 31 cells and for $p = 17$ with two words of 26 cells. So at least $2^n$ words of length $Ln$ occur in rows
   of $\Sigma_p$, and the topological entropy of $\Sigma_{12}$, $\Sigma_{15}$ and $\Sigma_{17}$ is at least
   $(\log 2)/34$, $(\log 2)/31$ and $(\log 2)/26$.
4. **Invariant measures** (proved on paper from items 1 to 3). For $p = 12$, 15 and 17 there is a measure on rows,
   invariant under $\sigma$ and under $F$, of positive entropy under $\sigma$, that is not of the form
   $t\lambda + (1 - t)\nu$ with $\lambda$ the uniform measure and $\nu$ of zero entropy.

## Argument

**Items 1 to 3.** Rule 30 is permutive in its left cell, so $F^p(x)_i$ reads the cells $i - p, \dots, i + p$, and the
module checks this light cone on finite words (`iterate_getD`). With $i = Lq + r$, $0 \le r < L$, these $2p + 1$ cells
lie in the blocks $q - 1$, $q$ and $q + 1$ when $p \le L$ (`window3_spec`). So whether $F^p(x)_i = x_{i-p}$ depends
only on $s(q - 1)$, $s(q)$, $s(q + 1)$ and $r$: $8L$ cases, which `checkG` runs and the kernel evaluates
(`check12`, `check15`, `check17`, by `decide +kernel`). Two words that differ at cell $r_0$ make $s(q)$ the cell
$Lq + r_0$ of the row (`blocks_determines`).

**Item 4.** $F$ commutes with $\sigma$, so $\Sigma_p$ is closed, invariant under $\sigma$, and mapped into itself by
$F$; on $\Sigma_p$, $F^p = \sigma^{-p}$ is a bijection, so $F$ is a homeomorphism of $\Sigma_p$ that commutes with
$\sigma$. By the variational principle $\Sigma_p$ carries a $\sigma$-invariant measure $\mu$ whose entropy is the
topological entropy of $\Sigma_p$, positive by item 3. Each $F^j_* \mu$ is $\sigma$-invariant with the same entropy,
since $F^j$ conjugates $\sigma$ on $\Sigma_p$ to itself, and $F^p_* \mu = \sigma^{-p}_* \mu = \mu$; so
$\bar\mu = \frac1p \sum_{j < p} F^j_* \mu$ is invariant under $\sigma$ and $F$, and its entropy is the same, entropy
being affine. Whether $F^p(x)_i = x_{i-p}$ holds depends only on the cells $i - p, \dots, i + p$, and it fails
somewhere for the single black cell, so some word of $2p + 1$ cells occurs in no row of $\Sigma_p$, and
$\lambda(\Sigma_p) = 0$; a combination $t\lambda + (1 - t)\nu$ carried by $\Sigma_p$ has $t = 0$, and then
$\nu = \bar\mu$ has positive entropy. $\square$

So a rigidity theorem for Rule 30 of the form "an invariant measure is uniform or of zero entropy" needs a further
hypothesis. On $\Sigma_p$ the light-like map $\sigma F$, $(\sigma F x)_i = x_i \oplus (x_{i+1} \lor x_{i+2})$, has
period $p$, so an ergodicity hypothesis along the light-like direction is the natural one; the measures above are not
ergodic for it, and with it the alternative holds ([light-like rigidity](../../findings/random-rows/lightlike-rigidity.md)).

## What the kit has

The kit's `Rule30Equivalents.PeriodicPoints` (`eq_of_recurs_of_eq_on`, `recurs_add_factorial`, `ncard_recurs_le`)
proves that a row with $F^k x = \sigma^d x$ is determined to the left by any $2k$ adjacent cells and is spatially
periodic when $1 - k \le d \le k$, so at most $4^k$ rows do this, and that Rule 30 has no gliders at the velocities
$-d/k$ in $[-1, 1)$; for $|d| > k$ an easier argument (each cell a function of the $d + k$ cells on one side) gives the
same. The case $d = -k$, velocity 1 to the right, is the one its argument leaves out: there the permutive cell
$x_{i-k}$ is the cell being compared, and it cancels. This module settles that case for $k = 12$, 15 and 17, in the
other direction.
