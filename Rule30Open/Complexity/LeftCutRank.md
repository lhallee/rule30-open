---
title: Across a left cut, rows white beyond a window run on the T-function, a window of j + 1 cells has rank 1 after 2^j steps, and the GF(2) rank of the cut bounds its width
category: complexity
problems: [3]
status: proved
lean: Rule30Open.Complexity.LeftCutRank
headline: [window_center, center_two_pow, tPhiIter_two_pow, testBit_tPhiIter, width_of_independent]
kit: independent
kit_modules: [Rule30Equivalents.TFunction, Rule30Equivalents.TFunctionCycles, Rule30Equivalents.AutomatonGroup]
evidence: [computations/left_cut_rank.py, tests/test_left_cut_rank.py]
---

# Across a left cut, rows white beyond a window run on the T-function, a window of j + 1 cells has rank 1 after 2^j steps, and the GF(2) rank of the cut bounds its width

A row is a map from the integers to colors, one step of Rule 30 is $x'_j = x_{j-1} \oplus (x_j \lor x_{j+1})$, and
$c_t(x)$ is cell 0 after $t$ steps (`evo x t 0`). $\Phi(x) = x \oplus (2x \lor 4x)$ is the kit's T-function on the
natural numbers (`tPhi`, written with shifts), and $\Phi^t$ its $t$-th iterate (`tPhiIter`).

## Statement

- `window_center`: let $D \ge 1$ and let $x$ be white on every cell $i \ge -t + D$. Write $N$ for the number whose bit
  $D - 1 - k$ is $x_{-t+k}$, $0 \le k < D$ (`windowNum`, cell $-t$ the top bit). Then $c_t(x)$ is bit $D - 1$ of
  $\Phi^t(N)$.
- `testBit_tPhiIter`: bit $n$ of $\Phi^L(x)$ is $x_n$ plus the parity, along $x, \Phi(x), \dots, \Phi^{L-1}(x)$, of
  $y_{n-1} \lor y_{n-2}$ (`tLow`), a function of the lowest $n$ bits.
- `tPhiIter_two_pow`: $\Phi^{2^j}(x)$ and $x$ agree on their lowest $j + 1$ bits, for every $j$ and $x$.
- `center_two_pow`: if $x$ is white on every cell $i > -2^j + j$, then $c_{2^j}(x) = x_{-2^j}$.
- `width_of_independent`: let the center factor through a set $S$ at a cut $a$, $c_t(\mathrm{splice}_a(x, z)) = G(F(x), z)$
  for all rows $x, z$ (as in `left_cut_factor` of [LeftCut](LeftCut.md)). If the rows $x^{(0)}, \dots, x^{(m-1)}$ are
  independent over GF(2) at the cut, that is, every nonempty set of them has a completion $z$ at which an odd number of
  their centers $c_t(\mathrm{splice}_a(x^{(i)}, z))$ is black, then $F(x^{(i)}) \ne F(x^{(j)})$ for $i \ne j$, so $S$
  has at least $m$ elements.

So the GF(2) rank of the matrix $[c_t(u, v)]$, $u$ the cells left of the cut and $v$ the rest, is at most the number
$N_{\mathrm{L}}$ of distinct rows, which is at most the width of every ordered decision diagram that reads the row from
the left, at that level. And by `center_two_pow`, on the rows white right of cell $-2^j + j$ the matrix after the
$a \le j + 1$ leftmost cells is the column $u \mapsto x_{-2^j}$ repeated: its rank is 1.

## Argument

**The window.** The repository's number evolution `nevo` (of [ConeScreening](ConeScreening.md)) carries the row with
cell $-t$ as bit 0 and moves bits down: bit $k$ of `nstep r` is $r_k \oplus (r_{k+1} \lor r_{k+2})$. On $D$ bits,
reversing the order turns this into $\Phi$: if $R$ has no bit from $D$ on and $N$ is $R$ read backwards on $D$ bits,
then bit $j < D$ of $\Phi^s(N)$ is bit $D - 1 - j$ of `nevo R s` for every $s$, and `nevo R s` keeps no bit from $D$
on (`tPhiIter_rev`, by induction on $s$, with the cases $j = 0$, $j = 1$, $j \ge 2$ of the two lower bits that
$\Phi$ reads). The center of a row white right of $-t + D - 1$ is bit 0 of `nevo R t` with $R$ the cells
$-t, \dots, -t + D - 1$ (`evo_local`, `evo_rowN`), which is bit $D - 1$ of $\Phi^t(N)$.

**The window at $2^j$ steps.** This is the kit's `orbit_two_pow_mod`, proved again because this library does not
depend on the kit's equivalent forms. Bits below $n$ of $\Phi(x)$ depend only on bits below $n$ of $x$
(`bitsAgree_tPhi`, `bitsAgree_iter`), so `testBit_tPhiIter` follows by induction on $L$. If $\Phi^L(x)$ agrees with
$x$ below bit $n$, then the orbit below bit $n$ repeats after $L$ steps and the parity over $M + L$ steps is the parity
over $L$ steps plus the parity over $M$ (`tLowPar_add`). For $j + 1$: by induction $\Phi^{2^j}$ fixes the lowest
$j + 1$ bits, hence so does $\Phi^{2^{j+1}} = \Phi^{2^j} \circ \Phi^{2^j}$, and bit $j + 1$ of $\Phi^{2^{j+1}}(x)$ is
$x_{j+1}$ plus the parity over $2^j + 2^j$ steps, which is the parity over $2^j$ steps added to itself, 0.
`center_two_pow` applies `window_center` with $D = j + 1$.

**Rank against width.** Take the set of the two rows $x^{(i)}, x^{(j)}$ (`parityUpTo` of its indicator is the xor of
their centers, `parity_pair`). Its completion $z$ gives $G(F(x^{(i)}), z) \ne G(F(x^{(j)}), z)$.

## What it means

These are the tools of [the left-cut rank](../../findings/complexity/left-cut-rank.md), which computes the rank of the
left cut and finds an explicit basis of its rows. `window_center` makes the windowed rank of that entry a computation on
$2^D$ numbers whatever $t$ is. `center_two_pow` is the reason no window of fixed width bounds the rank for every $t$:
at $t = 2^j$ with $j + 1$ at least the window, the windowed matrix has rank 1, so a lower bound that holds for every $t$
must use right settings that reach past cell $-t + \log_2 t$. `width_of_independent` turns a rank bound into a bound on
$N_{\mathrm{L}}$, the quantity of [LeftCut](LeftCut.md).

The kit proves `orbit_two_pow_mod` and `testBit_iterate` in its equivalent forms (`TFunction`, `TFunctionCycles`) and
relates $\Phi$ to rows white right of position 0 (`testBit_orbit`); `window_center` is that bridge in the frame of the
cone, proved through this repository's `nevo`, and `center_two_pow` is `orbit_two_pow_mod` read on the center. The
step from independent rows to distinct states is not in the kit, and the kit has no ordered decision diagram or
communication bound for Rule 30. All of this concerns $c_t$ as a function of an arbitrary row, not the center column of
the single black cell, so it does not bear on the kit's Problem 3.
