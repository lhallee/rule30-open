---
title: Behind a walk through its black cells, a left diagonal of any row white left of a cell forgets the cells past a prefix; this bounds the onsets of every extension of the prefix at once
category: diagonals
problems: [2]
status: proved
lean: Rule30Open.Diagonals.PrefixWalk
headline: [agree_of_walk, Ld_agree_of_prefix, Ld_agree_of_walk, Ld_repeats_of_walk]
kit: refines
kit_modules: [Rule30FiniteDiagonals, Rule30LightCone, Rule30AgedLeftDiagonals]
evidence: [computations/seed_onsets.py]
---

# Behind a walk through its black cells, a left diagonal of any row white left of a cell forgets the cells past a prefix; this bounds the onsets of every extension of the prefix at once

The left diagonals of a row white left of a cell $lo$ settle one after the other, and how late diagonal $j$ settles,
over all rows, is the question of [seed-uniform onsets](../../findings/diagonals/seed-uniform-onsets.md). This module
proves the rule that makes that question computable to depth 76: once the cells $lo, \dots, lo + m + 1$ are fixed,
every deeper diagonal is fixed too from a time read off the fixed cells alone, so one row stands for all rows with the
same prefix after that time.

## Statement

Write $D_k(t) = \mathrm{Ld}\,x\,lo\,k\,t = \mathrm{cell}_t(lo - t + k)$ for a row $x$ white left of $lo$ (the kit's
`Rule30FiniteDiagonals.Ld`), and $D'_k$ for a second such row $x'$. Both satisfy
$D_{k+2}(t+1) = D_k(t) \oplus (D_{k+1}(t) \lor D_{k+2}(t))$ (`DiagStep` and `Ld_diagStep` of
[DrivenSkeleton](DrivenSkeleton.md)). A *walk* from depth $m + 1$ to depth $d$ along $x'$ (`PrefixWalk`) is a
sequence $w$ such that for $m < k < d$ diagonal $D'_k$ is black at some time $r$ with $w_k \le r < w_{k+1}$.

- `forget_of_black`: two arrays with the step that agree on diagonals $k$ and $k+1$ from time $s$, with diagonal
  $k + 1$ black at a time $r \ge s$, agree on diagonal $k + 2$ from time $r + 1$. It is the shift 0 case of
  `shift_of_black` in [DrivenSkeleton](DrivenSkeleton.md), which compares two arrays read with a time shift.
- `agree_of_walk`: two arrays with the step that agree on diagonals $m$ and $m + 1$ at all times agree on every
  diagonal $k$ with $m + 1 \le k \le d$ from time $w_k$, for a walk $w$ along the first.
- `agree_or_flip_of_white`: if they agree on diagonal $k$ from $s$ and both are white on diagonal $k + 1$ from $s$,
  then from $s$ diagonal $k + 2$ of one is that of the other or its complement. It is the shift 0 case of
  `shift_or_flip_of_white` in DrivenSkeleton.
- `Ld_agree_of_prefix`: rows that agree on the cells $lo, \dots, lo + n$ agree on the diagonals $0, \dots, n$ at all
  times.
- `Ld_agree_of_walk`, `Ld_repeats_of_walk`: if $x$ and $x'$ agree on the cells $lo, \dots, lo + m + 1$ and $w$ is a
  walk along $x'$ from depth $m + 1$ to $d$, then $D_k(t) = D'_k(t)$ for $m + 1 \le k \le d$ and $t \ge w_k$; and if
  $D'_d$ repeats with period $P$ from $T$, then $D_d$ repeats with period $P$ from $\max(w_d, T)$.

The cells of $x$ right of $lo + m + 1$ are arbitrary, so the onset of diagonal $d$ over all rows with a given prefix
is at most $\max(w_d, T'_d)$, for one computed row $x'$ and its least walk.

## Argument

1. **Reset** (`forget_of_black`, from DrivenSkeleton's `shift_of_black`). Where $D_{k+1}(r) = 1$ the step gives
   $D_{k+2}(r + 1) = \lnot D_k(r)$ whatever $D_{k+2}(r)$ was, and the same for the second array; since
   $D_k(r) = D'_k(r)$ the two agree at $r + 1$. From there each step reads only cells that agree, so by induction on
   $t$ they agree from $r + 1$ on. This is the mechanism of `D_periodic_of_black` in [LeftMemory](LeftMemory.md) and
   of the kit's `Rule30AgedLeftDiagonals.reset_inherits`, there comparing a diagonal with its own time shift, here
   comparing two rows.
2. **Walk** (`agree_of_walk`). By induction on the depth, the pair $(k, k+1)$ agrees from $w_{k+1}$: the base is the
   hypothesis; the black cell of diagonal $k + 1$ at $r \in [w_{k+1}, w_{k+2})$ makes diagonal $k + 2$ agree from
   $r + 1 \le w_{k+2}$ (step 1), and diagonal $k + 1$ agrees from $w_{k+1} \le w_{k+2}$.
3. **White diagonal** (`agree_or_flip_of_white`, from DrivenSkeleton's `shift_or_flip_of_white`). With diagonal
   $k + 1$ white the step is $D_{k+2}(t + 1) = D_k(t) \oplus D_{k+2}(t)$ in both arrays, and $D_k = D'_k$, so
   $D_{k+2} \oplus D'_{k+2}$ keeps its value at $s$.
4. **Prefix** (`Ld_agree_of_prefix`). $D_k(0) = x(lo + k)$, diagonal 0 is constant and diagonal 1 accumulates it
   (`Ld_zero_succ`, `Ld_one_succ` of the kit, which need the white left side), and diagonal $k + 2$ follows from
   diagonals $k$ and $k + 1$ by the step; strong induction on $k$, then induction on $t$. This is the light cone
   of the kit's `Rule30LightCone.evol_window` for rows white left of $lo$, proved here on the diagonals.
5. **Rows** (`Ld_agree_of_walk`, `Ld_repeats_of_walk`). Step 4 gives the agreement on diagonals $m$ and $m + 1$, step
   2 the rest, and the period carries over from $\max(w_d, T)$ because the two diagonals are equal there.

## How the search uses it

`computations/seed_onsets_prune.c` finds the latest onset $M_j$ of each diagonal $j \le J$ over all rows with a
black cell at $lo$ and white left of it. At a prefix $x_1 \dots x_i$ it knows $D_{i-1}$ and $D_i$ at all times. It
walks: $w_{i+1}$ is one more than the first black cell of $D_i$, the diagonal $D_{i+1}$ is then known from $w_{i+1}$
(it is $\lnot D_{i-1}(r)$ at $r + 1$ and follows by the step), and so on to depth $J$; where a known diagonal is white
to the end of the table (an eventually white diagonal: 2, 7 and 28 in this range) it follows both values of the next
diagonal, as step 3 allows. If for every depth $d$ the bound $\max(w_d, U_d)$, with $U_d$ one more than the last
change with period 8 of the known part, is at most the latest onset found so far at depth $d$, no extension of the
prefix can raise any $M_d$ and the prefix is not extended. The bound is a theorem for the black steps
(`Ld_repeats_of_walk`) and, at the white steps, for each of the two branches (`agree_or_flip_of_white`). That a table
of $H$ times read with period 8 gives the true onsets, when every onset it reports is at most $H - 9$, is the window
argument of [seed-uniform onsets](../../findings/diagonals/seed-uniform-onsets.md); it is checked by the program and
not formalized here.

## What it does not give

As an induction over depths the rule is the front walk of [FrontWalker](FrontWalker.md): the walk advances about two
times per depth, so it bounds the onsets by slope 2, while the latest onsets have slope about $3/2$ in the computed
range. It prunes a prefix only when the walk to every deeper depth stays under the latest onsets, so short prefixes are
always extended, and the number of nodes grows by a factor of 1.2 to 1.9 per depth between $J = 56$ and $J = 76$
(650 thousand at 56, 97 million at 72, 1.37 billion at 76).

## The kit

The kit proves that the left diagonals of every row white left of a cell repeat with period $2^j$ from the onset
$2^j - 1$ (`Rule30FiniteDiagonals.Ld_uniform_period`) and uses the reset to transfer periods of one diagonal
(`Rule30AgedLeftDiagonals.reset_inherits`; the main branch's `Rule30LeftReset.reset_periodic` and
`Rule30FrontLaw`, which bounds the single cell's onsets by a recursive front), and its light cone
(`Rule30LightCone.evol_window`) gives `Ld_agree_of_prefix`. The two-array step lemmas are
[DrivenSkeleton](DrivenSkeleton.md)'s, with the shift 0. What this module adds is the walk: `agree_of_walk` and its
form for rows with a common prefix, `Ld_agree_of_walk` and `Ld_repeats_of_walk`, which bound the onsets of every
extension of a prefix at once.
