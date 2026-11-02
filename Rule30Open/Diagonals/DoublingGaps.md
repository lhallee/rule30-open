---
title: A left diagonal is eventually white exactly when the diagonal four before it is eventually the AND of the next two, and after a period doubling at half-period 1, 2 or 4 the next white diagonal is at least 5, 21 or 88 depths later
category: diagonals
problems: [2]
status: proved
lean: Rule30Open.Diagonals.DoublingGaps
headline: [D_no_two_white, D_white_iff_and, D_doubling_odd_weight, D_doubling_gap, doublingGap_one, doublingGap_two, doublingGap_three, doublingGap_four, doublingGap_exact]
kit: refines
kit_modules: [Rule30Diagonals]
evidence: [computations/doubling_gaps.py]
---

# A left diagonal is eventually white exactly when the diagonal four before it is eventually the AND of the next two, and after a period doubling at half-period 1, 2 or 4 the next white diagonal is at least 5, 21 or 88 depths later

The periods of the single cell's left diagonals grow only by doubling, right after an eventually white diagonal
([LeftMemory](LeftMemory.md)). How far apart the doublings are bounds the periods: if a doubling to period $2p$ is
always followed by at least $m(p)$ depths before the next white diagonal, the periods grow at most as fast as the
inverse of $m$. This module proves the local facts the spacing rests on and the first values of $m$ for the single
cell. The census of $m(p)$ to $p = 16$, the structured families to $p = 40$, and the computation that
$m(p) > 49$ except at $p = 1, 2, 5$ are in [doubling gaps](../../findings/diagonals/doubling-gaps.md).

## Statement

Let $D_j(t) = a_t(j - t)$ be the kit's left diagonal `Rule30Diagonals.D`, with
$D_{j+2}(t+1) = D_j(t) \oplus (D_{j+1}(t) \lor D_{j+2}(t))$ (`D_step`). "Eventually" means for every $t$ from some
time on.

- `D_no_two_white`: $D_i$ and $D_{i+1}$ are never both eventually white.
- `D_white_iff_and` (the white-step identity): $D_{j+4}$ is eventually white if and only if eventually
  $D_j(t) = D_{j+1}(t) \land D_{j+2}(t)$.
- `D_doubling_odd_weight` (descent): if $D_j$ has period $P$ from $T$, $D_{j+1}$ is white from $T$, and $D_{j+2}$
  has period $P$ from no time on, then $D_j$ has an odd number of black cells in each period, and for $P = 2Q$,
  $D_j$ has period $Q$ from no time on.
- `doublingGap_one` to `doublingGap_four`, `doublingGap_exact` (the census of the pair map, $p \le 4$):
  on words of period $2p$ written as natural numbers (bit $t$ is the cell at time $t \bmod 2p$), the orbit of the pair
  map from $(0, Y)$, for every anti-periodic $Y$ of least period $2p$ ($Y(t + p) = \lnot Y(t)$), has a non-white
  second word for its first $m(p) - 1$ steps, each computed word checked to solve the step relation, with
  $m(1), \dots, m(4) = 5, 21, 56, 88$; the word $Y = 1^p 0^p$ reaches the white word at step $m(p)$.
- `D_doubling_gap`: if $D_w$ is white from $T$ and $D_{w+1}(t + p) = \lnot D_{w+1}(t)$ for $t \ge T$, with
  $p = 1, 2$ or $4$, then $D_{w+k}$ has black cells at arbitrarily late times for every $1 \le k < m(p)$,
  $m(p) = 5, 21, 88$: the next white diagonal is at least $w + m(p)$.

## Argument

1. **Backward step and no two whites.** The step solved for $D_j$ reads
   $D_j(t) = D_{j+2}(t+1) \oplus (D_{j+1}(t) \lor D_{j+2}(t))$ (`DoublingGaps.back`, the kit main branch's
   `D_back`). If $D_{i+1}$ and $D_{i+2}$ are white from $T$, it makes $D_i$ white from $T$; descending, $D_0$ would
   be white, but $D_0$ is black (`D_zero`).
2. **White-step identity, forward.** Let $D_{j+4}$ be white from $s$ and write $x = D_{j+3}$. The step into
   $D_{j+4}$ gives $D_{j+2} = x$; the step into $D_{j+3}$ gives $D_{j+1}(t) = x(t) \oplus x(t+1)$; the step into
   $D_{j+2}$ gives $D_j(t) = x(t) \land \lnot x(t+1)$, which is $D_{j+1}(t) \land D_{j+2}(t)$. This is the kit main
   branch's `Rule30LeftAntiPeriod.D_white_prev_three` in another form, reproved here because the pinned kit does not
   have it.
3. **White-step identity, converse.** Let $D_j = D_{j+1} \land D_{j+2}$ from $s$ on and write $b = D_{j+2}$. The
   step into $D_{j+2}$ gives $D_{j+1}(t) = b(t) \oplus b(t+1)$ (`change_of_and`). Then the step into $D_{j+3}$ shows
   that $e(t) = D_{j+3}(t) \oplus b(t)$ satisfies $e(t+1) = e(t) \land \lnot b(t)$ (`copy_step`), so after a black
   cell $r_1$ of $b$, $D_{j+3} = D_{j+2}$; and then the step into $D_{j+4}$ gives
   $D_{j+4}(t+1) = \lnot b(t) \land D_{j+4}(t)$, so after a later black cell $r_2$ of $b$, $D_{j+4}$ is white
   (`white_of_and`). Black cells of $b$ occur at arbitrarily late times: otherwise $b$ is eventually white, then so is
   $D_{j+1} = b \oplus b(\cdot + 1)$, against step 1.
4. **Descent.** By `LeftMemory.D_period_dichotomy`, behind the white $D_{j+1}$ the diagonal $D_{j+2}$ fails period
   $P$ only when $D_j$ has odd parity over a period. If also $D_j$ had period $Q$ with $P = 2Q$, its parity over $2Q$
   consecutive times would be the parity over $Q$ taken twice (`windowParity_add`, `windowParity_double`), so even.
5. **The pair map on words.** Behind a black cell $r$ of $D_{j+1}$, $D_{j+2}$ is reset to $\lnot D_j(r)$ and from
   there follows the step, so on words of period $P$ the next word is determined by the two before it once the second
   is not white ([settled words](../../findings/diagonals/settled-words.md)). `DoublingGaps.next` computes it, starting
   from the first black cell, and `stepOK` checks that a word solves $c(t+1) = a(t) \oplus (b(t) \lor c(t))$ around
   the cycle; `regimeOK P n a b` checks $n$ steps of the orbit, each with a non-white second word and a checked next
   word. The census theorems are one `decide +kernel` each over the words below $2^{2p}$.
6. **From the words to the diagonals.** Read $D_{w+1}$ at times $T, \dots, T + 2p - 1$ as the word $Y$ (`word`,
   `bit_word`); it is anti-periodic (`anti_word`), so the census applies to it. By induction along the orbit
   (`track`): if $D_{w+k}$ and $D_{w+k+1}$ follow the words $a$ and $b$ from some time on (`D (w + k) (T + t)` is bit
   $t \bmod 2p$), and $b$ has a black cell at $r$, then $D_{w+k+2}$ follows the checked next word from one turn after
   $r$ (`follow`: both satisfy the same recursion and agree right after the reset). A diagonal that follows a word
   with a black cell is black at arbitrarily late times (`black_late`).

## In Lean

`windowParity` and `D_period_dichotomy` come from [LeftMemory](LeftMemory.md). The census theorems are about the
functions `next`, `stepOK` and `regimeOK` on natural numbers, evaluated by the kernel; their link to the diagonals
does not depend on `next` being correct, since `follow` uses only the checked step relation. The census for $p = 3$
leaves out $010101$ and $101010$, whose least period is 2 (they are anti-periodic with half-period 3 and have gap 5),
and `D_doubling_gap` is stated for $p = 1, 2, 4$, the half-periods of the single cell's doublings among the first
four (all its periods are powers of two). The module builds in about 12 s.

## What it gives and what it does not

For the single cell, $D_7$ is white and $D_8$ is anti-periodic with half-period 2, so `D_doubling_gap` gives no white
diagonal before depth 28, which is where the next one is; after the doubling at 28 it gives none before 116, and the
next is at 399. A lower bound $m(p) \ge f(p)$ for every $p$ would bound the number of doublings below depth $j$ by
$f^{-1}$ and so the period $P_j$, through `LeftMemory.D_period_doubles`; this module proves $f$ only for $p \le 4$,
and [doubling gaps](../../findings/diagonals/doubling-gaps.md) records the census and why a bound for every $p$ is
not in reach of these methods.

## Relation to the kit

The pinned kit has `Rule30Diagonals.D`, `D_step`, `D_zero` and `D_periodic`, which this module uses. The kit's main
branch (checked at its current head) has `Rule30LeftAntiPeriod.D_white_prev_three`, the forward direction of
`D_white_iff_and`, `D_back`, `Rule30LeftUnbounded.D_no_two_white` (the statement of `D_no_two_white`) and `Rule30WhiteSpacing`, which proves that white diagonals are at least five apart and
exactly five apart only at depth 2. The converse of the white-step identity, the descent to full period, the census
$m(p)$ and `D_doubling_gap` are not in either part of the kit.
