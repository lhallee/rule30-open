---
title: After a white run of at least 22, no column repeats 0^q t for any tail t of one to six cells that starts and ends with 1 but 10101
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.TailFamilies14
headline: [cycle_padding_column, tail_thresholds_column, short_tails_column, center_short_tails, not_eventually_short_tails]
kit: refines
kit_modules: [Rule30WhitePadding, Rule30WhiteEndNine, Rule30WhiteEnd, Rule30WhiteRunEight, Rule30FiniteWhiteRuns, Rule30WhitePad10111, Rule30PaddedWords, Rule30FiniteStrips, Rule30FiniteMaskedJen, Rule30ShortTail, Rule30FiveTail, Rule30SixTailSharpened]
evidence: [computations/tail_families.py, computations/limit_windows.py]
---

# After a white run of at least 22, no column repeats 0^q t for any tail t of one to six cells that starts and ends with 1 but 10101

[Limit windows](../../findings/columns/limit-windows.md) computes, with windows of 14 cells followed through the
column's whole history, that the block $0^q t$ is excluded for every $q \ge 22$ and every tail $t$ of at most six cells
but $10101$. This module proves it in Lean, with the least threshold of each tail. The pinned kit excludes the same
families from $q = 49$, $69$ and $74$ for tails of at most four, five and six cells, with sharper bounds for $1$, $11$
and $10111$ and, on its main branch, for nine more tails (see [What the kit has](#what-the-kit-has)). The proof pumps
the white run along residue classes modulo 4, since the white relation's powers cycle with period 4, and checks each
class with the kit's bit-parallel image of a set of windows, which makes 14 cells cheap for the kernel.

## Statement

A *tail* here is a word $u$ of one to six cells that starts and ends with 1. The rows are those with a leftmost 1, and
"repeats $w$" means: from some time $T$ on, column $k$ reads $w$ periodically, starting at any phase of $w$.

- `short_tails_column`: for every tail $u \ne 10101$ and every $q \ge 22$, no column of the orbit of such a row repeats
  $0^q u$. `center_short_tails` is the statement for `Rule30Prize.center`, and `not_eventually_short_tails` is the
  kit's form, with `Rule30StripCertificates.EventuallyWord`.
- `tail_thresholds_column`: the same for every $q \ge q_0(u)$, with the thresholds of the list `thresholds14`. They are
  10 for $1$, 8 for $11$, 9 for $101$, 18 for $111$, 16 for $1001$, 9 for $1011$, $1101$ and $1111$, 11 for $10001$, 8
  for $10011$, 9 for $10111$, 18 for $11001$, 9 for $11011$, 10 for $11101$, 13 for $11111$, and, for the tails of six
  cells, 17 for $100001$, 14 for $100011$, 16 for $100101$, 18 for $100111$, 9 for $101001$, $101011$ and $101111$,
  16 for $101101$, 15 for $110001$, 8 for $110011$, 14 for $110101$, 10 for $110111$, 16 for $111001$, 18 for
  $111011$, 22 for $111101$ and 14 for $111111$. These are the thresholds that `limit_windows.tail_thresholds` computes
  at 14 cells, so each is the least one that windows of 14 cells give.
- `cycle_padding_column`: the general lemma. If the Boolean check `cycleCert K N d k u` holds, with $K \ge 1$ and $u$
  nonempty, no column repeats $0^{N + dm} u$, for any $m \ge 0$.

## Argument

1. **Windows and their sets.** Watch the $K$ cells right of column $k$, with the cell beyond them free. One step
   beside a column reading $x$ sends a window to two windows. A set of windows is a number of $2^K$ bits, and the kit's
   `Rule30WhiteEndNine.fimage` computes the image of a whole set with $O(K)$ operations on numbers of $2^{K+1}$ bits;
   `fimage_mem` is its soundness. Here `enc_fapply` carries it from the single seed to every row (the window encoding
   of `Rule30FiniteStrips`).
2. **A chain of sets excludes a word** (`invariant_column`). Let $C_0$ be all windows, and suppose one period of $w$
   maps $C_n$ into $C_{n+1}$ for $n < k$ and $C_k$ into itself. If column $k$ repeats $w$ from time $T$, the true window
   at the start of every period from the $k$-th on lies in $C_k$. If, at every 0 of $w$, all windows reached from $C_k$
   have the same first cell, then column $k + 1$ at the white times of column $k$ repeats with the period of $w$, and
   masked Jen (`Rule30FiniteMaskedJen.masked_jen`) forbids that.
3. **Pumping a white run along a residue class** (`zf_pump`, `cycle_column`). Write $Z^j(Y)$ for the windows after $j$
   white steps from $Y$. If $Z^d(Z^N(Y)) \subseteq Z^N(Y)$, then $Z^{N + dm}(Y) \subseteq Z^N(Y)$ for every $m$, since
   images are monotone. `cycleCert K N d k u` follows $k$ periods of $0^N u$ from all windows, $C_{n+1} = u(Z^N(C_n))$,
   and checks this inclusion at every $Z^N(C_n)$, the closure $u(Z^N(C_k)) \subseteq C_k$, and that the first cell is
   known after each of the first $N + d$ white steps from $C_k$ and at each 0 of $u$ read from $Z^N(C_k)$. Then the
   same sets are a chain for $w = 0^{N + dm} u$: one period maps $C_n$ into $u(Z^{N + dm}(C_n)) \subseteq C_{n+1}$. A
   white phase $\varphi \ge N + d$ of the run is $N + dm' + e$ with $e < d$, and $Z^{\varphi}(C_k) \subseteq
   Z^{N+e}(C_k)$, which the check covers. With $d = 4$ this is a residue class modulo 4; with $d = 0$ it is the single
   word $0^N u$.
4. **Why a residue class.** Reading 0 is a relation on windows whose powers, at 14 cells, repeat with period 4 after
   53 steps (`limit_windows.white_cycle`). The kit's `Rule30WhitePadding.padding_strip` asks that $Z^{N+1} = Z^N$ on
   its sets, a fixed point. The check with $d = 1$ passes too, but only from $N = 21$ to $32$ depending on the tail;
   with $d = 4$ it passes from $N = 15$ to $29$. So both work, and the residue classes save single words: 378 pieces
   against 503 (`tail_families --lean 6 --step 1`).
5. **Covering every $q \ge q_0$** (`tailCert`, `tailCert_cover`, `tailCert_column`). A tail gets pieces $(N, d, k)$:
   for each residue modulo 4 the least $N \ge q_0$ at which the check of period 4 passes, which is 15 to 29, and every
   $q$ between $q_0$ and the largest of these four $N$ that no piece of period 4 covers, alone. `tailCert` checks every
   piece, that every $q$ in $[q_0, B)$ is covered and that the four $q$ in $[B, B + 4)$ are covered by pieces of period
   4; then every $q \ge q_0$ is $N + dm$ for a piece. The 31 tails have 378 pieces, 124 of period 4 and 254 single
   words, all with $k = 2$ periods but 40 with 3 to 6. The kernel checks them in about 150 seconds (`decide +kernel`,
   one theorem `cert_<u>` per tail).
6. **The tails of at most six cells** (`words`, `short_in_table`). A tail of one to six cells that starts and ends
   with 1 and is not $10101$ is in `thresholds14` with $q_0 \le 22$; the kernel checks this over every word of at most
   six cells. A phase shift is absorbed by starting at a later time (`shift_word`).

## What the kit has

The pinned kit excludes $0^r u$ for every $u$ of at most four cells from $r = 49$ (`Rule30ShortTail`), five from 69
(`Rule30FiveTail`) and six from 74 (`Rule30SixTailSharpened`), every tail of that size, including $10101$ and the tails
that start or end with 0. It has sharper bounds for three tails (collected in `Rule30PaddedWords.paddedBound`): $1$ from
9 for the center column (`Rule30WhiteEndNine`) and from 10 for every column of every row with a leftmost 1
(`Rule30WhiteEnd`), $11$ from 8 (`Rule30WhiteRunEight`, and `Rule30FiniteWhiteRuns` for every column of every nonzero
finite row) and $10111$ from 9 (`Rule30WhitePad10111`). The kit's main branch, after the pinned commit, adds
center-column bounds in its `Rule30PaddedWords`: $1111$ from 7, $1^k$ for $k \ge 3$ from 17 (`Rule30White17Runs`),
$1011$, $10011$, $11011$ and $101111$ from 9 and $1101$ from 11 (`paramStripCert`). So for the center column this
module's $q_0(u)$ equals the kit's for $11$, $1011$, $10111$, $11011$ and $101111$, is above it for $1$ (10 against 9),
$111$ (18 against 17, main branch) and $1111$ (9 against 7, main branch), and is below it for the other 23 tails, among
them $10011$ (8), $1101$ (9), $11111$ (13) and $111111$ (14). The uniform bound 22 for all 31 tails, against 74, is new,
and so is the statement for every column of every row with a leftmost 1 for every tail but $1$; the tails that start or
end with 0, and $10101$, keep the kit's bounds. Its bit-parallel image `fimage`, its strip encoding
(`Rule30FiniteStrips`) and masked Jen are the kit's; the residue-class pumping, the chain soundness for every row and
the covering are new. The kit's five white-padding families (`Rule30UniformWhitePadding`) and `padding_strip` use a
fixed point of the white steps. The kit's main branch has `Rule30ParametricStripCertificates.paramStripCert`, which
replaces the white run by the union of all runs of at least $r_0$ steps, so one check covers every $r \ge r_0$ and every
residue at once; it computes images with the kit's element-by-element `image`, which loops over all $2^K$ windows of a
number of $2^K$ bits (a file of 26 such images from all windows at 14 cells passed 6 GB of memory in the kernel here).
In Python at 14 cells (`tail_families --union 6`) that union check passes for every tail here, but from $q_0 + 1$ to
$q_0 + 3$ for eight of them ($1001$, $1101$, $10001$, $11111$, $110001$, $110101$, $111101$, $111111$), so keeping the
residues apart is what reaches the least thresholds, among them 22 for $111101$.

$10101$ is not good at 14 cells for any $q$; at 20 cells it is from $q = 26$ on
([tail families](../../findings/columns/tail-families.md)).

## Reproduce

```bash
python -m computations.tail_families --lean 6     # the pieces and the table of this module, a few seconds
python -m computations.tail_families --union 6    # the union check of the kit's main branch, 14 cells, about 1 min
lake build Rule30Open.Columns.TailFamilies14      # about 150 s
```
