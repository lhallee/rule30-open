---
title: Exponential width of left-to-right decision diagrams for every t is not reached; the a leftmost cells are pairwise distinguishable exactly up to a = t - 1, t - 2, t - 3, t - 4 for t in 9-12, 13-17, 18-21, 22-24, one level below what unrestricted letters allow, and every route to a bound for every t meets the eventual left edge of the single cell
category: complexity
problems: [3]
status: negative
kind: barrier
evidence: [computations/letter_words.py, computations/letter_words.c, tests/test_letter_words.py]
---

# Exponential width of left-to-right decision diagrams for every t is not reached; the a leftmost cells are pairwise distinguishable exactly up to a = t - 1, t - 2, t - 3, t - 4 for t in 9-12, 13-17, 18-21, 22-24, one level below what unrestricted letters allow, and every route to a bound for every t meets the eventual left edge of the single cell

**Question.** Write $c_t$ for the center cell after $t$ steps as a function of the cells $x_{-t}, \dots, x_t$ of an
arbitrary row, and $N_{\mathrm{L}}(t, a)$ for the number of distinct functions of the other cells that the $a$ leftmost
cells leave (the width at level $a$ of every ordered decision diagram that reads the row from the left). Is there a
level $a = \Omega(t)$ with $N_{\mathrm{L}}(t, a) \ge 2^{\Omega(t)}$ for every $t$, for instance
$N_{\mathrm{L}}(t, a) = 2^a$ for every $a \le ct$? [LateSeedCut](../../Rule30Open/Complexity/LateSeedCut.md) and
[LateSeedCutWide](../../Rule30Open/Complexity/LateSeedCutWide.md) prove $N_{\mathrm{L}}(t, a) = 2^a$ for $a \le 13$ from
a threshold on in $t$, a constant width; [the left cut](left-cut.md) shows $N_{\mathrm{L}}(t, t - 2) < 2^{t-2}$ from
$t = 18$.

**Outcome.** No bound that grows with $t$ is proved. The computations place the true range: $N_{\mathrm{L}}(t, a) = 2^a$
exactly for $a \le a^*(t)$ with $a^*(t) = t - 1, t - 2, t - 3, t - 4$ for $t$ in $9..12$, $13..17$, $18..21$, $22..23$, and
the separation that every letter word would allow, ignoring which words completions produce, is at most one level more.
Each route to a statement for every $t$ stops at the same place: probes that reduce to a bounded block (the only ones
that give a finite check per $a$) read the eventual left edge of the single cell, whatever the completion, at depth
proportional to $a$; the linear-algebra routes are capped by the thin language of letter words
([LetterWords](../../Rule30Open/Complexity/LetterWords.md)); and steering a pair apart through the triangular structure
needs the common cells between the pair's difference and the cut to pass the completion's influence, which stripes
ending in a black wall stop.

## The setting

The cone is the number $N = 2^a r + P$ ($P$ the $a$ left cells, $r$ the completion), one step is
$\mathrm{nstep}(N) = N \oplus ((N \gg 1) \lor (N \gg 2))$, and the completion acts on $P$ only through its letters
$e_s = \mathrm{nevo}(r, s) \bmod 4$; by the horizon of LateSeedCut the center is $R(M_w P)$, where $M_w$ composes the
three frozen-boundary steps of the kit's automaton group 2369 along the word $w = e_0 \cdots e_{T-1}$,
$T = t - \lceil a/2 \rceil + 1$, and $R$ is bit 0 after $\lceil a/2 \rceil - 1$ more steps. So
$N_{\mathrm{L}}(t, a) = 2^a$ if and only if every two settings $P \ne Q$ have a word $w \in W_T$ with
$R(M_w P) \ne R(M_w Q)$. $W_T$ is the language of [the rank ceiling](left-cut-rank-ceiling.md): six two-letter
constraints, $|W_T| = 4, 10, 22, \dots, 89850$ for $T \le 16$, growth at most $1.8283^T$, not of finite type in the range
computed.

## The true range

$N_{\mathrm{L}}(t, a)$ by refining the $2^a$ settings with the columns of the words of $W_T$ (`refine` and `wordmat` of
`computations/letter_words.c`; every count for $t \le 14$ agrees with the full truth table, and the deficits at
$t = 18, 19, 20$ with [the left cut](left-cut.md)):

| $t$ | 9-12 | 13-17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 |
|---|---|---|---|---|---|---|---|---|---|
| largest $a$ with $N_{\mathrm{L}}(t, a) = 2^a$ | $t - 1$ | $t - 2$ | 15 | 16 | 17 | 18 | 18 | 19 | 20 |
| $2^{t-2} - N_{\mathrm{L}}(t, t - 2)$ | 0 | 0 | 4 | 14 | 26 | 54 | 88 | 164 | 270 |
| $2^{t-3} - N_{\mathrm{L}}(t, t - 3)$ | 0 | 0 | 0 | 0 | 0 | 0 | 8 | 8 | 16 |

and $N_{\mathrm{L}}(t, t - 4) = 2^{t-4}$ at $t = 22, 23, 24$, $N_{\mathrm{L}}(t, t) = 2^t$ for $t \le 8$, and
$2^{16} - N_{\mathrm{L}}(17, 16) = 66$. A merge at level $a$ is a merge at level $a + 1$ (append the same cell to both
settings), so these entries fix the largest level. It moves one level down every four or five steps of $t$ (at
$t = 9, 13, 18, 22$), so $a^*(t) \approx 7t/9 + 1$ in this range, as the stripe heuristic of [the left cut](left-cut.md)
suggested. Every merged class computed sits on a stripe that ends black at the cut. At $t = 18$ they are that entry's
stripes, which fix the center. At $t = 22$, $a = 19$, the 8 merged pairs all end in the alternating run
$x_{-18}, \dots, x_{-4}$ that is black at $x_{-4}$, the cell next to the cut, have $x_{-19}$ free, and differ by flipping
$x_{-22}, x_{-21}, x_{-20}$ together ($000$ against $111$, $100$ against $011$, $010$ against $101$, $110$ against $001$):
the wall hides the completion well enough that this flip of the three leftmost cells is invisible to every
completion. On 400 random completions, two of the pairs ($x_{-19} = 0$ and $010 / 101$, $110 / 001$) gave a constant
center, 1 and 0, and the other six depend on the completion. At $t = 23$, $a = 20$, the 8 merged pairs end in the
alternating run $x_{-19}, \dots, x_{-4}$, black at $x_{-4}$, and differ in their first four cells.

**What unrestricted letters allow.** With every word of $T$ letters over the three steps allowed (backward refinement,
`ideal`), the $2^a$ settings separate from $T = 1, 2, 3, 3, 4, 4, 5, 5, 7, 7, 8, 8, 9, 10, 11, 12, 13, 13, 14, 14, 16, 16, 18$
for $a = 2, \dots, 24$, that is from $t = T + \lceil a/2 \rceil - 1$; the largest separated $a$ is then
$9, 9, 10, 11, 12, 13, 14, 14, 15, 16, 16, 17, 18, 19, 20, 21$ for $t = 9, \dots, 24$, against the true
$8, 9, 10, 11, 11, 12, 13, 14, 15, 15, 16, 17, 18, 18, 19, 20$ for $t = 9, \dots, 24$. The language costs at most one level,
and the range near $0.8t$ belongs to the frozen-boundary automaton itself: even unrestricted, $T + \lceil a/2 \rceil$
must reach about $1.2a$.

## Where the routes stop

1. **Late completions of any shape.** A completion white next to the cut until close to the horizon acts on the left
   cells as a bijection followed by a bounded block, which is what makes a finite check per $a$ possible (LateSeedCut,
   `lateSep_all`). The block comes from the left edge of the completion's pattern when it reaches the cut, at depth up
   to twice its length. In the periodic regime that edge is the single cell's, shifted in time: for 1000 random rows
   white left of a black cell at each of the depths $J = 20, 40, 60$, the low $J$ cells of the left edge from time
   $1.5J + 40$ on (past the settling times of [the seed onsets](../../findings/diagonals/seed-uniform-onsets.md)) are
   the single cell's at one of its phases, 4 of them at depth 20 and all 8 at depths 40 and 60 (`edge_shift`). This is
   what the three free bits behind the single cell's white diagonals at depths 2, 7 and 28
   ([LeftMemory](../../Rule30Open/Diagonals/LeftMemory.md) and its reset recursion) leave room for below depth 399. So
   arbitrary late completions give the late-seed probes at shifted phases and nothing else, and a check that holds for
   every $a$ needs a property of the single cell's
   eventual left edge at depth about $2.2a$, where its diagonals are generated by a recursion with no known closed
   form.
2. **Linear algebra over the columns.** The rank, the real rank and the spectral bound $4^a / \lVert C \rVert_F^2$
   ($C$ the correlation of two settings' functions under a random completion) are at most the number of distinct
   columns, at most $|W_T|$ (LetterWords, `cut_rank_le`): about $1.83^{t - a/2}$, so $2^{0.61t}$ over all levels at best.
   The spectral bound with uniform completions is much smaller: $2^{2.77}, 2^{4.22}, 2^{4.61}$ at $t = 10$,
   $a = 4, 6, 8$, and $2^{4.79}, 2^{6.19}, 2^{6.48}, 2^{5.70}$ at $t = 14$, $a = 6, 8, 10, 12$, because settings that
   differ only near $x_{-t}$ have strongly anticorrelated functions ($C = -1$ when they differ in $x_{-t}$ alone), which
   the bound counts like merges.
3. **Steering a pair apart.** The highest cell where two settings differ (next to the cut, in the bit order of the
   numbers) is invariant, so $N_{\mathrm{L}}(t, a) = 2^a$ splits exactly into: for every $m \le a$ and every prefix $u$ of
   $a - m$ cells, two settings of $m$ cells that differ at their cell $m - 1$ are separated by a completion starting
   with $u$. For such a pair the columns of cell $m - 1$ are complements, the difference one cell further left toggles
   whenever the column after the cut is white, and the two subsystems of the remaining $m - 1$ cells receive
   complementary steps at every time: one gets $\tau \circ \Phi$, the other $\Phi$ or $\sigma \circ \Phi$ as the cell
   after the cut is white or black. The control reaches the pair only through $u$, and a stripe ending in a black wall
   at the end of $u$ keeps the wall black and forgets what lies beyond it, which is how every merge computed arises.
   Below the top difference, the difference moves left only through ors whose other input is the pair's own cell, and
   no quantity was found that the steps cannot keep from reaching $x_{-t}$.
4. **Exact uniformity.** The kit's `card_trace` makes the vertical center column of a random row uniform. Along the cut
   nothing like it holds: the first light-like diagonal of a random completion takes only 302 of the 512 words of 9
   letters (2, 4, 8, 16, 30, 54, 96, 170, 302 for 1 to 9 letters), so no exact count of separating completions comes
   from uniformity.

## What it means

Every bound for every $t$ that grows with $t$ needs $a \to \infty$ and so a statement uniform in $a$; the reductions
available (LateSeedCut's `lateSep_all`, which holds for every $a$) make each $a$ a finite check, but the checks read the
single cell's eventual left edge deeper and deeper. The width itself is not in doubt in the range computed: it is $2^a$
up to $a^*(t) \approx 0.8t$, so at least $2^{a^*(t)}$ at that level, and larger beyond it (48,606 at $t = 14$,
$a = 16$, against $2^{12}$ at $a^*(14) = 12$); the exact count fails only where a stripe ending at the cut screens the
completion, in every merge computed. A proof would need either a pseudorandomness property of the eventual left edge at depth
$2.2a$ for every $a$ (the uniform form of [the late seeds](../../Rule30Open/Complexity/LateSeedCut.md)), or a mixing
statement for the frozen-boundary automaton driven by the words of $W_T$, for settings without long stripes.

**Reproduce.**

```bash
python -m computations.letter_words --threshold 17 23   # N_L at a = t - 2, t - 3, t - 4 (about 1 h at t = 23)
python -m computations.letter_words --ideal 24          # unrestricted letters, a <= 24 (a minute)
python -m computations.letter_words --edges 60 1000     # eventual left edges of random seeds (seconds)
```
