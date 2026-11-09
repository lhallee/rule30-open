---
title: A completion acts on the left cut through words that avoid six two-letter patterns, at most 2 P(T + 1) of them, so the GF(2) rank of the left cut is at most that for every t, and the conjectured rank 2 + floor(2^(t-3)/3) at a = t - 3 fails for every t ≥ 24
category: complexity
problems: [3]
status: proved
lean: Rule30Open.Complexity.LetterWords
headline: [letter_allowed, wordList_mem_allowed, allowedWords_length, lateCen_word, cut_rank_le, cut_rank_lt_rhoCut]
kit: new
kit_modules: [Rule30Equivalents.AutomatonGroup]
evidence: [computations/letter_words.py, computations/letter_words.c, tests/test_letter_words.py]
---

# A completion acts on the left cut through words that avoid six two-letter patterns, at most 2 P(T + 1) of them, so the GF(2) rank of the left cut is at most that for every t, and the conjectured rank 2 + floor(2^(t-3)/3) at a = t - 3 fails for every t ≥ 24

A row is a map from the integers to colors, one step of Rule 30 is $x'_j = x_{j-1} \oplus (x_j \lor x_{j+1})$, and
$c_t(x)$ is cell 0 after $t$ steps, a function of $x_{-t}, \dots, x_t$. Cut the cone after its $a$ leftmost cells, as
in [LateSeedCut](LateSeedCut.md): the cone is the number $2^a r + P$, $P$ the $a$ left cells and $r$ the completion,
one step is $\mathrm{nstep}(N) = N \oplus ((N \gg 1) \lor (N \gg 2))$, and $c_t$ is bit 0 of $\mathrm{nevo}(N, t)$. The
*letter* of the completion at time $s$ is $e_s = \mathrm{nevo}(r, s) \bmod 4$ (`letter`), its two cells next to the cut,
bit 0 the one next to it. Let $n = \lceil a/2 \rceil - 1$ and $T = t - n$.

## Statement

- `letter_allowed`: for every $r$ and $s$, $e_{s+1}$ follows $e_s$ by `allowedNext`: after 0 comes 0, 2 or 3; after 1
  comes 1, 2 or 3; after 2 comes 1 or 3; after 3 comes 0 or 2. The six pairs 01, 10, 20, 22, 31, 33 never occur.
- `wordList_mem_allowed`, `allowedWords_length`, `wordBound_values`: the word $e_0 \cdots e_{T-1}$ of every completion
  lies in a list of $\mathrm{wordBound}(T) = 2P_{T+1}$ words, $P$ the Pell numbers ($P_{k+1} = 2P_k + P_{k-1}$):
  4, 10, 24, 58, 140, 338, 816, 1970 for $T = 1, \dots, 8$.
- `lateCen_word`: if $2n + 1 \le a$, the center after $T + n$ steps depends on the completion only through its word of
  $T$ letters.
- `cut_rank_le`: let $1 \le a \le t$. If the rows $x^{(0)}, \dots, x^{(m-1)}$ are independent over GF(2) at the cut after
  their $a$ leftmost cells (every nonempty set of them has a completion $z$ at which an odd number of their centers
  $c_t(\mathrm{splice}_{-t+a}(x^{(i)}, z))$ is black, the notion of `width_of_independent` in
  [LeftCutRank](LeftCutRank.md)), then $m \le 2P_{T+1}$. So the GF(2) rank of the matrix $[c_t(u, v)]$ ($u$ the $a$ left
  cells, $v$ the rest) is at most $2P_{T+1}$, for every $t$.
- `cut_rank_lt_rhoCut`: for every $t \ge 24$, fewer than $\rho(t - 3) = 2 + \lfloor 2^{t-3}/3 \rfloor$ left settings are
  independent at the cut after $t - 3$ cells.

[The left-cut rank](../../findings/complexity/left-cut-rank.md) computed $\mathrm{rank}(t, a) = \rho(a)$ for every
$a \le t - 3$ and $t \le 14$ and conjectured it, with its stripe basis $B_a$ of $\rho(a)$ settings independent, for every
$t$. `cut_rank_lt_rhoCut` refutes the conjecture for every $t \ge 24$;
[the rank ceiling](../../negative-results/complexity/left-cut-rank-ceiling.md) gives the exact ranks, which fall below $\rho(t-3)$ from $t = 15$ on.

## Argument

**The constraints** (`letter_allowed`). With $M = \mathrm{nevo}(r, s)$ and its bits $b_0, b_1, b_2, b_3$, the letters
are $e_s = b_0 + 2b_1$ and $e_{s+1} = (b_0 \oplus (b_1 \lor b_2)) + 2(b_1 \oplus (b_2 \lor b_3))$ (`testBit_nstep`,
`mod_four_eq`). If $b_1 = 1$, bit 0 flips; if $b_1 = 0$ and bit 0 flips, then $b_2 = 1$ and bit 1 becomes black. The
sixteen cases give exactly `allowedNext`.

**The count** (`wordSets`, `wordList_mem`, `wordSets_length`). Split the words that obey the constraints by their last
letter, low (0 or 1) or high (2 or 3). A low word goes on with its own last letter (low) or with 2 or 3 (high); a high
word goes on with one low and one high letter (2 with 1 or 3, 3 with 0 or 2). So the lists of low and high words of
$k + 1$ letters have $L_{k+1} = L_k + H_k$ and $H_{k+1} = 2L_k + H_k$ members from $L_1 = H_1 = 2$, and every word of a
completion lies in the list its last letter names, by induction on its length with `letter_allowed`. $L_k + H_k$ is
$2P_{k+1}$.

**The center through the word** (`lateCen_word`, `center_splice_eq`). By the horizon of LateSeedCut (`lateCen_eq`), the
center after $T + n$ steps is bit 0 of $\mathrm{nevo}(A_T, n)$, where $A_T$ is the left part after $T$ letters
(`aliceRun`); `aliceRun_congr` makes it a function of the letters at times below $T$, which the word lists. A spliced row
is the number of its cone by `evolve_splice_late`, the completion read off its cells from the cut to $t$ (`coneNum`).

**The rank** (`cut_rank_le`). For a subset $c$ of the rows let its parity vector list, for every allowed word $w$, the
parity of the centers of the rows in $c$ driven by $w$ (`pv`). There are $2^m$ subsets (`allBits`) and at most
$2^{2P_{T+1}}$ parity vectors; if $m > 2P_{T+1}$, two different subsets $c \ne c'$ have the same vector
(`exists_collision`, a pigeonhole from `List.Nodup.length_le_of_subset`). Their symmetric difference is nonempty
(`exists_ne_index`), and at every completion $z$ its parity is the sum of the parities of $c$ and $c'$
(`parityUpTo_xor`) read at the word of $z$, which is an allowed word, where they agree: it is 0 at every completion,
against independence.

**The threshold** (`wordBound_lt_rhoCut`). At $a = t - 3$ the bound is $2P_{T+1}$ with $T = t - \lceil (t-3)/2 \rceil + 1$.
At $t = 24, 25$ it is $390{,}050$ and $941{,}664$ against $\rho = 699{,}052$ and $1{,}398{,}103$ (`decide`). From $t$ to
$t + 2$, $T$ grows by one, the bound grows by a factor at most 3 (`wordBound_succ_le`) and $\rho$ by at least
$4\rho - 6$ (`rhoCut_add_two`), so the inequality persists. It also holds at $t = 22$ and fails at $t = 23$
($390{,}050 > 349{,}527$), by `computations/letter_words.py`.

## What it means

The completion is $2t + 1 - a$ cells, but the left cut sees it only through one word of $T \approx t - a/2$ letters from
a thin language: the words obey the six two-letter constraints, and by exact enumeration ([the rank
ceiling](../../negative-results/complexity/left-cut-rank-ceiling.md)) there are only $|W_T| = 4, 10, 22, 50, 104, 208,
406, 774, 1466, 2728, 4994, 9038, 16174, 28814, 51010, 89850$ of them for $T \le 16$ (the ratio of the last two is 1.76
and still falling), against $2P_{T+1} \approx 2.41^T$ here. Every bound on the cut that goes through linear algebra over
the columns (the GF(2) rank, the real rank, the spectral bound $4^a / \|C\|_F^2$) is at most the number of distinct
columns, so at most $|W_T|$: at the level $a$ it is at most about $1.83^{t - a/2}$, and over all levels at most $2^{0.61
t}$ or so (with the entropy bound $\log_2 1.8283$ of the shift of 13-blocks). The width $N_{\mathrm{L}}(t, a)$, the
number of distinct rows, has no such ceiling: it is $2^a$ for every $a \le t - 4$ at $t = 22, 23, 24$, by computation
([the exponential width](../../negative-results/complexity/exponential-left-width.md)). So rank methods cannot prove the
exponential widths that the counts show at $a$ near $t$, and the stripe basis of the left-cut rank finding is
independent only while $|W_T| \ge \rho(a)$, roughly $a \le 0.6 t$.

The kit's `AutomatonGroup` has the three frozen-boundary steps through which the letters act (the letter 0 is
$\Phi$, 2 is $\sigma \circ \Phi$ and 1, 3 are $\tau \circ \Phi$, with the bits in the other order); it has no statement
about which letter sequences a completion produces, no rank or width bound for the cut, and no decision-diagram or
communication bound. The constraints, the count and the rank ceiling are new.
