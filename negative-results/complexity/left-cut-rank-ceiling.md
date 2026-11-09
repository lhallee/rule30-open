---
title: The GF(2) rank of the left cut after t - 3 cells falls below 2 + floor(2^(t-3)/3) from t = 15 on, because the completion acts through a thin language of words, so the stripe basis is not independent for every t
category: complexity
problems: [3]
status: negative
kind: refuted
evidence: [computations/letter_words.py, computations/letter_words.c, tests/test_letter_words.py]
---

# The GF(2) rank of the left cut after t - 3 cells falls below 2 + floor(2^(t-3)/3) from t = 15 on, because the completion acts through a thin language of words, so the stripe basis is not independent for every t

**Question.** Write $c_t$ for the center cell after $t$ steps as a function of the cells $x_{-t}, \dots, x_t$ of an
arbitrary row, $\mathrm{rank}(t, a)$ for the GF(2) rank of the matrix $[c_t(u, v)]$ with $u$ the $a$ leftmost cells and
$v$ the rest, and $\rho(a) = 2 + \lfloor 2^a / 3 \rfloor$. [The left-cut rank](../../findings/complexity/left-cut-rank.md)
computed $\mathrm{rank}(t, a) = \rho(a)$ for every $a \le t - 3$ and $t \le 14$, found an explicit basis $B_a$ of
$\rho(a)$ settings, and conjectured that $B_a$ is independent, so that $\mathrm{rank}(t, a) = \rho(a)$, for every $t$
and every $a \le t - 3$. With $a = t - 3$ this would give every left-to-right ordered decision diagram of $c_t$ a level of
width $2 + \lfloor 2^{t-3}/3 \rfloor$ for every $t$.

**Outcome.** The conjecture is false. $\mathrm{rank}(15, 12) = 1035 < \rho(12) = 1367$, by two computations that share
no code beyond the step of the rule, and $\mathrm{rank}(t, t - 3) < \rho(t - 3)$ at every $t$ computed from 15 to 20.
For every $t \ge 24$ it is proved in Lean ([LetterWords](../../Rule30Open/Complexity/LetterWords.md),
`cut_rank_lt_rhoCut`). The reason is structural: the completion acts on the left cells only through its word of
$T = t - \lceil a/2 \rceil + 1$ letters, its two cells next to the cut at each time, and these words form a thin
language, so the matrix has at most $|W_T|$ distinct columns.

## The ranks

From the columns of every word (`wordmat` of `computations/letter_words.c`, which also counts $N_{\mathrm{L}}$); the
entries at $t \le 14$ are those of the left-cut rank finding, and $\mathrm{rank}(14, 11)$, $\mathrm{rank}(15, 12)$ were
also computed from every completion directly (`rank_and_nl_full` on small cases in the test, a C run of all $2^{19}$
completions for $t = 15$):

| $t$ | 14 | 15 | 16 | 17 | 18 | 19 | 20 |
|---|---:|---:|---:|---:|---:|---:|---:|
| $\mathrm{rank}(t, t - 3)$ | 684 | 1035 | 1351 | 1896 | 2467 | 3428 | 4441 |
| $\rho(t - 3)$ | 684 | 1367 | 2732 | 5463 | 10924 | 21847 | 43692 |
| largest $a$ with $\mathrm{rank}(t, a) = \rho(a)$ | 11 | 11 | 12 | 12 | 13 | 14 | 14 |
| $\lvert W_T \rvert$ at $a = t - 3$ | 1466 | 2726 | 2728 | 4992 | 4994 | 9036 | 9038 |

For $15 \le t \le 18$ every $a$ from 4 to the level in the third row has $\mathrm{rank}(t, a) = \rho(a)$ (computed for
every such $a$), and every larger $a \le t - 2$ has less; for $t = 19$ and $20$ the levels from $t - 6$ to $t - 3$ were
computed. $N_{\mathrm{L}}(t, t - 3) = 2^{t-3}$ at all these $t$: the width stays full where the rank falls.

## Why

The letter of a completion at time $s$ is $e_s = \mathrm{nevo}(r, s) \bmod 4$; by the horizon of
[LateSeedCut](../../Rule30Open/Complexity/LateSeedCut.md) the center reads only $e_0, \dots, e_{T-1}$, so every column of
the matrix is the column of a word, and the rank is at most the number $|W_T|$ of words that completions produce:

| $T$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $\lvert W_T \rvert$ | 4 | 10 | 22 | 50 | 104 | 208 | 406 | 774 | 1466 | 2728 | 4994 | 9038 | 16174 | 28814 | 51010 | 89850 |

(over every completion of $2T$ cells; $T \le 8$ also by plain list runs in the test). At $a = t - 3$ and $t = 16$ this
is $2728 < \rho(13) = 2732$, and the gap widens: $|W_T|$ grows like $1.76^T$ with $T \approx t/2$, $\rho$ like $2^t$.
The words avoid the six pairs 01, 10, 20, 22, 31, 33 of consecutive letters (letter $= e_0 + 2e_1$, $e_0$ the cell next to
the cut), which alone allow $2P_{T+1}$ words ($P$ the Pell numbers), and that weaker count suffices from $t = 24$ on,
in Lean. Longer constraints cut the growth further: the shift of finite type whose $k$-blocks are the words of $W_k$ has
spectral radius 2.4142, 2.2470, 2.2470, 2.0945, 2.0217, 1.9799, 1.9419, 1.9168, 1.8875, 1.8630, 1.8461, 1.8283 for
$k = 2, \dots, 13$, so $|W_T| = O(1.8283^T)$; the minimal forbidden words number 6, 2, 0, 8, 10, 12, 24, 32, 72, 130, 184
for lengths 2 to 12, so $W$ is not of finite type in this range.

## What it means

The stripe basis $B_a$ is the right count where $|W_T| \ge \rho(a)$, roughly $a \le 0.6t$, and fails beyond: the rank is
a ceiling of the language, not of the cut. Every linear-algebra bound on the cut (GF(2) rank, real rank, the spectral
bound $4^a / \lVert C \rVert_F^2$) is at most the number of distinct columns, so at most $|W_T| = O(1.8283^{t - a/2})$,
and over all levels at most about $2^{0.61 t}$. That is still exponential in $t$, so a rank proof of exponential width is
not excluded; but the conjectured route, $\rho(a)$ at $a = t - 3$, is. The widths are another matter:
$N_{\mathrm{L}}(t, t - 3) = 2^{t-3}$ for $t \le 21$ ([the exponential width](exponential-left-width.md)), far above the rank.

**What would change this.** Nothing for $a = t - 3$; for the rank at smaller $a$, a proof that the words of $W_T$ give
$\rho(a)$ independent columns while $|W_T| \ge \rho(a)$, which the table supports for $a \le t - 5$ at $t \le 19$.

**Reproduce.**

```bash
python -m computations.letter_words --rank 14 20     # the ranks and N_L at a = t - 8 .. t - 2 (minutes)
python -m computations.letter_words --count 16       # |W_T| for T <= 16 (2 min with 4 threads; 512 MB at T = 16)
python -m computations.letter_words --forbid 12 --entropy 13   # forbidden words and radii (about 1 min)
```
