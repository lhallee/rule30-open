---
title: To depth 200,000 the settled words of the left diagonals look like fair words of their period; every word of period 16 occurs up to rotation, the longest white runs follow the longest-run law of fair words, and the largest white run W_j stays below log2 j + 6
category: diagonals
problems: [2]
status: computed
formalization: not-applicable
evidence: [computations/settled_words.py]
---

# To depth 200,000 the settled words of the left diagonals look like fair words of their period; every word of period 16 occurs up to rotation, the longest white runs follow the longest-run law of fair words, and the largest white run W_j stays below log2 j + 6

The left diagonals $D_j(t) = \mathrm{cell}(t, j - t)$ of the single cell repeat from their onsets. The *settled word*
of $D_j$ is one period of it, read from a common time after every onset, so that the words of different depths are
aligned; $P_j$ is its least period, $g_j$ and $b_j$ its longest cyclic white and black runs, and
$W_j = \max(g_1, \dots, g_j)$ over the diagonals that are not white. The one-step cost of a seed is $c_n = g_n + 1$, and
no finite certificate bounds the seed onsets at every depth unless the white runs are controlled
([seed finite certificate](../../negative-results/diagonals/seed-finite-certificate.md)). This entry describes the
words and their white runs.

## The words follow a bijection from one white diagonal to the next (paper)

On aligned words of a common period $P$, the next word $C = D_{j+2}$ is a function of $A = D_j$ and $B = D_{j+1}$
whenever $B$ is not white: $C(t+1) = \lnot A(t)$ at every black cell $t$ of $B$, and
$C(t+1) = A(t) \oplus C(t)$ elsewhere, so $C$ is the unique $P$-periodic solution (`D_periodic_of_black` of
[LeftMemory](../../Rule30Open/Diagonals/LeftMemory.md)). Conversely $A(t) = C(t+1) \oplus (B(t) \lor C(t))$. So the map
$F(A, B) = (B, C)$ is a bijection from the pairs whose second word is not white onto the pairs whose first word is not
white, and it commutes with rotations. A *regime* is the stretch of depths after a white diagonal $w$ up to the next
white diagonal $w'$: its pairs run along $F$ from the pair $(D_w, D_{w+1})$, whose first word is white and which
therefore has no preimage, to $(D_{w'-1}, D_{w'})$, whose second word is white. A path of an injective map from a point
without a preimage never returns, so the pairs of a regime are distinct up to rotation. Across a white diagonal,
$D_{w'+1}$ accumulates $D_{w'-1}$ (`D_shift_of_white`): with odd weight the period doubles and the new word is
anti-periodic, with even weight it is fixed up to complement. That the depth acts injectively on pairs is the fact the
kit's main branch uses to prove the periods unbounded (`Rule30LeftUnbounded`); lead 3 of
[linear settling leads](../../negative-results/diagonals/linear-settling-leads.md) checks that no pair repeats up to a
time shift to depth 200,000. So between period doublings the sequence of settled words has an exact finite-state
description, the orbit of $F$ on the $4^P$ pairs of period $P$; the question below is whether it has a smaller one.

## The words by regime (computed, to depth 200,000)

`settled_words` reads the words from the last 256 rows of `settled_slope.stream` (300,600 steps, every onset at
least four periods before the end) and checks the pair map at every depth on words aligned at period 32: $F$ gives
$D_{j+2}$ at the 199,992 depths with $D_{j+1}$ not white, its inverse gives $D_j$ at all 199,999, and the 7 others are
the white diagonals.

| Regime | Period | Depths | Words up to rotation | Pairs up to rotation | Largest $g$ | Words with one black cell | Anti-periodic (fair words) |
|---|---:|---:|---:|---:|---:|---:|---:|
| 8 to 28 | 4 | 21 | 6 | 20 | 3 | 3 | 9 (5.2) |
| 29 to 399 | 8 | 371 | 36 | 370 | 7 | 9 | 18 (23.2) |
| 400 to 53,207 | 16 | 52,808 | 4,116 | 52,807 | 15 | 11 | 182 (206.3) |
| 53,208 to 58,286 | 16 | 5,079 | 2,917 | 5,078 | 15 | 2 | 13 (19.8) |
| 58,287 to 87,866 | 16 | 29,580 | 4,114 | 29,579 | 15 | 4 | 100 (115.5) |
| 87,867 to 200,000 | 32 | 112,134 | 112,085 | 112,133 | 23 | 0 | 6 (1.7) |

- **Every word occurs.** The words of length 16 fall into 4,116 classes up to rotation, and the regime 400 to 53,207
  meets all of them (the regime 58,287 to 87,866 meets 4,114). The counts of the classes, against fair words of 16
  bits (a class of $s$ rotations has probability $s/2^{16}$), give chi-square 3,940.5, 4,101.7 and 4,136.9 on 4,115
  degrees of freedom in the three regimes of period 16 ($z = -1.92$, $-0.15$, $+0.24$). In the regime of period 32,
  112,134 words fall into 112,085 classes; fair words would give about 46.8 coincidences among the about $2^{32}/32$ classes,
  and 49 are seen.
- **Anti-periodic words.** The last column counts the words $w$ of the regime's period $P$ with
  $w(t + P/2) = \lnot w(t)$; a fair word of $P$ bits is one with probability $2^{-P/2}$. In the three regimes of
  period 16 the counts are below the fair numbers, by 1.4 to 1.7 standard deviations each (Poisson) and by 2.5 together
  (295 against 341.6), and at period 8 they are 18 against 23.2. The excess at periods 4 and 32 includes the twin
  anti-periodic diagonals $w + 1$ and $w + 3$ that follow each doubling at a white diagonal $w$ (8 and 10, 87,867 and
  87,869; the kit's main branch, `Rule30LeftAntiPeriod.D_twin_antiperiodic_of_not_evPer`).
- **Weights.** In the regimes of period 16 the weights of consecutive words are uncorrelated ($|r| \le 0.0024$) and
  those two depths apart have correlation $-0.489$ to $-0.503$. That is what the step gives if the words were fair (a heuristic): where
  $D_{j+1} \lor D_{j+2}$ is black, about three times in four, $D_{j+2}$ copies the complement of $D_j$ one step later,
  and elsewhere $D_j$ itself, so the covariance is $(1/4 - 3/4)$ times the variance.

So, to depth 200,000, no statistic computed here departs from fair words of their period by more than about 2.5
standard deviations, beyond what the step itself forces; the largest departure is the deficit of anti-periodic
words at period 16. A fixed substitution or a small automaton that produced the sequence of words up to
rotation would have to produce every class of period 16 within one regime, with fair-word frequencies; none is visible,
and the exact description is the orbit of $F$.

## The white runs follow the longest-run law of fair words (computed)

`run_law` counts exactly the words of $P$ bits by their longest cyclic white run (checked against enumeration for
$P \le 12$). Grouped by the common period of the regime, observed against expected for fair words with a black cell:

| $g$ | 1 | 2 | 3 | 4 | 5 | 6 | 8 | 10 | 12 | 14 | 15 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Period 16, observed | 2,935 | 20,056 | 25,524 | 17,750 | 10,348 | 5,469 | 1,305 | 371 | 77 | 24 | 17 |
| Period 16, expected | 2,944.2 | 19,949.8 | 25,576.6 | 17,979.9 | 10,207.1 | 5,349.1 | 1,366.6 | 341.7 | 85.4 | 21.4 | 21.4 |

| $g$ | 2 | 4 | 6 | 8 | 10 | 12 | 14 | 16 | 18 | 20 | 21 | 22 | 23 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Period 32, observed | 7,619 | 30,153 | 12,454 | 3,456 | 856 | 234 | 56 | 9 | 8 | 0 | 1 | 1 | 1 |
| Period 32, expected | 7,556.3 | 30,288.2 | 12,442.7 | 3,423.9 | 872.3 | 218.9 | 54.7 | 13.7 | 3.4 | 0.9 | 0.4 | 0.2 | 0.1 |

The tail halves with each step of $g$, as for fair words, up to the cap $g \le P - 1$: the 17 diagonals of period 16
with $g = 15$ are the words with one black cell, whose fair-word number is $16 \cdot 87{,}464 / 2^{16} = 21.4$.

**Records of $W_j$.** `max_run_quantiles` gives the law of $W_j$ when each settled diagonal $i \le j$ is an
independent fair word of its regime's period with a black cell (a heuristic model, not a property of the pattern).

| $j$ | 11 | 63 | 407 | 659 | 100,304 | 128,458 | 165,474 | 200,000 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| $W_j$ | 3 | 7 | 10 | 15 | 19 | 22 | 23 | 23 |
| Period of the regime | 4 | 8 | 16 | 16 | 32 | 32 | 32 | 32 |
| $\log_2 j$ | 3.46 | 5.98 | 8.67 | 9.36 | 16.61 | 16.97 | 17.34 | 17.61 |
| Model, 1% to 99% | 1 to 3 | 5 to 7 | 7 to 12 | 8 to 15 | 15 to 24 | 17 to 25 | 18 to 26 | 18 to 27 |

The table leaves out the records $W = 1, 2, 5, 6$ at $j = 3, 8, 35, 39$, whose bands are 0 to 1, 1 to 3, 3 to 7 and 3
to 7. Every record lies within the model's 1% to 99% band (at $j = 63$ and 659 at its top), and since $W_j$ grows only at its records,
$W_j - \log_2 j$ is largest at a record: **$W_j < \log_2 j + 6$ for every $1 \le j \le 200{,}000$** (the largest
difference is 5.66, at $j = 165{,}474$; the records are those of `white_records`).

**What the model says (heuristic).** For $N$ fair words of $P$ bits the largest white run is about
$\log_2(N P) - 1$, capped at $P - 1$. With $N \le j$ this makes $W_j$ at most about $\log_2 j + \log_2 P_j$, so
$W_j = O(\log j)$ as long as $\log P_j = O(\log j)$, which the heuristic of [left records](left-records.md) (the next
doubling near depth $2^{33}$) grants with room to spare. The proved bound is far weaker: a diagonal that is not white
has a black cell in every period, so $g_j \le P_j - 1$, and the kit's main branch bounds the period by
$2^{\lfloor (j + 5)/6 \rfloor}$ (`Rule30LeftAntiPeriod.D_evPer_pow_div_six`). The step moves white
runs between diagonals without shortening them ([RunTransfer](../../Rule30Open/Diagonals/RunTransfer.md)), which is why
no bound between $\log_2 P$ and $P - 1$ comes from it; the routes and where they stop are in
[white-run potential](../../negative-results/diagonals/white-run-potential.md).

## Reproduce

```bash
python -m computations.settled_words --depth 200000   # every table, about 3 min, 0.2 GB
```

`tests/test_settled_words.py` checks the words, rotations, runs and anti-periodicity against strings read from the
space-time diagram, the pair map against a scalar run, the longest-run law against enumeration, the model quantiles
against an enumeration of two words, the chi-square against string counts, and the run lemmas cell by cell on the rows.
