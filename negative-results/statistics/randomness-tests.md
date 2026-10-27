---
title: The center column passes every randomness test tried
category: statistics
problems: [2, 3]
status: negative
kind: no-signal
---

# The center column passes every randomness test tried

**Question.** Does the center column deviate from a fair coin anywhere a test can see, in a way that could point to a
proof of Problem 2 (density 1/2) or to structure for Problem 3?

**Tests and outcomes**, on the first $2^{22}$ cells unless stated, with a ChaCha20 keystream as the reference:

| Statistic | Center column | ChaCha20 |
|---|---:|---:|
| Density of black cells | 0.500169 | 0.499968 |
| Final standard score of the running density | 0.69 | -0.13 |
| Largest standard score after $t = 1{,}000$ | 2.65 | 2.19 |
| Largest autocorrelation, lags 1 to 4,096 | 0.0018 | 0.0020 |
| Lags beyond $3/\sqrt{n}$ (about 11 expected) | 15 | 6 |
| Largest periodogram ordinate over the mean, first $2^{20}$ cells (1% point 17.8) | 12.9 | 14.4 |

- Agreement of $c(t)$ with $c(t + \ell)$ stays within 0.001 of 1/2 for every lag $\ell \le 2^{19}$, over $10^6$ cells.
- Correlation with the Thue-Morse, Rudin-Shapiro, period-doubling and paperfolding sequences, shifted by up to 8, is at
  most 0.0024 in absolute value over $2^{20}$ cells; $c(2t)$ and $c(2t + 1)$ against $c(t)$, at most 0.003.
- Black counts on dyadic blocks and the counts of $c(t) \ne c(t + 2^k)$, $k \le 19$, are all within 2.3 standard
  deviations of half.
- Parities of the black counts of row $t$ on position classes modulo $2^k$ ($k \le 4$, $t < 4{,}000$), and rows read
  as integers modulo 3, 5, ..., 255 and modulo 65,537: no eventual period up to a quarter of the range, agreement with
  $c$ about 1/2, residues consistent with uniform.
- Sparse samplings that an eventual period would make regular: $c(k!)$ would be eventually constant and $c(2^k)$
  eventually periodic. Neither, nor $c(2^k \pm 1)$, $c(3 \cdot 2^k)$, $c(5 \cdot 2^k)$ or the prefix black count at
  $2^k$ modulo 2, 4 and 8, shows a pattern for $k \le 20$.

**What it means.** The column looks like ChaCha20 to every test here. That is evidence consistent with Problem 2, not a
proof, and it says nothing about cells beyond the range tested.

**Evidence.** Quoted from code that is not in this repository; the $2^{22}$ cells agree with all 100,001 terms of the OEIS b-file of
[A051023](https://oeis.org/A051023). [computations/rule30.py](../../computations/rule30.py) generates the column.
