---
title: As a function of the digits of n, the center cell has the algebraic normal form and the Fourier and mod-3 spectra of a random function
category: complexity
problems: [3]
status: negative
kind: no-signal
evidence: [computations/index_spectrum.py, tests/test_index_spectrum.py]
---

# As a function of the digits of n, the center cell has the algebraic normal form and the Fourier and mod-3 spectra of a random function

**Question.** Let $g_L(n) = c(n)$ for $1 \le n < 2^L$ and $g_L(0) = 0$, a Boolean function of the $L$ binary digits of
$n$. A shortcut of Problem 3 in a restricted circuit model would show in this function: a polynomial over GF(2) with
few monomials would be a fast GF(2) formula; a large correlation with a parity of some digits is what small
$\mathrm{AC}^0$ circuits have (their Fourier spectrum is concentrated on small sets, by Linial, Mansour and Nisan), and
the residue modulo 3 of a sum of digits is the statistic that the polynomial approximations of Razborov and Smolensky
work with. These are heuristic markers of structure, not tests that a given circuit class must pass. Do any of them
depart from a uniformly random function of $L$ bits?
(Rule 90's column is white after time 0, so its $g_L$ is 0, with an empty normal form; that comparison is trivial and
says nothing about difficulty.)

**Method.** Exhaustive, over all $2^L$ inputs and all sets $S$ of digits. Monomials and degree come from the Moebius
transform. The Walsh bias is $\max_{S \ne \emptyset} |E_n (-1)^{g(n) + \sum_{i \in S} n_i}|$. The mod-3 bias is
$\max_{S \ne \emptyset, r} |E_n (-1)^{g(n)} (1[|n \wedge S| \equiv r \bmod 3] - 1/3)|$, from the transform with
kernel $\left(\begin{smallmatrix} 1 & 1 \\ 1 & \omega \end{smallmatrix}\right)$, $\omega = e^{2\pi i/3}$, which gives
$\sum_n (-1)^{g(n)} \omega^{|n \wedge S|}$ for every $S$ at once. The random columns are 20 uniformly random truth
tables of the same size (seed 0), and 10 at $L = 20$. The number of monomials of a uniformly random function has mean
$2^{L-1}$ and standard deviation $2^{L/2 - 1}$ (each coefficient is an independent fair bit), 512 at $L = 20$.

**Outcome.**

| $L$ | monomials of $g_L$ | $2^{L-1}$ | random: mean (sd) | degree | Walsh bias | random mean, max | mod-3 bias | random mean, max |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 8 | 125 | 128 | 128.7 (7.6) | 7 | 0.156 | 0.189, 0.234 | 0.094 | 0.097, 0.128 |
| 10 | 524 | 512 | 511.4 (10.0) | 10 | 0.111 | 0.111, 0.135 | 0.074 | 0.055, 0.076 |
| 12 | 2,039 | 2,048 | 2,039.8 (29.2) | 12 | 0.060 | 0.060, 0.067 | 0.031 | 0.029, 0.034 |
| 14 | 8,194 | 8,192 | 8,188.6 (66.3) | 13 | 0.034 | 0.032, 0.038 | 0.016 | 0.017, 0.019 |
| 16 | 32,879 | 32,768 | 32,785.6 (142.6) | 15 | 0.0169 | 0.0173, 0.0193 | 0.0083 | 0.0085, 0.0092 |
| 18 | 131,364 | 131,072 | 131,145.5 (256.5) | 17 | 0.0095 | 0.0092, 0.0104 | 0.0047 | 0.0046, 0.0055 |
| 20 | 524,535 | 524,288 | 524,055.0 (378.9) | 20 | 0.0048 | 0.0050, 0.0054 | 0.0023 | 0.0024, 0.0026 |

At $L = 16$ the monomials by degree are 0, 11, 58, 277, 899, 2,148, 4,068, 5,753, 6,536, 5,683, 4,047, 2,154, 879, 302,
60, 4, 0 for degrees 0 to 16, against $\binom{16}{d}/2$: 0, 8, 60, 280, 910, 2,184, 4,004, 5,720, 6,435, 5,720, 4,004,
2,184, 910, 280, 60, 8, 0. The degree is $L$ exactly when the number of black cells in $[1, 2^L)$ is odd, which the
coefficient of the top monomial counts.

Controls at $L = 20$, each found at once: Thue-Morse (a parity of all digits) has Walsh bias 1, Rudin-Shapiro has 19
monomials of degree at most 2, and the indicator of $\mathrm{popcount}(n) \equiv 0 \pmod 3$ has mod-3 bias 0.444.

**What it means.** On these ranges $g_L$ is indistinguishable from a random function by all three measures: its normal
form has about $2^{L-1}$ monomials spread over the degrees as for a random function, so no sparse GF(2) polynomial
computes it, and no parity of digits and no residue modulo 3 of a sum of digits correlates with it beyond the random
scale of about $2^{-L/2} \sqrt{2 L \ln 2}$, the largest of $2^L$ Gaussian correlations. Each of these is a statement
about $L \le 20$: for a fixed $L$, any function of $L$ bits has a circuit of size $O(2^L / L)$, and the asymptotic
question, whether the bias decays like $2^{-\Omega(L)}$, is a circuit lower bound for an explicit function that no
finite table settles. The tests extend the correlations with Thue-Morse and Rudin-Shapiro of [the randomness
tests](../statistics/randomness-tests.md) to every set of digits, the dense polynomials of [the polynomial
structure](../structure/polynomial-structure.md), which are polynomials in the cells of the cone, to polynomials in the
digits of the index, and the automaton bounds of [no small automaton](automaton-lower-bounds.md), which count the
distinct rows of the matrix $c(h 2^k + l)$ (the split of the digits between two players in communication complexity), to
measures that do not see a digit order. The kit proves in Lean that for almost every configuration the same function of
its column needs circuits of more than $2^L / (8L)$ gates for all large $L$ (`Circuits`); like that theorem, these
numbers do not reach the single cell's column at every $L$. The normal form, complemented because $g_L(0) = 0$, is the
binomial transform $\gamma$ of the column over GF(2), which has a period $2^m$ from $2^a$ exactly when $c$ has a period
$2^a$ from $2^m$ and is eventually periodic exactly when $c$ is ([BinomialDuality](../../Rule30Open/Complexity/BinomialDuality.md)).

**Reproduce.**

```bash
python -m computations.index_spectrum --bits 18 --random 20   # the table to L = 18 (about 15 s)
python -m computations.index_spectrum --bits 20 --random 10   # the row L = 20 and the controls (about 3 minutes)
```

[tests/test_index_spectrum.py](../../tests/test_index_spectrum.py) checks the three transforms against direct sums over
every set of digits on a random table of 6 bits, the controls, and the row $L = 10$ of the table.
