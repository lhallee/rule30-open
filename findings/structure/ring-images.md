---
title: On a ring of W cells Rule 30 reaches all but (p_W + 1)/2 - [3 | W] rows, p_W the power sums of the roots of x³ - x² - 2, so one step loses about 0.85^W bits
category: structure
problems: [3]
status: paper
formalization: wanted
evidence: [computations/ring_images.py, tests/test_ring_images.py]
---

# On a ring of W cells Rule 30 reaches all but (p_W + 1)/2 - [3 | W] rows, p_W the power sums of the roots of x³ - x² - 2, so one step loses about 0.85^W bits

**Result.** Let $F_W$ be one step of Rule 30 on the $2^W$ rows of a ring of $W \ge 3$ cells (the rows of period $W$ of
the line). Let $p_W$ be the sum of the $W$-th powers of the three roots of $x^3 - x^2 - 2$: $p_1 = p_2 = 1$, $p_3 = 7$,
$p_W = p_{W-1} + 2 p_{W-3}$. Then the number of rows that $F_W$ does not reach is

$$m_W = \frac{p_W + 1}{2} - [3 \mid W],$$

so $|F_W(\{0,1\}^W)| = 2^W - m_W$ and one step loses $\delta_W = W - \log_2 |F_W(\{0,1\}^W)| = -\log_2(1 - m_W
2^{-W})$ bits. With $\rho \approx 1.69562$ the real root of $x^3 = x^2 + 2$, and the other two roots of modulus
$\sqrt{2/\rho} \approx 1.086$, $m_W = \rho^W/2 + O(1.09^W)$ and $\delta_W \sim (\rho/2)^W / (2 \ln 2)$, with
$\rho/2 \approx 0.8478$. Every row has at most three preimages, and exactly three occur only when $3 \mid W$.

| $W$ | 3 | 4 | 6 | 8 | 12 | 16 | 20 | 24 | 32 | 64 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| rows not reached, $m_W$ | 3 | 5 | 12 | 33 | 280 | 2,337 | 19,305 | 159,536 | 10,901,569 | $2.38 \cdot 10^{14}$ |
| loss of Rule 30, bits | 0.678 | 0.541 | 0.300 | 0.199 | 0.102 | 0.052 | 0.027 | 0.0138 | 0.0037 | $1.9 \cdot 10^{-5}$ |
| loss of Rule 90, bits | 1 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 |
| loss of Rule 150, bits | 2 | 0 | 2 | 0 | 2 | 0 | 0 | 2 | 0 | 0 |

The largest loss of Rule 30 is 0.678 bits, at $W = 3$; from $W = 13$ to 400 it stays below 0.088 bits. Rule 90 on a
ring is linear with a kernel of dimension 1 for odd $W$ (the two constant rows) and 2 for even $W$ (rows constant on
each parity class), so it loses 1 or 2 bits at every $W$. Rule 150 loses 2 bits when $3 \mid W$ and none otherwise, since its circulant $x^{-1} + 1 + x$ shares the factor
$x^2 + x + 1$ with $x^W - 1$ over GF(2) exactly when $3 \mid W$.

**Proof.** Rule 30 is left permutive: $x'_i = x_{i-1} \oplus (x_i \lor x_{i+1})$, so two rows with the same image that
agree on cells $i, i + 1$ agree on cell $i - 1$, and going left around the ring, everywhere. So for two distinct rows
$x \ne y$ with $F_W(x) = F_W(y)$, the pairs $(x_i, x_{i+1})$ and $(y_i, y_{i+1})$ differ at every $i$. Let $N_2$ be the
matrix on the 12 states $((a, b), (a', b'))$ with $(a, b) \ne (a', b')$, with an edge to $((b, c), (b', c'))$ when
Rule 30 gives the same cell over $b$ and $b'$ and $(b, c) \ne (b', c')$. The ordered pairs of distinct rows with the
same image are exactly the closed walks of length $W$ in it, so there are $\operatorname{tr} N_2^W$ of them, and in the
same way $\operatorname{tr} N_3^W$ ordered triples of pairwise distinct rows with one image, on the 24 states of three
pairwise distinct pairs. No row has more than three preimages: the kit proves it in Lean for every configuration of the
line (`Rule30Equivalents.Preimages.card_le_three`), and the rows of a ring are the configurations of period $W$. With
$n_k$ the number of rows with exactly $k$ preimages, $\operatorname{tr} N_2^W = 2 n_2 + 6 n_3$ and
$\operatorname{tr} N_3^W = 6 n_3$, and the rows not reached number $n_2 + 2 n_3 = \operatorname{tr} N_2^W / 2 -
\operatorname{tr} N_3^W / 6$. The characteristic polynomials, computed exactly, are $x^8 (x - 1)(x^3 - x^2 - 2)$ for
$N_2$ and $x^{18} (x^3 - 1)^2$ for $N_3$, so $\operatorname{tr} N_2^W = p_W + 1$ and $\operatorname{tr} N_3^W = 6 [3
\mid W]$ for every $W \ge 1$, which gives the formula. The three preimages when $3 \mid W$ are the three phases of
$(100)^{W/3}$, all mapped to the black row, as on the line (the kit's `exists_card_eq_three`).

The formula agrees with the enumeration of all $2^W$ rows for $3 \le W \le 24$, and so do the maximal numbers of
preimages. The proof is on paper; the kit's `card_le_three` is in Lean, and the count is not.

**What it means.** The step of Rule 30 on a ring is almost a bijection, the finite form of the kit's
`Mixing.ae_existsUnique_preimage` (almost every configuration of the line has exactly one preimage). The pairs of
distinct rows with one image are the branchings that the kit's `exists_ne_left_eq` exhibits on the line, and their
growth rate $\rho$ is that of the 12-state graph. Counting orphans on rings by transfer matrices is a standard method,
and the counts here are not claimed new to the literature on preimages; the closed form is computed here. The
consequence for a lower bound through erased information is in [the information lost on a
ring](../../negative-results/complexity/ring-information-loss.md).

**Reproduce.**

```bash
python -m computations.ring_images --max-width 24   # the table, both characteristic polynomials (about 15 s)
```

[tests/test_ring_images.py](../../tests/test_ring_images.py) checks the ring step against a cell-by-cell rule, the
formula and both traces against the enumeration of all rows for $W \le 14$, the characteristic polynomials and the
traces to $W = 40$, and the Rule 90 image sizes.
