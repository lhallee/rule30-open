---
title: Counts of black cells move left by at most a factor of three
category: columns
problems: [2]
status: proved
lean: Rule30Open.Columns.ColumnTransfer
headline: [transfer, transfer_white, iterate, transfer_right, transfer_right_white, iterate_right, center_lower]
kit: new
kit_modules: [Rule30Jen, Rule30MaskedJen]
---

# Counts of black cells move left by at most a factor of three

Write $N_i(n)$ for the number of black cells of column $i$ of the single-cell orbit at the times $0, \ldots, n - 1$,
and $W_i(n) = n - N_i(n)$ for the white ones.

## Statement

For every column $i$ and all $n, k \ge 0$:

- `transfer`: $N_{i-1}(n) \le N_i(n + 1) + N_i(n) + N_{i+1}(n)$.
- `transfer_white`: $N_{i-1}(n) \le W_i(n + 1) + W_i(n) + W_{i+1}(n)$.
- `iterate`: $N_{-k}(n) + N_{-k+1}(n) \le 3^k \left(N_0(n + k) + N_1(n + k)\right)$.
- `transfer_right`: $N_{i+1}(n) \le N_{i-1}(n) + N_i(n + 1)$, and `transfer_right_white`: $N_{i+1}(n) \le
  W_{i-1}(n) + W_i(n + 1)$.
- `iterate_right`: $N_k(n) + N_{k+1}(n) \le 2^k \left(N_0(n + k) + N_1(n + k)\right)$.
- `center_lower`: $N_1(n) \le N_{-1}(n) + N_0(n + 1)$, that is, $N_0(n + 1) \ge N_1(n) - N_{-1}(n)$.

## Argument

Rule 30 is left permutive (`Rule30Jen.cell_left`): cell $(t, i - 1)$ is $c(t + 1, i) \oplus (c(t, i) \lor c(t, i + 1))$.
If it is black, one of the three cells $(t + 1, i)$, $(t, i)$, $(t, i + 1)$ is black, since otherwise the sum is 0;
and one of them is white, since if all three are black the sum is 0 again. Summing these pointwise bounds over $t < n$
gives the two transfers, with $\sum_{t < n} c(t + 1, i) \le N_i(n + 1)$. The iterated form applies `transfer` at $i = -k$, which
bounds column $-k - 1$ by columns $-k$ and $-k + 1$, and uses that $N$ grows with $n$, so $S_{k+1}(n) \le 3 S_k(n + 1)$ for $S_k$ the left side.
Read the other way, if cell $(t, i + 1)$ is black the `or` is 1, so exactly one of $(t, i - 1)$ and $(t + 1, i)$ is
black and exactly one is white; summing gives the rightward forms, which iterate with factor 2.

## What it means

In densities, with $\bar d$ an upper and $\underline d$ a lower density of black cells:
$\bar d_{i-1} \le 2 \bar d_i + \bar d_{i+1}$ and $\bar d_{i-1} \le 2(1 - \underline d_i) + (1 - \underline d_{i+1})$.
So if columns 0 and 1 both had black density 0, every column left of the center would too, and if two adjacent
columns both had black density 1, the column to their left would have black density 0. The hypotheses are not known
to fail, since Problem 2 is open, and none of these gives a positive lower density for the center column.

The pointwise steps are the kit's (`Rule30MaskedJen.left_of_black`, `left_of_white`); the kit and the repository have
no inequality between counts of black cells in different columns, so the summed form is new, and modest.
