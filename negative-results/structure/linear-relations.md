---
title: No linear relation among subsequences of the center column
category: structure
problems: [1, 3]
status: negative
kind: no-signal
---

# No linear relation among subsequences of the center column

**Question.** Does the center column satisfy an exact identity linking cells at related indices, such as
$c(2t)$ and $c(t)$, or $c(t)$ and another column, that could give a shortcut (Problem 3) or a recursive structure
(Problem 1)?

**Outcomes.**

- **Affine index maps.** No GF(2) linear identity among $c(an + b)$ for $a \le 12$ and $b < 40$: rank 480 of 480 on
  1,200 samples. Given the window $c(n-6), \dots, c(n+6)$, the cell $c(mn + r)$ for $m = 2, 3, 4$ has conditional
  entropy 1 bit up to the finite-sample bias.
- **Nonlinear index maps.** Relations among $c$ at 106 maps of the index ($2t$, $t/2$, $3t$, XOR with $2^j$, the Gray
  code, bit reversal, $t \pm$ lowest set bit, $\lfloor t\varphi \rfloor$ and others) have full rank, except the
  identity $t \oplus 2^{15} = t - 2^{15}$ on the indices where it holds.
- **Copies in other patterns.** Over every elementary rule, the seeds 1, 11, 101, 111, 1001 and 1101, columns within 12
  of the center and time shifts up to 6, the only exact copies of $c$ are Rule 30's own symmetry images and seeds that
  differ right of the center, which [the seed extensions](../../Rule30Open/Seeds/SeedExtensions.md) explain.
- **Other columns.** No other column of the pattern, shifted in time, tracks $c$ beyond light-cone correlations
  (columns within 64, offsets within 300, 40,000 steps): only the right diagonal through each cell deviates from 1/2.
- **Arithmetic sequences.** Thue-Morse, Rudin-Shapiro, paperfolding, Beatty sequences, Legendre symbols, the parity of
  integer square roots and digit statistics correlate with $c$ only at the random scale.
- **Right diagonals.** No exact relation $R(aj + b, cs + d) = R(j + e, s + f)$ among the right edge's diagonals.

**What it means.** Nothing ties cells of the column together except the rule itself. The kit's equivalent forms prove
in Lean that Problem 1 itself is the absence of linear relations of one kind, over any field: no nonzero polynomial
times the generating function is a polynomial, and no linear recurrence holds
([`LinearRelations`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/equivalents/Rule30Equivalents/LinearRelations.lean)).

**Evidence.** Quoted from code that is not in this repository.
