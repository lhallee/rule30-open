---
title: No compressor or Markov model beats one bit per cell
category: statistics
problems: [3]
status: negative
kind: no-signal
---

# No compressor or Markov model beats one bit per cell

**Question.** Is any short-range predictability in the center column visible to standard predictors?

**Setup.** The first $2^{22}$ cells, split in time: the first 80% to fit, the last 10% to score, in bits per cell.
Controls that a working pipeline must crack: Rudin-Shapiro, column 1 of Rules 90 and 150, random 2-automata with 8,
32 and 128 states. Controls it must not: a ChaCha20 keystream and the center column under a fixed permutation.

**Outcome.** Every predictor scores the center column at 1.0000 bits per cell: Markov models of orders 0 to 24, 28 and
32 (best 1.0000 at order 3), context-tree weighting at depths 8, 16 and 24, xz at `-9e` and zstd at `--ultra -22`.
The same predictors take Rudin-Shapiro to 0.0005 (zstd), Rule 150's column 1 to 0.0002, and the random automata to
0.0002 to 0.0011, and leave ChaCha20 and the shuffled column at 1.0000.

**What it means.** No short-range dependency of the kinds these models capture exists in the first $2^{22}$ cells. It
does not exclude long-range or arithmetic structure; see [the linear complexity](../complexity/linear-complexity.md)
and [the learned models](../learned-models/next-cell-transformers.md).

**Evidence.** Quoted from code that is not in this repository.
