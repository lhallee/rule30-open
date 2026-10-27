---
title: Transformers do not predict the next cell
category: learned-models
problems: [3]
status: negative
kind: no-signal
---

# Transformers do not predict the next cell

**Question.** Can a sequence model learn a shortcut for the center column that generalizes in time? A model below 0.95
bits per cell on held-out cells would have been a lead for a negative answer to Problem 3.

**Setup.** Decoder-only transformers (RoPE, RMSNorm, bf16) of 4.1M, 16.0M and 64.1M parameters, contexts of 1,024 and
4,096 tokens, with byte tokens (8 cells) or cell tokens, trained on the first 80% of $2^{22}$ cells, early-stopped on
the next 10%, scored on the last 10%. Same controls as [the compression test](../statistics/compression.md), plus two
linear feedback shift registers, of 31 and 1,279 cells.

**Outcome.** The center column scores 1.0003 to 1.0014 bits per cell with byte tokens and 1.0000 with cell tokens,
never near the 0.95 bar. The excess above 1 grows with model size (fitting noise) and is flat across the test split.
The same models take Rudin-Shapiro, Rule 90's and Rule 150's column 1 and a 32-state automaton below 0.001 (one
Rudin-Shapiro run stalled at 0.125, the floor its byte tokens give for free), and learn the 31-cell register's
recurrence at context 1,024. They do not learn the 1,279-cell register, whose two-tap recurrence
lies inside every context.

**What it means.** Short-range structure as learnable as the controls is absent. The 1,279-cell register shows the
limit: a dependency of that kind would also go unseen, which is why the
[Berlekamp-Massey test](../complexity/linear-complexity.md) excludes the linear ones exactly.

**Evidence.** Quoted from training code and run logs that are not in this repository.
