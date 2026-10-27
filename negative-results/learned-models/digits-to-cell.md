---
title: No model maps the digits of t to cell t
category: learned-models
problems: [3]
status: negative
kind: no-signal
---

# No model maps the digits of t to cell t

**Question.** Problem 3 asks how hard it is to compute $c(t)$ from $t$. Can a model read the digits of $t$ and output
$c(t)$ beyond its training range?

**Setup.** A GRU reading the digits most significant first, a bidirectional transformer reading them least significant
first, and an MLP on one-hot digits, in bases 2, 3 and 4. Extrapolation trains on $t < 2^{20}$ and tests on
$2^{20} \le t < 2^{22}$ (3,145,728 cells; chance has a standard deviation of 0.0003); interpolation uses a random
80/20 split. Class-balanced loss, three seeds for the GRU in base 2.

**Outcome.** Balanced accuracy on the center column is 0.4992 to 0.5004 in all seven configurations and three seeds,
against a bar of 0.55; the GRU cannot even fit its training cells (training accuracy 0.499 to 0.502). On the controls
the same models extrapolate an 8-state automaton (0.96), part of a 32-state one (0.84), and fit all three random
automata when interpolating. Both linear feedback shift registers stay at chance, although each has an $O(\log t)$
formula for cell $t$.

**What it means.** Excluded: automata small enough for these learners, about 32 states; the exact search in
[the automaton bounds](../complexity/automaton-lower-bounds.md) goes much further. Not excluded: arithmetic shortcuts,
which these learners miss even on the registers. A learner that recovers both registers from the digits of $t$, for
instance one biased toward polynomial arithmetic over GF(2), would be needed to make this negative conclusive.

**Evidence.** Quoted from training code and run logs that are not in this repository.
