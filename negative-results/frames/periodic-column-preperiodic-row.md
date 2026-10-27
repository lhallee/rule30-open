---
title: A periodic column does not force a periodic row
category: frames
problems: [1]
status: negative
kind: refuted
evidence: [computations/backgrounds.py]
---

# A periodic column does not force a periodic row

**Conjecture tried.** In the right-edge frame, Rule 30 is the bijection $\Phi(y) = y \oplus (2y \lor 4y)$ of the
2-adic integers, and a row is rational when it is eventually periodic to the left. A natural hope for Problem 1 was
that a row whose column is eventually periodic must have an eventually periodic orbit in the frame (be
$\Phi$-preperiodic). The finite rows are not $\Phi$-preperiodic, since their width grows by two cells a step, so the
conjecture would have excluded every eventually periodic column of a finite row.

**Refuted.** The ether backgrounds ([periodic backgrounds](../../findings/frames/periodic-backgrounds.md)) have an
eventually periodic column, of period 4 or 8, while their orbit is not preperiodic: the part of $\Phi^n(y)$ before its
periodic tail keeps growing, 53 cells after 50 steps, 103 after 100 and 205 after 200 for the background
$(0000001)^\infty$. The column is held periodic by the ether's boundary layer while the rest of the row keeps changing.

**What survives.** Problem 1 still says exactly that $\Psi(1)$ is irrational
([the 2-adic trace](../../findings/frames/two-adic-trace.md)), but a proof cannot go through orbit periodicity in the
frame.

**Reproduce.** `prefix_growth` in [computations/backgrounds.py](../../computations/backgrounds.py), printed by
`python -m computations.backgrounds 9 2 2048`.
