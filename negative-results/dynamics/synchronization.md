---
title: Driven halves never synchronize
category: dynamics
problems: [1]
status: negative
kind: no-signal
evidence: [computations/defect_returns.py]
---

# Driven halves never synchronize

**Question.** Driven by the same center column, do two different halves converge? Synchronization would make the half
next to a periodic center a function of the drive alone, a finite-state object a proof could analyze.

**Outcomes.**

- **Left halves.** Two reachable left halves (the single cell's true prefix to step 300, then the true center versus
  random bits to step 600, then a periodic word in phase) never synchronize near the center: about half of depths 1 to
  100 differ at every checked time up to six times the run length. Driving left halves by one periodic word from
  different starts does not synchronize column $-1$ either. Left permutivity keeps differences alive and the OR
  spreads them.
- **Right halves.** Right halves driven by the same periodic word never synchronize and show no lag rigidity, except
  that column 1 locks under the three words of period 4
  ([the locking finding](../../findings/columns/period-four-locking.md)).
- **Near misses.** Long coincidences between two left halves under one center (agreeing for 144 and 202 steps) always
  separate again; none is a counterexample to the kit's open statement `EdgeObservable`
  ([`Rule30TraceEdge`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30TraceEdge.lean)).
- **The walled ether defect.** The defect on the ether of
  [the ether census](../../findings/period-two/ether-defect-census.md), beside the held 0 at cell $-1$, does not forget
  its bottom either. At all 28 alignments, take every defect on the cells $[0, 3 + T)$, step it $T$ times, and group
  the defects by their top 6 cells. From $T = 6$ on (3 or more free cells below the top word) no top word fixes the 3
  lowest cells of $D_T$, and from $T = 7$ on some top word leaves all 8 words of them possible. With a top word only 2
  cells short of the whole defect, some top word still leaves all 4 completions visible in the 3 lowest cells at every
  $T$ from 5 to 12, and between 16% and 25% of top words fix them; both counts are the same at all 28 alignments. A
  flip of cell 0 alone leaves the 3 lowest cells of $D_T$ unchanged for 28%, 43% and 50% of the defects at $T = 4$, 8
  and 12 (alignment 0, 0). Cell 0 beside the wall loses nothing either: the actual cell 0 follows
  $x_{t+1}(0) = x_t(0) \oplus x_t(1)$, so its old value is recovered from its new value and the old cell 1. So no
  number of steps up to 12 makes the bottom of the walled defect a function of its top, and entry into a closed strip
  does not reduce to a finite-state question about top words this way.

**What it means.** The half next to a periodic center keeps information about its start indefinitely, so no reduction
to one universal system per word is available.

**Evidence.** The left halves, right halves and near misses are quoted from code that is not in this repository. The
walled ether defect is `python -m computations.defect_returns forget --cells 3 --steps 12` (about a second), and
`tests/test_defect_returns.py` checks its bottom words against direct runs of `defect_potential.defect_step` and the
rule for cell 0 on every defect of 6 cells at two alignments.
