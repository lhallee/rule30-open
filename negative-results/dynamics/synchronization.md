---
title: Driven halves never synchronize
category: dynamics
problems: [1]
status: negative
kind: no-signal
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
  ([`Rule30TraceEdge`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/7d665044b904117af9e82328aeb90a30692b2b85/lean/Ruliology/CellularAutomata/Rule30TraceEdge.lean)).

**What it means.** The half next to a periodic center keeps information about its start indefinitely, so no reduction
to one universal system per word is available.

**Evidence.** Quoted from code that is not in this repository.
