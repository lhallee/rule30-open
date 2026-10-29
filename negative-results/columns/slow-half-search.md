---
title: A search for slow right halves finds no counterexample and misses the slowest halves
category: columns
problems: [1]
status: negative
kind: no-signal
evidence: [computations/slow_halves.py]
---

# A search for slow right halves finds no counterexample and misses the slowest halves

**Question.** Least period four for the center column comes down to attraction: every finite right half, driven by a
word of period four, enters the kit's ether-and-wall family ([the locking conjecture](../../findings/columns/period-four-locking.md)).
[The census](../../findings/columns/absorption-census.md) checks every half of up to 20 cells. Does a search find a
half of more cells that enters much later, or never, a candidate counterexample?

**Method.** A beam search over prefixes, driven from phase 0: all halves of 12 cells, then, at each length, the 512
halves that enter latest, each extended by one more cell, white or black, up to 64 cells, with entry searched for 8,000
steps. At 12 cells the beam holds every half, so its result there must equal the census, and it does.

**Outcome.** The latest entry found, by the number of cells:

| word | 12 (all halves) | 16 | 20 | 32 | 48 | 64 | census, 16 cells | census, 20 cells |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| $0001$ | 544 | 557 | 587 | 813 | 876 | 986 | 732 | 1,032 |
| $0011$ | 980 | 994 | 994 | 1,431 | 1,515 | 1,515 | 1,627 | 1,957 |
| $0111$ | 416 | 416 | 416 | 616 | 931 | 931 | 544 | 787 |

At 16 and 20 cells the beam reaches only 51% to 76% of the census maximum: the slowest halves of a length do not
extend the slowest halves of the length before. Up to 64 cells the search finds no half that enters later than 1,515
steps, and every half it tries enters. Several of its slowest halves carry a long alternating stretch, the stripe.

**What it means.** No counterexample to attraction appears, but the search is weak evidence: slow halves are rare and
give a search nothing to climb, so a search that extends prefixes misses them even where the census finds them. A hunt
beyond 20 cells needs exhaustive enumeration or a structural description of the slow halves, which is the third item
of the period-four lead in [the roadmap](../../ROADMAP.md#next-steps).

**Reproduce.**

```bash
python -m computations.slow_halves 0001 0011 0111 --beam 512 --start 12 --stop 64 --steps 8000
```

[computations/slow_halves.py](../../computations/slow_halves.py) runs in about 80 s; the census values are those of
[the census finding](../../findings/columns/absorption-census.md) at phase 0.
