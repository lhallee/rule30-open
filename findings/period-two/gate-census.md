---
title: Beside an alternating center every right half of up to 20 cells enters a gap trap, the kit's ether family or a lock of period seven
category: period-two
problems: [1]
status: computed
formalization: partial
evidence: [computations/gate_census.py]
---

# Beside an alternating center every right half of up to 20 cells enters a gap trap, the kit's ether family or a lock of period seven

Drive a finite right half with a center that alternates, in either phase. Every right half of up to 20 cells enters,
within 4,190 steps, one of three sets of windows that the rule never leaves, whatever the cells beyond the window do:

1. **the gap trap**, a closed set of windows of columns 1 to 16 on which the black cells of column 1, at the white
   steps of the center, come 3 or 5 white steps apart: the setting of the kit's open `Q01Gap`;
2. **the kit's ether-and-wall family** for the word $0101$, on which column 1 is periodic;
3. **a lock of period seven**, 195 windows of columns 1 to 32 on which column 1 repeats $0101000$ at the white steps,
   new here, with its exclusion in Lean ([SevenLock](../../Rule30Open/PeriodTwo/SevenLock.md)).

Halves that enter the family or the lock leave column 1 periodic, and then no finite left half keeps the center
alternating against them: period two is excluded outright, whatever the left half. Halves that enter the gap trap
are excluded by the kit's open `Q01Gap`. So **`Q01Gap` alone excludes every finite configuration whose right half,
at a step from which its center alternates, has at most 20 cells**, and period two splits into a statement about the
right half (every finite right half enters one of the three sets) and one about the left half (`Q01Gap`).

## The census

Every integer below $2^n$ is a right half, bit $i$ the cell $i + 1$. Phase 0 has the center black at the even steps
(the kit's `altCol`), phase 1 at the odd steps. The census follows each half for 8,000 steps and records the first
white step at which its window enters the gap trap or the lock; for the halves that enter neither it then runs the
ether-family check of `computations.absorption`.

| cells | phase | gap trap (latest entry) | lock (latest) | kit's family (latest) | none |
|---:|---:|---:|---:|---:|---:|
| 16 | 0 | 63,227 (3,341) | 561 (2,047) | 1,748 (126) | 0 |
| 16 | 1 | 63,046 (2,704) | 577 (2,170) | 1,913 (155) | 0 |
| 18 | 0 | 253,407 (3,341) | 1,989 (2,763) | 6,748 (245) | 0 |
| 18 | 1 | 252,465 (3,340) | 2,114 (2,746) | 7,565 (231) | 0 |
| 20 | 0 | 1,014,274 (4,189) | 7,440 (2,763) | 26,862 (255) | 0 |
| 20 | 1 | 1,010,422 (4,190) | 7,997 (2,762) | 30,157 (254) | 0 |

About 96.2% to 96.7% of the halves enter the gap trap, 2.6% to 2.9% the kit's family and 0.7% to 0.9% the lock.
The three are disjoint as destinations: on the gap trap column 1 has no gap of 2 between black cells, on the family it
alternates, and on the lock it repeats $0101000$, so a half that enters one never enters another. A finite set of
windows does not replace the family: the halves that lock into alternation do so with time-periodic zones of 6, 13
and 20 columns beside the center (the halves 11111, 0000110111 and 00001110000110111, cell 1 first, in
`python -m computations.gate_census zones`), ether units of seven columns, which the kit's family describes with any
number of units.

## The three sets

- **The gap trap** (`gap_states`, `gap_entry`) is computed, not copied: the greatest set of pairs of a window of
  columns 1 to 16 and a count of white steps since the last black cell of column 1 that the double step keeps for all
  four values of column 17 at the two steps, such that the next black cell comes 3 or 5 white steps after the last.
  A half enters when its window is black in column 1 and good with a count of 0; from then on every gap is 3 or 5.
  It has 3,562 entry windows, and every one of the 829 windows of the kit's `Rule30GateTrap.trap` (on the kit's main
  branch, after the commit pinned here) is good for some count (`kit_trap_inside`, run on the codes of the kit's
  `Rule30Certificates/GateTrap.lean`), so a half in the kit's trap is in this one by its next black cell. The
  empty half enters at step 293, as in the kit (`u_empty_gaps`).
- **The kit's family** is `Rule30Ether.InFamily` for $0101$ with the alignments $(3, 0)$ and $(3, 2)$, as
  [the absorption route](../../negative-results/period-two/absorption-route.md) uses it; there, 3% of the halves
  enter it and the rest were left open. Here the rest is accounted for.
- **The lock** is the closure of the late windows of the half $0101001$ under every input, at width 32
  (`seven_lock`); [SevenLock](../../Rule30Open/PeriodTwo/SevenLock.md) checks it in the kernel and proves that a
  finite configuration with an alternating center never enters it.

## What it means

The kit reduces period two to `CQ01`, and for the right halves that enter its gate trap to `Q01Gap`, a statement
about finite left halves alone: none has free bits whose complement eventually has its black cells 3 or 5 apart.
The census shows that, for small right halves, nothing else is needed: every one of them either is excluded outright
or comes down to `Q01Gap`. As with the words of period four ([the absorption
census](../columns/absorption-census.md)), the statement that every finite right half enters one of the three sets is
open, and of the same kind as the problem: the far cells of the right half are chaotic and have to deliver the entry.
The census reaches 20 cells; the slowest entries, at steps 4,189 and 4,190, are into the gap trap.

`Q01Gap` is weaker than the kit's `Q01` only by the shape of the free bits, which still form a set of positive
entropy (sequences of the blocks $001$ and $00001$), so it inherits the difficulty of `Q01`: the left half has to
absorb a positive rate of information.

## Reproduce

```bash
python -m computations.gate_census census --cells 16 --steps 8000   # about 30 s
python -m computations.gate_census census --cells 18 --steps 8000   # about 2 min
python -m computations.gate_census census --cells 20 --steps 8000   # about 15 min
python -m computations.gate_census lock
```

`tests/test_gate_census.py` checks the double step against direct runs of Python integers, the closure of the lock
and the word it forces, the example of the Lean file, the listing of the lock in the Lean file, the gaps of every half
of up to 8 cells that enters the gap trap in a direct run, and the census of halves of up to 6 cells.
