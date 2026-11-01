---
title: The single cell's pattern has no periodic domains of short spatial period, so it has no ether walls whose slopes or holonomy could be read
category: structure
problems: [1]
status: negative
kind: no-signal
evidence: [computations/pattern_domains.py]
---

# The single cell's pattern has no periodic domains of short spatial period, so it has no ether walls whose slopes or holonomy could be read

**Idea.** Two proposals start from walls between phases of the ether in the single cell's own pattern. One codes a
wall by its cutting sequence against the ether's lattice: a wall of irrational slope cuts an aperiodic word, and an
eventually periodic center column should force the walls' words to be eventually periodic and their slopes rational.
The other gives each cell its ether phase and reads the walls as a cochain, and asks for the holonomy of the phase
around rectangles with one side on the center column, which an eventual period would make trivial. Both need the
pattern to be a patchwork of ether domains separated by walls. The first test is the classification itself.

**Test.** A background of Rule 30 that recurs, $F^k x = \sigma^d x$ with $1 - k \le d \le k$, is periodic in space
(the kit's `Rule30Equivalents.PeriodicPoints`, `recurs_add_factorial`), and the ether is one. So every row of a domain
of a recurring background repeats with the background's spatial period. Call a block of $L \times L$ cells a *domain
block* when each of its $L$ rows repeats across the block with one period $p \le p_{\max}$.
[computations/pattern_domains.py](../../computations/pattern_domains.py) counts the domain blocks that lie inside the
light cone of the single cell, by half, streaming the rows, and the same on a random row run with white beyond its
ends, away from them.

**Outcome.**

| Rows | Block | Periods | Left half | Right half | Random row (block starts) |
|---:|---:|---:|---:|---:|---:|
| 0 to 8,191 | 24 by 24 | 1 to 16 | 0 of 33,174,585 | 0 of 33,174,585 | 0 of 28,842,075 |
| 0 to 8,191 | 16 by 16 | 1 to 8 | 0 of 33,305,041 | 9 of 33,305,041 | 0 of 29,021,075 |
| 0 to 4,095 | 12 by 12 | 1 to 7 | 8 of 8,296,701 | 236 of 8,296,701 | 24 of 7,215,599 |
| 0 to 4,095 | 10 by 10 | 1 to 7 | 382 of 8,313,003 | 1,609 of 8,313,003 | 742 of 7,237,965 |

- No block of 24 by 24 cells in the light cone of the single cell, to row 8,191, has rows that repeat with a period of
  at most 16. The ether, of spatial period 7, would fill such blocks. A domain of a background of longer spatial
  period, such as the period-6 background of spatial period 84 in
  [space-time backgrounds](../../findings/columns/space-time-backgrounds.md), is outside this test.
- The few domain blocks of 16 by 16 cells, all 9 of them, sit within 64 cells of the right edge, at rows 4,102 to
  4,104. At 12 by 12 cells, 186 of the 236 in the right half do too, all at rows $t$ with $t \bmod 256$ between 2 and
  8, all repeating with period 6: short patches next to the right edge at times just past a multiple of 256. They last
  a few rows and separate nothing. That they come at these times fits the kit's `Rule30Equivalents.Odometer`, in
  which cell $j$ from the right edge has a period dividing $2^j$ in time (a heuristic link, not a derivation).
- Away from the edges the pattern has domain blocks at the rate of a random row: at 12 by 12 cells, 58 of the 16.6
  million block starts of both halves lie 64 or more cells from an edge, $3.5 \times 10^{-6}$ against $3.3 \times
  10^{-6}$ for the random row; at 10 by 10 cells, 1,354 of 16.6 million, $8.1 \times 10^{-5}$ against $1.0 \times
  10^{-4}$.

So there are no domains of spatial period at most 16 for walls to separate, the classification step of both proposals has nothing to classify, and
no wall speed can be measured. The ether and its walls are objects of driven right halves, where the column is held
to a block ([space-time backgrounds](../../findings/columns/space-time-backgrounds.md),
[EtherDomain](../../Rule30Open/Columns/EtherDomain.md)), not of the single cell's pattern; beside an alternating
center the locked layer is neither the stripe nor the ether ([slip geometry](../../findings/period-two/slip-geometry.md)),
and the left half under that center is not a patchwork of ether domains
([ether patchwork](../period-two/ether-patchwork.md)).

**The rational branch.** An exactly periodic wall of rational slope cannot occur in a configuration that recurs at a
slower-than-light velocity, since such a configuration is spatially periodic (the kit, above). The same leftward
reconstruction works on a right half driven by any column (an argument, not in Lean): if the cells $h(i)$, $i \ge 1$,
satisfy $F^k h(i) = h(i + d)$ for every $i \ge k + 1$ with $1 - k \le d \le k$, then $h(j - 1)$ is fixed by $h(j),
\dots, h(j + 2k - 1)$ for $j \ge 2$, since cell $j - 1 + k$ after $k$ steps reads cells $j - 1, \dots, j - 1 + 2k$
only, none of them the driving column, and depends on cell $j - 1$ through an exclusive or; two equal windows among
any $4^k + 1$ adjacent ones then make $h$ spatially periodic on all of $i \ge 1$, with a period dividing $(4^k)!$. So
a right half that comes back to itself shifted, at such a velocity, holds no wall at all. The right half of the single
cell never comes back to itself (Kopra's theorem, the kit's `Rule30Equivalents.RightHalfReturns`), and its right edge
moves at the speed of light, outside this range.

**What it means.** Cutting sequences and holonomy of ether walls need walls, and the single cell's pattern shows
none at any scale tested, near the center column or away from it. A proof along these lines would have to produce the
walls from the hypothesis of an eventual period, which is the open step of the trap route in [the
roadmap](../../ROADMAP.md).

**Reproduce.** `python -m computations.pattern_domains --steps 8192 --side 24 --max-period 16` (about 35 s), and with
`--side 16 --max-period 8`, and with `--steps 4096 --side 12 --max-period 7` and `--side 10`.
[tests/test_pattern_domains.py](../../tests/test_pattern_domains.py) checks the census against blocks checked cell by
cell on rows from `computations.rule30.spacetime`, and the fixed alternating row.
