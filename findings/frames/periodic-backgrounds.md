---
title: Only the stripe and the ether backgrounds give a periodic column
category: frames
problems: [1]
status: computed
formalization: wanted
evidence: [computations/backgrounds.py]
---

# Only the stripe and the ether backgrounds give a periodic column

Take a row that is white right of some cell and eventually periodic to its left. Among every such row with a period
word of up to 9 cells and a prefix of up to 2 cells, the column under the edge is eventually periodic for exactly
three kinds of background: white, the alternating stripe (column eventually constant), and the period-7 backgrounds of
the kit's ether (column period 4 or 8). Every other background tried gives a column with no period up to 64.

## Result

Over 2,048 steps, with the column's second half tested for periods up to 64:

| Background, as its least rotation | Column periods |
|---|---|
| $0$ (white) | 1 |
| $01$ (the stripe) | 1 |
| $0000001$, $0010011$, $0111111$ | 4 and 8 |
| $0000111$, $0011111$ | 8 |

The five period-7 words are the ether family. The kit's
[`Rule30Ether`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Ether.lean)
studies this background; next to the center its boundary layer, columns 1 to 8, has period 8 and absorbs the chaos to
its right.

## Why it matters

A finite row cannot use either mechanism: it is white far to the left, and information from the left passes every
column ([the one-way valve](../dynamics/one-way-valve.md)). So these rows show what an eventually periodic center column
would need near the center, a stripe or an ether, and that it would have to persist against the chaotic region to its
left. A survey of the 2-adic rationals $p/q$ with odd $q \le 31$, whose periods reach 30 cells, found the
same three kinds and no others.

## Reproduce

```bash
python -m computations.backgrounds 9 2 2048
```

[computations/backgrounds.py](../../computations/backgrounds.py) runs in about 5 s.
