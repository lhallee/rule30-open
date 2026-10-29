---
title: Column words that fix the cell beside the column exclude no block the finite game misses, up to period 20
category: columns
problems: [1]
status: negative
kind: no-signal
evidence: [computations/forcing.py]
---

# Column words that fix the cell beside the column exclude no block the finite game misses, up to period 20

**Idea.** The block exclusions of [WallSegments](../../Rule30Open/Columns/WallSegments.md),
[WallSets](../../Rule30Open/Columns/WallSets.md) and [WideWall](../../Rule30Open/Columns/WideWall.md) rest on one step:
at each 0 of a repeating column $k$, cell $k + 1$ is a function of the column's history, so it repeats with the column,
and then column $k - 1$ repeats too, against [the adjacent-column theorem](../../Rule30Open/Columns/AdjacentColumns.md).
Nine 1s give such a function, the wall of [LongRuns](../../Rule30Open/Columns/LongRuns.md). If other column words gave
one, the step would reach blocks without nine 1s in a row. Call a word $u$ of $n$ values of column $k$, read at times
$t - n, \dots, t - 1$, *forcing* if cell $k + 1$ at time $t$ is the same for every start of cells
$k + 1, \dots, k + n + 1$ at time $t - n$, the only cells that can reach it in time. A block is excluded when the $n$
values before each of its 0s, read cyclically, form a forcing word. This is the step in its strongest form: it keeps
every correlation that three values or sets of windows forget.

**Outcome.**

- **Forcing words without long runs exist.** The shortest have seven values: $0110000$ forces 1 and $0110001$ forces 0.
  Nine 1s force 0, and eight 1s and a 0 force 1. Of the words of length $n$, the fraction that force is 0.0156 at
  $n = 7$, 0.0586 at 10, 0.1247 at 16 and 0.1446 at 20, growing more slowly at each length. Of the 4,260 forcing
  words of length 20 with no shorter forcing suffix, 4,222 have no nine 1s in a row.
- **They exclude few blocks.** With the forcing words of length 20, 364 of the primitive blocks of period at most 20
  are excluded. The 343 among them with nine 1s in a row are exactly the blocks of WallSets, at every period, so its
  sets of three-cell windows after the wall lose nothing on this range. The other 21 are $01^7$, $0 1^8 0 1$, padded
  words such as $0^q 11$ for $9 \le q \le 12$ and $0^q 10011$ for $9 \le q \le 11$, and blocks with eight 1s in a row
  such as $0^q 1 0 1^8 0 1 1$ for $q = 3, 5, 6, 7$. A lookback of fixed length does not follow a padding to the end:
  $0^q 11$ for $13 \le q \le 18$, and $0^q 1$ for every $q \le 19$, are not among them. Every one of the 364 has a run of at least
  seven 1s or of at least nine 0s.
- **The game excludes all of them.** [The finite game](../../Rule30Open/Columns/FiniteGame.md) excludes each of the 21
  at width 6, and the kit excludes seven of them, by strip certificates and one padded word. Up to period 16 the forcing
  words of length 20 exclude 91 blocks, the game 197 ([the game blocks](../../findings/columns/game-blocks.md)).

**What it means.** A forcing word fixes the cell beside the column against every start, including starts that a right
half which has run beside the repeating column for a long time can no longer reach. The game's recurrent components
use that history, and a longer lookback approaches it only slowly: from length 16 to 20 the blocks of period at most
16 grow from 80 to 91. So a wall after other runs exists, and on this range it reaches no block the game misses; both
stay with blocks that have a long run near their 0s, which typical blocks of large period lack.

## Reproduce

```bash
python -m computations.forcing --length 20 --max-period 20 --game
```

[computations/forcing.py](../../computations/forcing.py) finds the forcing words by a search over the word that carries
the exact set of configurations of the cells that can still reach cell $k + 1$, checked against brute force over every
start for every word of up to nine values, and runs the block test; it takes about 2 minutes. With `--length 16` it
gives the 80 blocks of period at most 16.
