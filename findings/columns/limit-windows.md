---
title: Windows of 14 cells followed through the column's whole history exclude every tail of up to six cells but 10101 after 22 white cells, and 1,672 blocks of period at most 22
category: columns
problems: [1]
status: computed
formalization: partial
evidence: [computations/limit_windows.py]
---

# Windows of 14 cells followed through the column's whole history exclude every tail of up to six cells but 10101 after 22 white cells, and 1,672 blocks of period at most 22

[WallSegments](../../Rule30Open/Columns/WallSegments.md) and [WallSets](../../Rule30Open/Columns/WallSets.md) follow the
cells beside a column from the wall that nine 1s leave. Here the start is not a wall but the column's whole history: no
run of 1s is needed, and a white run narrows the windows that the rest of the block leaves. The test, with windows of
`w` cells, is the pinned kit's bitmask strip certificate taken to its limit. It excludes more blocks than the wall sets
at every period, reproduces the kit's grammar of long white runs with almost the same thresholds, and puts the white run
that a tail of up to six cells needs at 22 where the pinned kit has 74. Each block and each tail family needs only an
instance of the kit's `stripCert` or `padding_strip`; the mixtures need a new soundness lemma.

## Result

**The test.** Let column $k$ repeat a block from some time on. The window is cells $k + 1, \dots, k + w$; cell
$k + w + 1$ is free at every step, so one step beside a column reading $x$ sends a window to two windows (`window_moves`).
At a late time $t$ the real window lies in the image of the set of all windows under the block read $m$ times, for every
$m$ with $t - mP$ past the start; these sets decrease with $m$, so it lies in their limit, the set $S_i$ of windows at
each phase $i$ (`limit_sets`). If at every 0 of the block all windows of $S_i$ have the same cell $k + 1$ (`is_good`),
then cell $k + 1$ is a function of the phase at the 0s, column $k - 1$, which is
$x_t(k - 1) = x_{t+1}(k) \oplus (x_t(k) \lor x_t(k + 1))$, repeats with the column, and
[the adjacent-column theorem](../../Rule30Open/Columns/AdjacentColumns.md) forbids that. So no column of an orbit of a
row with a leftmost 1 repeats a good block.

**The kit's form of the test.** The pinned kit's `Rule30StripCertificates.stripCert w K k` starts from all strips of
$K$ cells, applies the word $w$ for $k$ periods, checks that one more period maps the result into itself (automatic for
a decreasing sequence) and asks that cell 1 be constant at every white phase. So `is_good` at windows of 14 cells is
`stripCert` of the block at $K = 14$ for every $k$ at least the number of periods the limit takes to stabilize, and
`Rule30FiniteStrips.not_eventually_word_strip` (with `not_eventually_word_strip_finite`) is its soundness for every
column of every row with a leftmost 1. Each good block is therefore a kernel-checkable instance of the kit's lemmas.
`tail_thresholds` is the analogue of the kit's `Rule30WhitePadding.padding_strip`, which certifies $0^r u$ for every
$r \ge N$: the kit runs it with $k = 2$ and small widths (and `Rule30ShortTail` uses `stripCert` of $0^r 111$ at
$K = 14$, $k = 2$), this entry with the exact limit at 14 cells. What is new is the lower thresholds (22 against 74),
the survey counts and the mixture fixed point (`consistent`).

**Tails after a white run** (`tail_thresholds`, windows of 14 cells). For a tail $t$ that starts and ends with 1, write
$q_0(t)$ for the least $q$ such that $0^q t$ is good for every $q' \ge q$. Reading a run of 0s is a fixed relation on
windows whose powers repeat with period 4 after a preperiod of 53 steps (`white_cycle`), so goodness of $0^q t$ for
$q \ge 57$ depends only on $q \bmod 4$, and the $q \le 60$ decide every $q$.

| Tail length | Tails | With a threshold | Largest $q_0$ | No threshold |
|---:|---:|---:|---:|---|
| 1 | 1 | 1 | 10 | |
| 2 | 1 | 1 | 8 | |
| 3 | 2 | 2 | 18 | |
| 4 | 4 | 4 | 16 | |
| 5 | 8 | 7 | 18 | 10101 |
| 6 | 16 | 16 | 22 | |
| 7 | 32 | 30 | 26 | 1010001, 1100001 |
| 8 | 64 | 60 | 30 | 10000111, 10011101, 10110001, 11100001 |

The families of at most six cells that start and end with 1 are proved in Lean with these thresholds
([TailFamilies14](../../Rule30Open/Columns/TailFamilies14.md)); at 20 cells every tail of up to eight cells but
$1100001$ has a threshold, $10101$ at 26 ([tail families](tail-families.md)).

So no column repeats $0^q t$ for any $q \ge 22$ and any tail $t$ of at most six cells but $10101$, nor for $q \ge 30$ and
a tail of at most eight cells but those seven. The thresholds of the tails of up to five cells are 10 for $1$, 8 for $11$,
9 for $101$, 18 for $111$, 16 for $1001$, 9 for $1011$, $1101$ and $1111$ (and also 7), 11 for $10001$ (and 9), 8 for
$10011$, 9 for $10111$, 18 for $11001$, 9 for $11011$, 10 for $11101$ (and 8) and 13 for $11111$. The thresholds of the
tails of six cells are 8 to 18 except for $111101$, which needs 22. The pinned kit excludes $0^r u$ for $u$ of at most
four bits from $r = 49$, five from 69 and six from 74 (`Rule30ShortTail`, `Rule30FiveTail`,
`Rule30SixTailSharpened`) for every tail of that size, $10101$ included, which this test misses. The pinned kit's white-padding families (`game.PADDING_FAMILIES`) need these white runs for the same tails:

| Tail | 101 | 1101 | 11101 | 1001 | 1011 | 101011 | 1111 | 1 | 11 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Kit | 23 | 14 | 23 | 22 | 13 | 13 | 31 | 9 | 8 |
| Here | 9 | 9 | 10 | 16 | 9 | 9 | 9 | 10 | 8 |

(for the tails $1$ and $11$ the kit's figures are those of its padded words, which are better by one and equal here).

Larger tails need a few
more white cells each, about four per cell (`--tails 10 --width 14` gives the largest threshold as 35 at nine cells and 39 at ten).

**Mixtures** (`consistent`, `mixture`). Let $Y$ be the windows that any history of segments $t\,0^q$ leaves at the start of
a segment, with $q$ at least a bound that may depend on $t$: it decreases to a fixed set, and if from $Y$ the first cell
is known at every 0 of every segment and of every white run after it, then every cyclic word made of such segments is
good, for any number of segments. At windows of 14 cells:

- Tails of up to six cells, with white runs of at least 18, are consistent for the 30 tails that are good alone at 18
  (all but $10101$ and $111101$); with at least 26, for the 31 that are good alone (all but $10101$); with at least 22,
  for 30 of the 31 ($111101$ is dropped). Tails of up to eight cells with white runs of at least 26 are consistent for
  120 tails ($10110111$, whose own threshold is 30, is absent at 26; at 30 it is dropped, as $111101$ is at 22). So every cyclic word whose black clusters have at most six cells and are separated by white runs of at
  least 26 is excluded, except for the cluster $10101$, with any number of clusters and so for periods without bound.
  The kit's families of long white runs have no internal white run in a cluster.
- Runs of at least nine 1s join every mixture computed here (tails of up to six or eight cells at white runs 18 to 30,
  and the runs 1, 2 and 4 at 9) (`long_black_states`; windows of many cells keep learning from further 1s, so every
  length from 9 on is included).

**Blocks by period** (`survey`, windows of 14 cells). Counts of good primitive blocks, against the finite game
([up to 16](game-blocks.md), [17 and 18](game-blocks-18.md), [19 and 20](game-blocks-20.md), [21](game-blocks-21.md)):

| Period | 8 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Good blocks | 2 | 3 | 6 | 7 | 20 | 27 | 43 | 64 | 96 | 124 | 183 | 240 | 345 | 511 |
| WallSets | 0 | 1 | 2 | 4 | 8 | 12 | 21 | 28 | 43 | 54 | 77 | 92 | 125 | 148 |
| Neither WallSets nor the kit | 0 | 0 | 0 | 0 | 4 | 11 | 18 | 32 | 48 | 64 | 99 | 141 | 209 | 348 |
| The game | 3 | 3 | 7 | 9 | 21 | 31 | 53 | 68 | 119 | 142 | 217 | 291 | 434 | |

The block of period 1, the constant $1$, is also good, and no block of period 2 to 7 or 9 is. In all, 1,672 blocks of
period at most 22 are good. All 616 blocks of WallSets up to period 22 are good. The "Neither" row leaves out the
blocks that `kit_excludes` accepts: the pinned kit's strip certificates, padded words, padding and black-run families,
and the main branch's white runs of at least 17 and four categories. Of the 76 blocks of period at most 14 that
the game excludes, 66 are good here and the other 10 are not: the constant $0$ and $00000001$, $00000001011$,
$000000010111$, $000000001111$, $0000000011111$, $00000000011101$, $00000000011111$, $00000000101011$ and
$00000001011011$. The game is the same test with the cells right of the column simulated exactly and the left column
asked to be a function of the phase on each recurrent component. Every node on a cycle of the game graph at phase $i$
is reachable from itself in a multiple of $P$ steps, so its window lies in $S_i$; a block good at 14 cells therefore has
cell $k + 1$ constant at the 0s on every recurrent component, and the game excludes it at 14 cells. The game lists up
to period 21 were computed at widths 6, 10 and 14 in turn, so every good block of period at most 21 is in the game's
list, by this inclusion (the counts, 79 to 95 percent of the game's at periods 13 to 21, are consistent with it). What
it adds is that the blocks come in families that hold at
every period, as above, and one argument covers them; and it reaches period 22 (511 blocks) with no game run.

## What it adds to WallSets and the kit

- WallSets needs nine 1s in a row. This test needs none: 974 of the good blocks of period 13 to 22 are neither in
  WallSets nor excluded by the kit (pinned or main), for example $0^{14}101$, $0^{13}1101$, $0^{12}10011$ and
  $0^{11}10001$ and their rotations. Of the 974, 682 have exactly one white run of at least 8, and 211 have a run of eight 1s or more and no white run of 8, such as $0^4 1 0 1^8$
  with its white run short (`--survey` prints both counts).
- At a white run of 22 the pinned kit's tails of up to six cells are all excluded but $10101$, against 74.
- The kit's long white runs have thresholds 17, or 10, 8, 7 and 9 for black runs of 1, 2, 4 and at least 9; the same
  mixtures here need 16 (18 after exactly three 1s) for every black run, and at most 10, 9, 9 and 9 for the runs 1, 2, 4 and at
  least 9, so the thresholds are not lowered ([window thresholds](../../negative-results/columns/window-thresholds.md)).

## Method

- `window_moves(width)` is the table of steps; `limit_sets(block)` iterates the image of all windows until the set at
  phase 0 stops changing (the sequence decreases, so it does); `is_good` tests the 0s.
- `white_cycle` computes the powers of the one-step relation of a run of 0s as bit sets and verifies the repeat by
  comparing rows; `tail_thresholds` tests $0^q t$ for $q$ up to the preperiod plus two periods minus one.
- `consistent` takes the generators `{tail: least white run}` and optionally the least white run after runs of at least
  nine 1s, iterates $Y \leftarrow Y \cap \bigcup_{\text{segments}} \bigcup_{q \ge \text{least}} Z^q(\text{tail}(Y))$ from
  all windows to a fixed point, with the orbits of the white relation on sets found by repetition, and checks the 0s
  from $Y$.
- The test checks the code against direct simulation of random driven rows (the cell $k + 1$ at the 0s agrees across
  40 random rows after 40 periods, with the value the limit gives), a second implementation with tuples at width 4 on
  every block of period at most 8, the powers of the white relation as a matrix, the WallSets blocks of period 9 to 13
  at width 6 (the survey finds all 616 up to period 22 good), and the kit sets against `game.kit_blocks`.

## Reproduce

```bash
python -m computations.limit_windows --survey 22 --width 14 --workers 10   # 1,672 blocks, about 8 min
python -m computations.limit_windows --tails 8 --width 14 --cycle 14       # the table of tails, about 2 min
python -m computations.limit_windows --mixtures 6 --width 14 --whites 18,22,26
python -m computations.limit_windows --mixtures 8 --width 14 --whites 26,30
python -m computations.limit_windows --runs 8,10,12,14,16                  # one run of 1s alone, by width
```
