---
title: The exact channel from a free column into column 1 keeps positive entropy at every width up to 30 beside the three words of period four
category: columns
problems: [1]
status: negative
kind: no-signal
evidence: [computations/channel_ladder.py]
---

# The exact channel from a free column into column 1 keeps positive entropy at every width up to 30 beside the three words of period four

**Question.** Beside a center that repeats $0001$, $0011$ or $0111$, take the window of columns 1 to $W$ with column
$W + 1$ free at every step, restricted to its limit set (the windows with arbitrarily long histories), and read column
1 at the white phases, where column $-1$ is the next center cell xor column 1. If at some finite $W$ the readings of
every play were eventually periodic, column $-1$ would be eventually periodic for every right half, finite or not, and
masked Jen ([AdjacentColumns](../../Rule30Open/Columns/AdjacentColumns.md), the kit's `Rule30MaskedJen`) would exclude
the word with no `Absorption` and no `C3`. By [the reading lists of entropy
0](zero-entropy-readings.md) that happens at width $W$ exactly when the cyclic-class test passes there, which is when
the channel's entropy is 0. Does the entropy reach 0 at some width up to 30?

**Outcome.** No. For each word and every width from 10 to 30 the class test fails on one large component of the window
graph, and the exact entropy of the readings stays positive: at width 30 it is 0.298, 0.296 and 0.242 bit per period
for $0001$, $0011$ and $0111$. The entropy falls steadily with $W$. For $0011$ and $0111$ the kill test of this search
fires: at width 30 the fall over two cells is below 0.01, and a geometric fit over widths 25 to 30 levels off at a
growth of 1.096 and 1.125 words per period (0.13 and 0.17 bit), a heuristic sign that no width brings them to 0. For
$0001$ it does not fire: the fall over two cells is 0.015 at width 30, nearly constant since width 25, and the fit
does not level off above growth 1. The free column makes every entropy here an upper bound for the channel beside a
real right half, so the ladder neither excludes the words nor shows that the real channel has positive entropy; a
straight-line extrapolation (a heuristic) would bring $0001$ to entropy 0 near width 60, where the limit set would
hold some $10^{11}$ windows per phase.

## The ladder

**Prefix lemma.** Dropping column $W + 1$ maps a step at width $W + 1$ to a step at width $W$: the first $W$ cells of a
successor are a successor of the first $W$ cells, with the old column $W + 1$ as the free cell. So a window with
arbitrarily long histories at width $W + 1$ has a prefix with arbitrarily long histories at width $W$:
$L(W + 1) \subseteq \{w : \text{prefix}_W(w) \in L(W)\}$, and the channel's entropy never rises with $W$. `limit_sets`
starts from all $2^{10}$ windows at each phase and widens one cell at a time: the candidates at $W + 1$ are the windows
whose prefix lies in $L(W)$, and `trim` removes, until none is left, the candidates with no predecessor among those
left. What remains is the greatest set in which every window has a predecessor, which is the limit set (every window of
it has histories of every length, and every window with such histories lies in it).

**Class test and entropy.** On the step graph of the limit set every strongly connected component with a move inside
it has a cyclic period $d$; `classes` asks whether the reading is a function of the level modulo $d$, the test of
`game.component_periods` (the tests compare the two). Within each component that fails, the readings form a sofic
language; its subset automaton, period by period from the set of the component's phase-0 windows (the word of
readings of one period is a function of the phase-0 window, since the free column reaches column 1 only after $W$
steps), is deterministic, and its Perron root, bracketed by Collatz-Wielandt bounds to $10^{-7}$, is the growth per
period. Sets of windows are named in the automaton by their size and two sums of random 64-bit keys, so two different
sets would be merged with probability about $2^{-128}$ per pair; at width 10 a plain construction with sets compared
whole gives the same growth (the tests).

**Results.** At every width only one component of the window graph with a move fails the class test, apart from a
second one of a few hundred windows for $0111$ at widths 22 to 27 (growth 1.070 per period down to 1.029); the
growth per period of that large component, which is the channel's, in words per period with bits per period after
it:

| $W$ | $0001$ | $0011$ | $0111$ |
|---:|---:|---:|---:|
| 10 | 1.3905 (0.476) | 1.4347 (0.521) | 1.3671 (0.451) |
| 12 | 1.3859 (0.471) | 1.3695 (0.454) | 1.3375 (0.420) |
| 14 | 1.3794 (0.464) | 1.3516 (0.435) | 1.3101 (0.390) |
| 16 | 1.3763 (0.461) | 1.3291 (0.410) | 1.2867 (0.364) |
| 18 | 1.3453 (0.428) | 1.3036 (0.382) | 1.2641 (0.338) |
| 20 | 1.3181 (0.398) | 1.2820 (0.358) | 1.2508 (0.323) |
| 22 | 1.2976 (0.376) | 1.2647 (0.339) | 1.2318 (0.301) |
| 24 | 1.2777 (0.354) | 1.2563 (0.329) | 1.2138 (0.279) |
| 25 | 1.2676 (0.342) | 1.2516 (0.324) | 1.2075 (0.272) |
| 26 | 1.2594 (0.333) | 1.2460 (0.317) | 1.2023 (0.266) |
| 27 | 1.2517 (0.324) | 1.2410 (0.312) | 1.1965 (0.259) |
| 28 | 1.2446 (0.316) | 1.2372 (0.307) | 1.1914 (0.253) |
| 29 | 1.2374 (0.307) | 1.2316 (0.301) | 1.1871 (0.247) |
| 30 | 1.2295 (0.298) | 1.2274 (0.296) | 1.1827 (0.242) |

Reading column 1 at all four phases instead of the white ones gives the same growth for $0001$ and $0011$ (the black
phase adds nothing) and more for $0111$ (1.3298 at 16 cells, 1.2771 at 20 and 1.2306 at 24): column 1 at the black
phases of $0111$ is not forced. At 16 cells the readings carry 0.154, 0.205 and 0.364 bit per reading for the three
words, above the bounds 0.050 to 0.072 that [codes of closed walks](zero-entropy-readings.md) give for every list of
forbidden words forced at that width, as they must.

The sizes at width 30, over the four phases: the limit set holds 6,046,121, 9,205,219 and 9,769,651 windows, the
failing component 1,938,448, 3,785,300 and 1,854,251 nodes, and its automaton 74,534, 161,279 and 47,689 states; the
limit set grows by a factor of about 1.5 per cell and the automaton by 1.3 to 1.55. The largest resident memory was
1.66 GB, 3.56 GB and 2.02 GB, and widths 26 to 30 took about 19, 29 and 9 minutes with one thread on a loaded machine
with four cores.

**Structure.** The failing component is terminal up to width 15 for $0001$ (13 for $0011$, 12 for $0111$); from 16
cells for $0001$ (14 for $0011$, 13 for $0111$) a play can leave it into terminal components that pass the class test,
of cyclic period 8. At width 16 the one such component for $0001$ has 109 windows, and they carry the kit's 109 wall
states on columns 4 to 16 (`kit_wall_cells`, against `absorption.kit_wall`). These components grow with the width
(109, 188, 328, 535, 931, ... windows), and a new series starts at 109 windows from 23 cells for $0001$, from 20
and 27 for $0111$, and from 18, 21, 25 and 28 for $0011$. So the
class test fails because the free column can keep a play in the large component as long as it likes; for a real right
half the cells beyond column $W$ decide whether the play leaves it, which is the entry question of [the
certificate](../../findings/columns/period-four-certificate.md) and the kit's `Absorption`. [The reach of the kit's
conjectures](../../findings/columns/kit-absorption-reach.md) asks the other quantifier, a set of windows that every
move keeps away from the family, and finds none up to 26 cells.

## The kill test

The kill test fires for a word if the class test still fails at width 30 and either the fall of the growth over two
cells is below 0.01, or a fit $g(W) = g_\infty + a r^W$ over the last six widths gives $g_\infty$ above 1.05
(`fit_tail`, least squares over a grid of $r$, a heuristic):

| word | fall over widths 28 to 30 | fit over widths 25 to 30 | rms of the fit |
|---|---:|---:|---:|
| $0001$ | 0.0150 | $g_\infty = 0.796$, $r = 0.984$ | $2.4 \cdot 10^{-4}$ |
| $0011$ | 0.0098 | $g_\infty = 1.096$, $r = 0.967$ | $3.4 \cdot 10^{-4}$ |
| $0111$ | 0.0087 | $g_\infty = 1.125$, $r = 0.931$ | $2.0 \cdot 10^{-4}$ |

For $0011$ and $0111$ both conditions hold, and the ladder gives no sign of reaching 0. For $0001$ neither does: the
fall per cell is nearly constant from width 25 to 30 (0.0081, 0.0077, 0.0071, 0.0072, 0.0079), the fit runs below
growth 1 (which no channel can have, since every play reads some word), and the data say nothing about a limit. The
kill test is a heuristic; what the computation proves is the table: no width up to 30 gives entropy 0 for the three
words.

## Controls

- $000000001011$, which the class game excludes at 16 cells ([the class game](../../findings/columns/class-game.md)):
  at width 16 its limit set holds 14,476 windows over the 12 phases, and its three components with a move (7,312, 532
  and 22 nodes, of cyclic periods 12, 36 and 12) all pass the class test, so the channel's entropy is 0 there.
- The alternating center $01$, read at its white phase: at every width from 18 to 22 the window graph has a terminal
  component that fails the class test with growth 1.09207 per period, 0.127 bit per white step, the same at each
  width; the channel as a whole has 0.185 bit at width 18 and 0.137 at 22.

## Where it stops

Each width costs about 1.5 times the last in windows and 1.3 to 1.55 times in automaton states; within 4 GB the
exact entropies reach about 30 cells for $0011$ and a cell or two more for the others, where the growth falls by about
0.004 to 0.008 per cell. If the fall for $0001$ went on at that rate, entropy 0 would come near 60 cells; if it slows
as for $0011$ and $0111$, never. Either way the ladder bounds the real channel from above, and it cannot reach 0 while
a free column can hold a play in the large component, which is the absorption question in another form. The exact
numbers stay as the strongest statement about the channel beside a free column: the readings at width $W$ have
exactly this entropy, against the lower bounds that [codes of closed walks](zero-entropy-readings.md) give.
The same channel, used as a constraint on the free reading of the kit's `C3`, is [the constrained left-half
search](channel-left-c3.md).

## Reproduce

```bash
python -m computations.channel_ladder --block 0001 --widths 10-30           # about 22 min, 1.7 GB
python -m computations.channel_ladder --block 0011 --widths 10-30           # about 31 min, 3.6 GB
python -m computations.channel_ladder --block 0111 --widths 10-30           # about 10 min, 2.0 GB
python -m computations.channel_ladder --block 0111 --widths 16,20,24 --reads all   # column 1 at every phase
python -m computations.channel_ladder --block 000000001011 --widths 16 --base 16  # control: the class test passes
python -m computations.channel_ladder --block 01 --widths 18-22             # control: period two
```

Each run prints the components of every width, the fall over two cells and the fit over the last six widths.
`tests/test_channel_ladder.py` checks the widened limit sets at widths 6 to 8 against `limit_windows.limit_sets` from
all windows, the counts of distinct reading words of 1 to 8 periods from the limit set at width 6 against a brute-force
count, the components and the class test against `game.component_periods`, the growth at width 10 against a plain
subset construction with dense eigenvalues, and the wall component at width 16.
