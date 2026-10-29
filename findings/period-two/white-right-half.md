---
title: Against a white right half, no left half of fewer than a million cells keeps the center alternating
category: period-two
problems: [1]
status: computed
formalization: partial
evidence: [computations/coupled.py]
---

# Against a white right half, no left half of fewer than a million cells keeps the center alternating

The kit's open milestone for period two,
[`Rule30PeriodTwoSideways.CQ01Empty`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30PeriodTwoSideways.lean),
asks that no finite configuration whose cells right of the center are white keeps its center alternating from time 0.
Exactly one left half, finite or not, does so, and computing it to depth $2^{20}$ shows that every left half of fewer
than 1,048,573 cells loses the alternation within 21 steps past its width. That left half has density 1/2 and white
runs no longer than a random sequence has, so this is evidence for the milestone, not a proof. For every right half of
at most 14 cells the same holds for left halves of fewer than 4,079 cells, within 26 steps.

In Lean, [WhiteRightHalf](../../Rule30Open/PeriodTwo/WhiteRightHalf.md) computes $\Psi(\emptyset)$ to depth 32,768
in the kernel: every configuration with a white right half and a left half within depth 32,754 leaves the alternation
$1, 0, 1, \dots$ within 13 steps past its width.

## The one candidate

Fix the center column $c$ and the right half $R$ at time 0. The right half evolves as the half driven by $c$, so its
column 1 is known; the center's update $c(t + 1) = x(t, -1) \oplus (c(t) \lor x(t, 1))$ forces column $-1$; and
Rule 30 is permutive in its left input, so columns 0 and $-1$ rebuild every column to the left,
$x(t, -j - 1) = x(t + 1, -j) \oplus (x(t, -j) \lor x(t, -j + 1))$. The row at time 0 that results, $\Psi(R)$, is the
only left half that keeps the center on $c$ forever (the kit's `Psi_unique`), and a left half that first differs from
it at depth $d$ keeps the center on $c$ through time $d - 1$ and leaves it at time $d$ (`exact_death_center`). A finite
left half of width $W$ differs from $\Psi(R)$ by the first black depth of $\Psi(R)$ past $W$, so the white runs of
$\Psi(R)$ are exactly how far finite left halves outlast their widths. `CQ01Empty` says that $\Psi(\emptyset)$ has
infinitely many black cells. The kit records this death identity for widths up to 300.

## Result

$\Psi(\emptyset)$ for the alternating center, computed sideways to depth $2^{20} = 1{,}048{,}576$:

| center from time 0 | black cells | last black depth | longest white run | last records (length at first depth) |
|---|---|---|---|---|
| $1, 0, 1, \dots$ (the kit's) | 525,185 | 1,048,573 | 20 | 12 at 16,529, 19 at 41,071, 20 at 564,974 |
| $0, 1, 0, \dots$ | 523,677 | 1,048,576 | 22 | 17 at 193,423, 19 at 264,573, 22 at 564,973 |

So every finite configuration with a white right half and a left half of width $W < 1{,}048{,}573$ has a center that
leaves the alternation $1, 0, 1, \dots$ by time $W + 21$, and the alternation $0, 1, 0, \dots$ by time $W + 23$ when
$W < 1{,}048{,}576$.

Over all 16,384 right halves of at most 14 cells, $\Psi(R)$ to depth 4,096 has white runs of at most 25 in either
phase, and a black cell at depth 4,079 or beyond. So no finite configuration with a right half of at most 14 cells and a
left half of fewer than 4,079 cells keeps its center alternating from time 0 past 26 steps beyond the left width. This
complements [the 120-cell finding](alternating-within-120.md), which covers every right half but left halves of at most
120 cells.

Heuristic: among $n$ fair coin flips the longest run of tails is about $\log_2 n$, 20 for $n = 2^{20}$ and 26 for the
$2^{26}$ cells of each phase of the second computation, against 20 to 22 and 25 here.

## What it means

$\Psi(\emptyset)$ is one explicit 2-adic integer, and `CQ01Empty` asks only that its binary expansion does not end in
zeros. To depth $2^{20}$ it looks like a random sequence, so nothing in it suggests a pattern a proof could use.

For the three words of period four the same candidate is periodic. Against a white right half, $\Psi$ repeats with
period 7 or 14 from depth at most 34, in each word and phase. In 6 of the 12 cases the repeating row is a row of the
kit's ether, and in the other 6 it becomes one within 1 to 10 steps of Rule 30. The reason is absorption: the white
right half enters the kit's ether-and-wall family within 16 steps, after which column 1 repeats, and a repeating pair
of columns rebuilds a periodic left half. [EmptyRight.lean](../../Rule30Open/Columns/EmptyRight.md) turns that into a
proof that no finite configuration with a white right half has a center repeating $0001$, $0011$ or $0111$, and, through
the kit's period-three trap, $001$. Beside an alternating center the right half never locks
([the right channel](right-channel.md), [the absorption route](../../negative-results/period-two/absorption-route.md)),
and the candidate inherits its randomness.

## Reproduce

```bash
python -m computations.coupled empty --depth 1048576
python -m computations.coupled all --cells 14 --depth 4096
```

[computations/coupled.py](../../computations/coupled.py) runs the first in about 2.5 min and the second in about 2 min.
The tests check $\Psi$ against stepping whole rows (the death identity, for random words, phases, right halves and
widths), against the antidiagonal rebuild of [held_map.py](../../computations/held_map.py), and, for $0011$, against the
left half of the kit's ether.
