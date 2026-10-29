---
title: No left half of up to 80 cells meets the kit's C3 for a period-four word
category: columns
problems: [1]
status: computed
formalization: wanted
evidence: [computations/held_map.py]
---

# No left half of up to 80 cells meets the kit's C3 for a period-four word

The kit reduces least period 4 to three open statements about the left half alone,
[`Rule30PeriodFourSkeleton.C3`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30PeriodFourSkeleton.lean)
for $w = 0001$, $0011$ and $0111$ (`least_period_four_of_C3`). For each word and each of the four phases, no left half
of at most 80 cells keeps the kit's pattern from time 0. For $0001$ with the right half's check, the integer condition
of [EtherDomain.md](../../Rule30Open/Columns/EtherDomain.md), no positive integer below $2^{140}$ meets it. The search
follows only the halves that keep the pattern so far, a vanishing fraction, because each reading of cell $-1$ fixes one
more cell of the half. The margin by which the longest-lived half outlasts its length keeps growing, so more
computation moves the bound without settling the statements.

## The statements

`C3 w` says that no finitely supported left half, run as Rule 30 on the cells left of the center with the center
replaced by the effective boundary $c'_w(t) = w(t) \land w(t + 1)$, keeps cell $-1$ equal to a pattern $P_w$ at three
of the four phases for all large times:

| word | $c'_w$ at phases 0 to 3 | $P_w$, cell $-1$ at phases 0 to 3 |
|---|---|---|
| $0001$ | $0000$ | 0, free, 0, 1 |
| $0011$ | $0010$ | free, 0, 0, 1 |
| $0111$ | $0110$ | free, 0, 0, 1 |

The half at time $K$ of a finitely supported half is finitely supported, so `C3 w` holds exactly when no finitely
supported half keeps $P_w$ from time 0, at any of the four phases. For $0001$ the boundary is white, the half follows
the period-two map $H$, and [EtherDomain.md](../../Rule30Open/Columns/EtherDomain.md) proves the stronger integer
condition with the right half's check: the free phase is never black in two consecutive periods.

## The search

Write the half at step $t$ as an integer whose bit $j$ is cell $-1 - j$. The lowest bit at which two halves differ
moves one cell toward the center per step ([Domains.md](../../Rule30Open/PeriodTwo/Domains.md), `held_disagree`),
and the boundary enters only through cell $-1$. So cell $-1$ at step $t$ is bit $t$ of the starting half XOR a
function of its lower bits, and the first $M$ readings of cell $-1$ fix the half's lowest $M$ cells: every sequence of
readings comes from exactly one half modulo $2^M$. This is the triangular structure of
[the period-two search](../period-two/alternating-within-120.md), applied to the period-four statements.

The halves of at most $M$ cells that keep $P_w$ through step $M - 1$ are therefore as many as the readings $P_w$
allows: one free reading in four, so $2^{M/4}$ per phase when 4 divides $M$, against $2^M$ halves; and for $0001$
with the check, the words on the free steps with no two 1s in a row, $F_{k + 2}$ for $M = 4k$ ($F$ the Fibonacci
numbers; 196,418 below $2^{100}$). The search builds the spacetime one antidiagonal at a time along this tree and
follows each branch with white cells beyond cell $-M$ until it fails. It agrees with stepping every half directly for
every support up to 13 or 15.

## Result

Every left half of at most 80 cells fails, for each word in each phase; 1,048,576 branches per phase keep the
pattern through step 79 and each fails later. The latest first failure over the halves of exactly $M$ cells, as a
margin past $M$, over the four phases:

| statement | largest margin, $M \le 80$ | margin at $M$ = 20 | 40 | 60 | 80 |
|---|---|---|---|---|---|
| `C3 0001` | 25, at $M = 76$ | 7 | 9 | 15 | 25 |
| `C3 0011` | 25, at $M = 71$ | 19 | 13 | 16 | 24 |
| `C3 0111` | 27, at $M = 76$ | 8 | 12 | 20 | 24 |

For $0001$ with the check at phase 0, Lean's statement `center_period_four_0001_integer`, every positive integer
below $2^{140}$ fails, the latest at step 166, after 24,157,817 branches keep the condition through step 139. The
margin is 6 at $M = 32$, 10 at 64, 15 at 100, 23 at 120 and 26 at 140.

Heuristic: if the readings past a half's length were fair coin flips, a branch would pass each fixed phase with
probability 1/2, three phases in four, and the longest of $N$ branches would last about $\tfrac{4}{3} \log_2 N$ steps.
For C3 at $M = 80$, with $N = 2^{20}$ per phase, that is 27 steps, against observed margins of 24 to 27; the check
for $0001$ removes more branches, and its margins run a little shorter. The margins grow like $M/3$, and a finite
search settles only the halves it covers.

## What it means

With [the absorption census](absorption-census.md), both of the kit's reductions of least period 4 have computed
evidence: every small right half enters the ether-and-wall family, and no small left half keeps $P_w$. Each condition
has infinite solutions, so a proof has to use that the half is finite. Every infinite branch of the tree is one, and
for each word the ether's left half, read from an ether column aligned with the word, is one that repeats with period
4: the tests check this for the alignments $(6, 0)$ of $0001$, $(0, 0)$ and $(1, 3)$ of $0011$, and $(2, 2)$ of
$0111$, and for $0001$ Lean has it as `ether_fits`, as the kit's `C3w_011_ether` has it for period 3. Neither search
suggests a finite certificate: the margins grow here, and the entry times grow with the support there.

## Reproduce

```bash
python -m computations.held_map 80 --tree c3
python -m computations.held_map 140 --tree check
```

[computations/held_map.py](../../computations/held_map.py) (`tree_failures`) runs the first in about 3 min and the
second in about 8 min; `--tree c3` at 56 cells takes 3 s, and `--tree check` at 100 cells 4 s. The tests check the
tree against stepping every half, and the ether's solutions against direct stepping.
