---
title: Windows of 20 cells exclude 0^q 10101 for every q of at least 26 and give every tail of up to eight cells but 1100001 a least white run; 1100001 has one, 37, at 22 cells
category: columns
problems: [1]
status: computed
formalization: wanted
evidence: [computations/tail_families.py, computations/limit_windows.py]
---

# Windows of 20 cells exclude 0^q 10101 for every q of at least 26 and give every tail of up to eight cells but 1100001 a least white run; 1100001 has one, 37, at 22 cells

[Limit windows](limit-windows.md) decides the families $0^q t$, for every $q$, with windows of 14 cells: every tail $t$
of at most six cells that starts and ends with 1 has a least white run $q_0(t)$ except $10101$, and seven tails of seven
or eight cells have none. [TailFamilies14](../../Rule30Open/Columns/TailFamilies14.md) proves the 31 families of at
most six cells in Lean. Here the same test runs with windows of 20 cells, which `limit_windows` could not reach because
it holds the powers of the white relation as $2^{20}$ rows of $2^{20}$ bits. All 128 tails of at most eight cells but
$1100001$ get a least white run, $10101$ among them at 26, and $1100001$ gets one, 37, with windows of 22 cells.

## Result

**The white relation at 20 cells** (`white_cycle_sets`). One step beside a 0 sends a window of 20 cells to two windows.
Row $u$ of the $j$-th power of this relation is the set of windows reached from $u$ in $j$ white steps, so the powers
repeat from $p$ with period $d$ exactly when every row does: $p$ is the largest preperiod of a row and $d$ the least
common multiple of their periods. Following the $2^{20}$ rows one at a time gives **preperiod 84 and period 4** at 20
cells (53 and 4 at 14 cells). Goodness of $0^q t$ for $q \ge 88$ therefore depends only on $q \bmod 4$, and the $q \le
91$ decide every $q$.

**Tails after a white run at 20 cells** (`tail_table`, $q = 1, \dots, 91$). For a tail $t$ that starts and ends with
1, $q_0(t)$ is the least $q$ such that $0^q t$ is good for every $q' \ge q$; the last column is the largest limit set
of a good $0^q t$, over the phases, the $q$ and the tails of that length.

| Tail length | Tails | With a threshold | Largest $q_0$ | No threshold | Largest limit set |
|---:|---:|---:|---:|---|---:|
| 1 | 1 | 1 | 10 | | 6,303 |
| 2 | 1 | 1 | 8 | | 17,169 |
| 3 | 2 | 2 | 18 | | 11,310 |
| 4 | 4 | 4 | 16 | | 12,694 |
| 5 | 8 | 8 | 26 | | 12,791 |
| 6 | 16 | 16 | 22 | | 15,959 |
| 7 | 32 | 31 | 25 | 1100001 | 27,633 |
| 8 | 64 | 64 | 30 | | 16,103 |

Against 14 cells, 27 thresholds change and none rises:

- six tails without a threshold at 14 cells get one: $10101$ at 26, $1010001$ at 15, $10011101$ at 15, $10110001$ at
  18 (with $q = 15, 16$ good too), $10000111$ at 23 and $11100001$ at 24;
- 21 thresholds drop, by 1 to 4: $10001$ 11 to 9, $100111$ 18 to 17, $110111$ 10 to 9, $111011$ 18 to 14,
  $1000001$ 16 to 14, $1000111$ 26 to 25, $1011011$ 8 to 7, $1100111$ 17 to 15, $1101001$ 13 to 10, $10000001$ 18 to
  17, $10001101$ 17 to 16, $10010001$ 15 to 14, $10010101$ 18 to 16, $10100001$ 17 to 16, $10100101$ 24 to 21,
  $11000101$ 14 to 13, $11000111$ 17 to 15, $11010001$ 21 to 20, $11101011$ 14 to 13, $11101111$ 25 to 23 and
  $11111101$ 24 to 23.

So, with windows of 20 cells, no column of the orbit of a row with a leftmost 1 repeats $0^q t$ for any $q \ge 26$ and
any tail $t$ of at most six cells that starts and ends with 1, $10101$ included, nor for any $q \ge 30$ and any such
tail of at most eight cells but $1100001$. The test is the kit's strip certificate at $K = 20$ with the exact limit, so
each $q$ is an instance of `Rule30FiniteStrips.not_eventually_word_strip`; the family over all $q$ rests on the
preperiod and period above.

**$1100001$.** At 20 cells $0^q 1100001$ is good for no $q \le 91$, so for no $q$. At 22 cells (`--good`) it is good
for every $q$ from 37 to 100 and for no $q \le 36$, and cycle certificates (below) of period 4 cover every $q \ge 49$,
from the starts 49, 50, 51 and 52 with two periods each. So with windows of 22 cells it is excluded for every
$q \ge 37$. The preperiod of the white relation at 22 cells is not computed; the certificates make it unnecessary.

**Cycle certificates of $10101$ at 20 cells** (`cycle_certificate`, the check of TailFamilies14). The check of period 4
passes from the starts 46, 47, 48 and 49, with two periods, and at no start below them in their residue classes, with
up to eight periods. So a proof of the family in the form of TailFamilies14 would have four pieces of period 4 and the
20 single words $q = 26, \dots, 45$.

**All tails at once.** With the thresholds above, every tail of at most eight cells that starts and ends with 1 is
excluded after a white run of at least 37, by windows of at most 22 cells.

## What the kit has

The pinned kit proves $0^r 10101$ excluded for every $r \ge 69$, in every column of every row with a leftmost 1
(`Rule30WhitePadding10101`), and every tail of at most four, five and six cells from 49, 69 and 74 (`Rule30ShortTail`,
`Rule30FiveTail`, `Rule30SixTailSharpened`), with sharper bounds for $1$, $11$ and $10111$ (9, 8 and 9 for the center
column, `Rule30PaddedWords`). Its main branch has the same bound for $10101$ and sharper center-column bounds for nine
more tails of at most six cells, among them $1111$ from 7 and $1^k$ ($k \ge 3$) from 17;
[TailFamilies14](../../Rule30Open/Columns/TailFamilies14.md#what-the-kit-has) compares them tail by tail. At 20 cells
the thresholds here stay above the kit's for $1$ (10 against 9), $111$ (18 against 17) and $1111$ (9 against 7). For the
tails of seven and eight cells it has `Rule30ArbitraryWhitePadding`, whose white run for a tail of $n$ cells is singly
exponential in $n$ (more than $2^{20n}$). The thresholds here, 26 for $10101$, at most 30 for the tails of up to eight
cells and 37 for $1100001$, are computed, not proved.

## What a Lean proof at 20 cells needs

The kit's bit-parallel image `Rule30WhiteEndNine.fimage` makes 14 cells cheap: TailFamilies14 checks 378 pieces in
about 150 seconds. At 20 cells a set is a number of $2^{20}$ bits and an image works on numbers of $2^{21}$ bits: ten
images from all windows take 5.3 s of kernel time and 1.7 GB of memory, because the kernel keeps the intermediate
numbers. One piece $(N, d, k)$ of TailFamilies14 costs about $(k + 2)(N + d + |t|)$ images, 220 for each class piece
of $10101$ above, so about 110 s and some 25 GB in one declaration. Splitting the check into declarations of about ten
images each needs the sets between them as literals of $2^{20}$ bits (256 KB of hexadecimal each), and a sparse list
of windows does not help at the start: the white images of all windows shrink to their limit of 4,263 windows only
after 47 steps (`limit_windows --stabilize 20`). A sparse certificate, a closed list of windows with a one-period check
and a separate proof that the true window enters it, is not designed here.

## Method

- `singleton_orbit` follows the sets reached from one window by white steps until one repeats, as sorted arrays;
  `white_cycle_sets` takes the largest preperiod and the least common multiple of the periods over all windows, in
  chunks, with a progress bar. The test checks it against `limit_windows.white_cycle` (the relation as bit sets) at 5
  and 8 cells.
- `tail_table` runs `limit_windows.is_good` on $0^q t$ for $q = 1, \dots, p + 2d - 1$, as
  `limit_windows.tail_thresholds` does with its own cycle; the test checks the two against each other at 8 cells.
- `cycle_certificate` is `TailFamilies14.cycleCert` on sets of windows as arrays; the test checks that a single-word
  certificate is found exactly where `is_good` holds on four blocks at 10 cells, and that two pieces of the Lean module
  pass it at 14 cells.

## Reproduce

```bash
python -m computations.tail_families --cycle 20                                    # (84, 4), about 9 min
python -m computations.tail_families --tails 8 --width 20 --preperiod 84 --workers 2   # the table, about 30 min
python -m computations.tail_families --good 1100001 --width 22 --upto 100          # about 80 s
python -m computations.tail_families --certify 1100001 --width 22 --least 37 --upto 100
python -m computations.tail_families --certify 10101 --width 20 --upto 90
```

The kernel cost of ten images at 20 cells, with the pinned kit:

```lean
import Ruliology.CellularAutomata.Rule30WhiteEndNine
open Ruliology.CellularAutomata Rule30StripCertificates Rule30WhiteEndNine
set_option maxRecDepth 100000
theorem ten : fapply 20 (List.replicate 10 false) (fullSet 20) % 2 = 1 := by decide +kernel
```
