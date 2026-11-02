---
title: Right halves whose first 14 to 18 cells lie in the forced basin enter the period-four family whatever lies beyond
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ForcedBasin
headline: [forcedBasin_0011_14, forcedBasin_0111_14, forcedBasin_0001_16, forcedBasin_0011_16, forcedBasin_0111_16]
kit: refines
kit_modules: [Rule30Ether, Rule30WhiteEndNine, Rule30StripCertificates]
evidence: [computations/forced_basin.py]
---

# Right halves whose first 14 to 18 cells lie in the forced basin enter the period-four family whatever lies beyond

Masked Jen excludes the three words of least period four, $0001$, $0011$ and $0111$, for a finite configuration as
soon as its right half, driven by the word, enters the kit's ether-and-wall family (the kit's open
`Rule30Ether.Absorption`). The other classes of entering halves in Lean are a vanishing share of the halves of $n$
cells (the halves of at most 14 cells, sparse halves, ether prefixes) or a fixed but tiny one: the halves white on
cells 1 to 30, $2^{-30}$ of them (the kit's `Rule30EtherSingleCell.absorption_high` for $0001$, `high_0011` and
`high_0111` of [WhiteGap](WhiteGap.md)), and the halves white on a longer gap after six cells (WhiteGap). Here the
class is a fixed share of a few percent to a third of all halves for every $n$: the halves whose first $K$ cells form
a window of the forced basin. In Lean
that share is, by word and phase, 4.1% to 14.5% of the halves at $K = 14$ for $0011$ and $0111$ (the basin of $0001$
is empty below 16 cells), 2.5% to 23.5% at $K = 16$ and 7.0% to 33.6% at $K = 18$ ([ForcedBasin18](ForcedBasin18.md)).
By computation it grows to 21.3% to 55.7% at $K = 24$.

## Statement

Drive a right half $x$, cells $1, 2, \dots$ beside the center, with the center repeating $w$ from phase $\varphi$. Its
window at time $t$ is cells $1, \dots, K$. A window *certifies entry* when, for an alignment $(j_0, s)$ of $w$ with the
ether and a depth $k$ with column $j_0 + k$ a $B_3$ column and $k + 13 \le K$, cells $1, \dots, k$ carry the ether and
cells $k + 1, \dots, k + 13$ one of the kit's 109 wall states. Such a half is in the family
(`Rule30Ether.InFamily`), whatever its cells beyond $K$. The *forced basin* $B_K(w, \varphi)$ is the least set of
(phase, window) pairs that holds these and every pair whose successors, for both values of cell $K + 1$, lie in it.
The *rank* of a pair is the round at which it joins. For each word, phase $\varphi < 4$ and the widths in the table
below (`Covers`):

1. **Entry** (`enters_of_basin`). Every driven right half, finite or infinite, whose window at time 0 lies in
   $B_K(w, \varphi)$ is in the family by step $R$, the largest rank.
2. **Counting** (`count_halves`). For every $n \ge K$, exactly $|B_K(w, \varphi)| \cdot 2^{n - K}$ of the $2^n$ right
   halves of $n$ cells start with a window of the basin, and each of them enters by step $R$.
3. **Exclusion** (`excludes_of_basin`). No finite configuration whose cells $1, \dots, K$ at an onset of $w$ at phase
   $\varphi$ form a window of the basin has a center that repeats $w$ from that onset, whatever its left half. (The
   theorem takes the onset as time 0; the configuration at an onset is again finite.)

| word | $K$ | $\lvert B_K \rvert$ at phases 0, 1, 2, 3 | of $2^K$ | $R$ | theorem |
|---|---|---|---|---|---|
| $0011$ | 14 | 885, 837, 665, 685 | 4.1% to 5.4% | 26 | `forcedBasin_0011_14` |
| $0111$ | 14 | 2,243, 2,376, 2,129, 2,322 | 13.0% to 14.5% | 37 | `forcedBasin_0111_14` |
| $0001$ | 16 | 2,212, 2,066, 1,730, 1,647 | 2.5% to 3.4% | 32 | `forcedBasin_0001_16` |
| $0011$ | 16 | 9,957, 9,693, 9,428, 9,093 | 13.9% to 15.2% | 44 | `forcedBasin_0011_16` |
| $0111$ | 16 | 15,332, 15,418, 14,478, 15,204 | 22.1% to 23.5% | 51 | `forcedBasin_0111_16` |
| $0001$ | 18 | 21,588, 21,096, 19,829, 18,456 | 7.0% to 8.2% | 42 | `forcedBasin_0001_18` |
| $0011$ | 18 | 60,151, 59,169, 57,797, 55,883 | 21.3% to 22.9% | 53 | `forcedBasin_0011_18` |
| $0111$ | 18 | 87,964, 86,442, 84,527, 85,589 | 32.2% to 33.6% | 64 | `forcedBasin_0111_18` |

The family needs $k + 13 \le K$ with $(j_0 + k) \bmod 7 = 2$, so it first fits at $K = 13$ for $0111$ (depth 0), 14 for
$0011$ (depth 1) and 16 for $0001$ (depth 3); below those widths the basin is empty. The width-18 theorems are in
[ForcedBasin18](ForcedBasin18.md). The theorems are about the set after $R$ rounds (`basin`) and its size, which the
kernel computes; that no pair joins after round $R$, so that this set is the whole basin, is the computation's
(`python -m computations.forced_basin shares`).

## Argument

1. **The game.** The window steps as the kit's strip step (`Rule30StripCertificates.stripStep`) with the center and cell
   $K + 1$ as inputs (`win_succ`), so the windows of a driven half are one play of the game of
   [BitGame](BitGame.md) with the center as its column, and the cells beyond enter only as cell $K + 1$ (`run_eq_win`).
2. **The all-successor test.** BitGame's preimage `pre` holds every node with some move into a set
   (`BitGame.pre_sound`). Its complement applied to the complement, `allPre`, holds only nodes whose two moves both lie
   in the set (`allPre_sound`). This is generic in the block and the width.
3. **Layers.** `basinFrom` adds, each round, the nodes of `allPre` of the last set to the target. By induction on the
   rounds, a node present after $n$ rounds enters the target within $n$ steps along every play (`basinFrom_sound`).
   The rounds run in the kernel on bit tables of $4 \cdot 2^{K+2}$ bits; nothing but the counts is stored at widths
   14 and 16.
4. **The target is the family.** `target` is built from the kit's wall list, one table per phase. Each of its windows
   matches, on its first $k + 13$ cells, the ether followed by a wall state at the right ether phase (`target_sound`),
   and a half with such a window is in `InFamily` (`inFamily_of_window`). The family is a trap
   (`Rule30Ether.trap_invariant`), so a half that enters stays in.
5. **Counting.** `popc` counts the bits of a table and is the count of the indices whose bit is set (`popc_spec`). The
   kernel evaluates it as `popcR`, a recursor with 16-bit leaves read from a table of the 256 bytes. The halves of $n$
   cells are counted by their first $K$ (`countP_mod`).
6. **Exclusion.** Entry gives `EmptyRight.no_finite_of_family`: in the family, column 1 has period 4 at the white times
   of the center, which masked Jen for finite configurations forbids beside a center of period 4.

The bit-parallel test in step 2 and the layers in step 3 do not depend on the family: any target table, block and
width can use `basinFrom_sound`.

## What the share does and does not give

**The same set as the certificate's forced entry.** [The certificate
finding](../../findings/columns/period-four-certificate.md) measured, in its section "Attraction is open", the windows
from which entry into its lock certificate is forced: $0001$ 11.8% to 13.1% at $W = 20$, $0011$ 27.8% to 29.6%,
$0111$ 41.2% to 42.5%. That target is different, the greatest closed set on which column 1 is fixed at the white
phases, but the two forced basins are the same set of windows for every word and every width from 13 to 20
(`python -m computations.forced_basin compare --widths 13,14,15,16,17,18,19,20`, under a minute). So the shares there
are these shares at widths 14 to 20; what this entry adds is the Lean statement for every half with such a window, the
ranks, the widths 21 to 24 and the entry times below.

**Shares by computation** (`python -m computations.forced_basin shares`), range over the four phases, largest rank in
parentheses:

| $K$ | $0001$ | $0011$ | $0111$ |
|---|---|---|---|
| 13 | | | 8.9% to 10.1% (31) |
| 14 | | 4.1% to 5.4% (26) | 13.0% to 14.5% (37) |
| 15 | | 9.6% to 10.9% (37) | 17.9% to 19.4% (43) |
| 16 | 2.5% to 3.4% (32) | 13.9% to 15.2% (44) | 22.1% to 23.5% (51) |
| 17 | 4.7% to 5.6% (34) | 17.6% to 19.3% (49) | 26.6% to 28.1% (58) |
| 18 | 7.0% to 8.2% (42) | 21.3% to 22.9% (53) | 32.2% to 33.6% (64) |
| 19 | 9.4% to 10.7% (48) | 24.7% to 26.6% (57) | 36.9% to 38.1% (74) |
| 20 | 11.8% to 13.1% (53) | 27.8% to 29.6% (65) | 41.2% to 42.5% (83) |
| 21 | 14.2% to 15.5% (62) | 30.6% to 32.5% (74) | 44.6% to 46.1% (93) |
| 22 | 16.5% to 17.8% (72) | 33.2% to 35.2% (76) | 48.3% to 50.0% (97) |
| 23 | 18.9% to 20.2% (74) | 35.6% to 37.6% (89) | 51.2% to 52.8% (104) |
| 24 | 21.3% to 22.7% (82) | 37.8% to 39.8% (89) | 54.1% to 55.7% (109) |

The share grows by 2 to 6 points per cell at these widths: about 2.4 for $0001$ at every width, for $0011$ by less
at each larger width (from 5.6 to 2.2), and for $0111$ by 4.0 to 5.6 up to width 19 and by 2.8 at width 24. The
largest rank grows by 0 to 13 steps per cell. Whether the share tends to 1 is open, and that is what entry for every finite half through windows alone
would need.

**It does not shorten the slow halves.** For every right half of at most 16 cells driven from phase 0, against the basin
of width 20 (`python -m computations.forced_basin times`, 2,000 steps): every half enters the family; of the 65,536,
62,020 ($0001$), 63,622 ($0011$) and 65,452 ($0111$) reach the basin and enter the family at most 49, 58 and 77 steps
later, and the others enter the family only at a depth whose wall lies beyond cell 20 and are not in the basin by step
2,000. At every quantile the two times differ by 12 to 43 steps:

| word | quantile | family entry | basin entry |
|---|---|---|---|
| $0001$ | 50%, 90%, 99%, 99.9%, 100% | 78, 190, 342, 489, 732 | 50, 163, 316, 462, 708 |
| $0011$ | 50%, 90%, 99%, 99.9%, 100% | 55, 235, 499, 787, 1,627 | 30, 211, 476, 775, 1,600 |
| $0111$ | 50%, 90%, 99%, 99.9%, 100% | 44, 123, 248, 382, 544 | 7, 90, 210, 342, 501 |

A half that is slow to enter the family is slow to reach the basin, by nearly the same number of steps: the time is
spent before the window is in the basin, not in the delays the free cell can force inside it. A larger share of windows
does not shorten that time.

## Lean

`Rule30Open.Columns.ForcedBasin`: `allPre`, `allPre_sound`, `basinFrom`, `basinFrom_add`, `basinFrom_sound`, `run`,
`Enters`, `target`, `target_sound`, `win`, `win_succ`, `inFamily_of_window`, `enters_of_basin`, `popc`, `popcR`,
`count_halves`, `excludes_of_basin`, `Covers`, `covers_of_counts`, `spread`, in the namespace `ForcedBasin`, and the
five theorems at widths 14 and 16. Each count is one kernel computation of all the rounds; the module builds in about
10 seconds with a peak near 2.1 GB, its checks one at a time (`Elab.async false`).

## Relation to the kit

The kit states entry for every finite right half as its open `Rule30Ether.Absorption` and uses it in
`least_period_four_of_absorption`; its family and wall list are used as they are. Its bit-parallel images
(`Rule30WhiteEndNine.fimage`, and `Rule30FastImage` on its main branch) compute forward images; neither the kit nor its
equivalent forms have the all-successor test or a basin. The strip step is the kit's
`Rule30StripCertificates.stripStep`.
