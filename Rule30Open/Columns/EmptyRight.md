---
title: Against a right half of at most six cells no center column repeats a word of period four
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.EmptyRight
headline: [smallRight_0001, smallRight_0011, smallRight_0111, emptyRight_001, no_finite_of_family, no_finite_of_ptrap]
kit: refines
kit_modules: [Rule30Ether, Rule30EtherThreeTrap, Rule30EtherThreeReach, Rule30Coupled, Rule30FiniteMaskedJen]
evidence: [computations/absorption.py, computations/right_half.py, computations/coupled.py]
---

# Against a right half of at most six cells no center column repeats a word of period four

No configuration with finitely many black cells whose cells right of column 6 are white has a center column that
repeats $0001$, $0011$ or $0111$ from time 0, in any phase and whatever its left half holds (`smallRight_0001`,
`smallRight_0011`, `smallRight_0111`). With a white right half the same holds for $001$ (`emptyRight_001`). The white
right half is the first case of the coupled question for a word, and for period two it is the kit's milestone
[`Rule30PeriodTwoSideways.CQ01Empty`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30PeriodTwoSideways.lean),
which is open; for these four words it is settled here, and for the words of period four so are the 63 other right
halves of at most six cells.

## Statement

For a word $w$ of length 4, a phase $\varphi$ and a width $n$, `SmallRight w n φ` says that no finite configuration $y$
with $y(p) = 0$ for every $p > n$ has center column $c(t) = w[(t + \varphi) \bmod 4]$ at every time $t \ge 0$.
`EmptyRight w φ` is the case of a white right half, and `EmptyRight3` the same for a word of length 3. `SmallRight`
holds with $n = 6$ for the three words of period four and every $\varphi$, so `EmptyRight` does too (`emptyRight_0001`
and its siblings); `EmptyRight3` holds for $001$ and every $\varphi$.

## Argument

1. **The right half does not see the left.** In any configuration the cells right of the center evolve as the right
   half driven by the center column (`Rule30Coupled.right_eq_drv`). With the center fixed to repeat $w$, the right half
   is one explicit evolution of its cells at time 0, the same for every left half.
2. **It enters a trap.** For the words of period four the trap is the kit's ether-and-wall family
   (`Rule30Ether.InFamily`): for an alignment $(j_0, s)$ of $w$ with the ether, columns $1$ to $k$ carry the ether,
   column $k$ is a $B_3$ column, and columns $k + 1$ to $k + 13$ form one of the kit's 109 wall states. Each of the 64
   right halves of at most six cells is in it by step 521 in each of the 12 cases of word and phase. The steps and
   depths are listed (`entries0001_0` and the rest, from `lean_entries` in
   [computations/absorption.py](../../computations/absorption.py)), and the kernel checks each one by running the
   driven half as bit masks (`smallCheck`, `familyCheck`, through the kit's `Rule30EtherThree.rowN`); the 768 checks
   take about 10 s. The white right half enters by step 16:

   | word | alignment $(j_0, s)$ | entry step of the white half at phases 0, 1, 2, 3 | $k$ |
   |---|---|---|---|
   | $0001$ | $(6, 0)$ | 14, 13, 12, 11 | 3 |
   | $0011$ | $(0, 0)$, and $(1, 3)$ at phase 3 | 12, 11, 10, 9 | 2, and 1 at phase 3 |
   | $0111$ | $(2, 2)$ | 9, 8, 8, 16 | 0 |

   For $001$ the trap is the kit's `t001`, 815 labelled states of the 47 columns next to the center. The white right
   half is its state 597 at step 1270, 1269 or 1268 at phases 0, 1, 2 (the kit's `rowN_empty_eq` at phase 0, and
   `rowN_001_1`, `rowN_001_2` here, each a kernel computation). The three are one run: from phases 0 and 1 the center
   first reads white for two steps or one, which leaves the white half white, and then reads as from phase 2.
3. **The trap keeps column 1 periodic.** Once in the ether-and-wall family, columns $1$ to $k$ carry the ether forever,
   and whenever $B_3$ is white the first wall cell is the ether's $B_4$ (`Rule30Ether.trap_invariant`); so at every
   white time of the center, column 1 is an ether column, of period 4. In `t001` column 1 at the white times is a fixed
   function of a label that advances by one modulo 21 per step (`Rule30EtherThree.PTrap.invariant`).
4. **Masked Jen forbids that.** In a configuration with a leftmost black cell, a column with period $P$ from some time
   on and its right neighbor with period $P$ at the white times of that column cannot coexist
   (`Rule30FiniteMaskedJen.masked_jen`). The configuration has a leftmost black cell because it is finite and its
   center is black at some time. These are `no_finite_of_family` and `no_finite_of_ptrap`: the kit's
   `absorption_excludes` and `PTrap.trap`, which concern the single seed, carried to every finite configuration.

The kit's `Absorption` and `AbsorptionT` conjectures ask for step 2 for every finite right half. Each right half that
enters gives the statement for every left half, so [the absorption census](../../findings/columns/absorption-census.md),
in which all right halves of up to 20 cells enter, is the same argument by computation for those halves; here the
kernel checks it to six cells. Eight cells check too, in about 54 s, which is why they are left out of the build.

## What it means

For these four words the right half alone settles the small cases, whatever the left half does. For the other words of
period two and three it does not: column 1 of the white right half, read at the white times, has no period up to 400
times the word's length over steps 100,000 to 200,000 beside $01$ or $011$, while beside $001$ it repeats with period
21 (`right_half.locked_period`). For the alternating center the one left half that could keep the center on its word
against a white right half looks random to depth $2^{20}$
([the white right half](../../findings/period-two/white-right-half.md)), and the ether-and-wall family catches almost
none of the right halves ([the absorption route](../../negative-results/period-two/absorption-route.md)). Against a
white right half and a word of period four, that left half is periodic from depth at most 34, repeating a row of the
ether or a row that becomes one within 10 steps.

The statements concern configurations whose right half is small when the repetition starts. They say nothing about the
single seed's orbit, whose right half at time $T$ has $T$ cells.

## Lean

`Rule30Open.Columns.EmptyRight`: `SmallRight`, `EmptyRight`, `EmptyRight3` and the theorems above, with
`no_finite_of_family` and `no_finite_of_ptrap` for any finite configuration whose driven right half enters the trap,
`familyCheck`, `inFamily_of_check`, `smallCheck` and `smallRight_of_check` for the kernel computation, and
`smallRight_mod` for the phase.
