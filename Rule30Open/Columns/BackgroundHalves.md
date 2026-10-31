---
title: The right half beside a 0001 column of the 80-cell background is in the ether-and-wall family at no time
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.BackgroundHalves
headline: [background_half_not_inFamily, background_half_not_absorbed, background_half_8, drv_eq, prefix_short]
kit: new
kit_modules: [Rule30Ether]
---

# The right half beside a 0001 column of the 80-cell background is in the ether-and-wall family at no time

Rule 30 has a background of period 8 in time and 80 cells in space ([the backgrounds](../../findings/columns/space-time-backgrounds.md)).
Eight of its columns repeat $0001$. The right half beside such a column, driven by $0001$, is the background
itself. This module proves that this half is never in the family of the kit's
[`Rule30Ether`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Ether.lean):
ether on columns $1, \dots, k$ with $j_0 + k \equiv 2 \pmod 7$, followed by one of the 109 wall states
(`InFamily`). It holds at every time and for every alignment of the ether, not only the two alignments, $(5, 0)$ and
$(6, 0)$, of the kit's conjecture for $0001$.

## Statement

- `colOK x0 ph0` says column $x_0$ of the background reads $0001$ from phase $ph_0$, and `colOK_list` lists the
  pairs: columns $8, 18, \dots, 78$, each from two phases, 16 pairs in all.
- `drv_eq`: for such a pair the kit's driven half `drv`, with column 0 equal to $0001$ and the half at time 0 equal to
  the background to the right of column $x_0$, reads the background at every time:
  $\mathrm{drv}(t, p) = B(x_0 + p, t + ph_0)$, with $B(j, \varphi)$ column $j$ of the background at phase $\varphi$. So
  it has period 8 in time (`Fb_period`) and period 80 in space (`Fb_space_period`).
- `prefix_short`: for every such pair, every phase $\varphi < 8$, and every alignment $j < 7$, $s < 4$ of the ether, the
  half differs from $\mathrm{ether}(j + c, \varphi + s)$ at some column $c \le 8$ (all times and alignments follow by
  periodicity in `not_inFamily`). The half carries the ether on at most its first 7 columns, whatever the alignment.
- `background_half_not_inFamily`: `InFamily` fails for the driven half, for all $j_0$, $s$ and $t_1$.
- `background_half_not_absorbed`: with drive phase $\varphi = 0$ (the phase at which the drive matches the column), the
  conclusion of the kit's `Absorption` for the alignments `A0001` fails for it.
- `background_half_8`: an `x : Nat → Bool` with black cells at arbitrarily large columns (`background_half_unbounded`)
  whose driven half, with drive phase $\varphi = 0$, is in the family at no time and no alignment.

## Argument

1. **The half is the background.** The background is a table of 80 columns by 8 phases, stored as a 640-bit number.
   `ring_rule_small` checks that column $j + 1$ at phase $\varphi + 1$ is $\mathrm{rule}(B(j,\varphi), B(j+1,\varphi),
   B(j+2,\varphi))$ for the 640 pairs of residues, and `ring_rule` extends it to all $j$ and $\varphi$. The column
   $x_0$ reads $0001$ from $ph_0$ (`colOK_spec`). Induction on $t$ then matches the driven half to the table
   (`drv_eq`).
2. **A short ether prefix.** Membership at time $t_1$ with alignment $(j_0, s)$ needs $\mathrm{ether}(j_0 + p, t_1 + s)$
   on columns $p = 1, \dots, k$, and the ether depends on $j_0 \bmod 7$ and $(t_1 + s) \bmod 4$, the half on $t_1 \bmod 8$.
   So $7 \cdot 4 \cdot 8 = 224$ cases cover every time and alignment, for each of the 16 pairs. In every case the half
   differs from the ether at one of the first 8 columns (`prefix_short`, a kernel computation). Hence $k \le 7$.
3. **No wall.** For $k \le 7$ with $(j_0 + k) \bmod 7 = 2$ and the ether on columns $1, \dots, k$, the 13 cells after
   column $k$ are not one of the wall states with the right phase (`wall_absent`, a kernel computation over the same
   cases).
4. **Together.** If the half were in the family with some $k$, step 2 gives $k \le 7$ and step 3 excludes the wall
   (`not_inFamily`). The time, $j_0$ and $s$ are reduced modulo 8, 7 and 4 on the way.

The bound of 7 columns holds for all 28 alignments of the ether, not only the kit's.

## In Lean

`ringNat` is the table, `ringBit j ph` reads it, and `Fb x0 ph0 t p` is the half beside column $x_0$. The kernel
computations (`ring_rule_small`, `colOK_list`, `prefix_short`, `wall_absent`) are `decide +kernel`; the module builds in about a minute. No `sorry`, no `native_decide` and no axioms
beyond `propext` and `Quot.sound`. The table is the ring that
[computations/background_halves.py](../../computations/background_halves.py) finds for period 8 and 80 cells;
`ring_rule_small` re-checks that it is a Rule 30 orbit, and `colOK_list` that it has these columns.

## What it does not say

The half has infinitely many black cells, and the kit's `Absorption` is about finitely supported halves, so this is not
a counterexample to it. Truncations of the half to $n$ cells do enter the family (a computation, not proved here),
which is the kit's `Absorption` at work. Nothing here bears on whether $0001$ can be the tail of the center column.

## Relation to the kit

The kit defines the family (`InFamily`) and the driven half (`drv`), proves that finite halves of a particular
form stay out of a given trap forever (`never_enters_S0001`, `config_pure_ether`), and states the absorption
conjecture. `InFamily` occurs only in `Rule30Ether`, `Rule30EtherSingleCell` (with its Aux and Cases) and
`Rule30EtherThree`, and none of them treats a background of 80 cells.
