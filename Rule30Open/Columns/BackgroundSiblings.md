---
title: Entry into 41 more carried traps is false, refuted by the same wall carried farther into its background
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.BackgroundSiblings
headline: [nine8_not_absorption_sibling, el1_9_not_absorption_sibling, tw0_29_not_absorption_sibling, th0_11_not_absorption_sibling, fo0_13_not_absorption_sibling]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30Ether]
evidence: [computations/background_prefix.py]
---

# Entry into 41 more carried traps is false, refuted by the same wall carried farther into its background

The wall modules carry one wall leftward along its chain and take, for each block the chain reaches, the trap at the
least distance $d$ that reaches it ([NineTraps](NineTraps.md), [TenTraps](TenTraps.md), ElevenTraps to
[FourteenTraps](FourteenTraps.md)). The chain becomes periodic: from a distance $s$ on, column $D + q$ is column $D$,
and the columns from $s$ on are a background periodic in time and space
([the backgrounds](../../findings/columns/space-time-backgrounds.md)). When $s > 0$ the background's own half beside a
column that repeats a block is in the block's trap at none of its labels, and the same wall carried farther, into the
background, gives a trap of the same block apart from the first. So entry into the first is false. This refutes entry
into 107 traps of the wall modules, 41 of them not refuted before, all checked in Lean.

## Statement

Let $T_D$ be the wall carried to distance $D$ (`carried` in
[computations/lock_chain.py](../../computations/lock_chain.py)): the chain's columns $D - 1, \dots, 0$ in front of every
state of the wall, a labelled trap of $D + w$ cells for the block of column $D$, $w$ the wall's width.

1. **The sibling is closed** (`sib_<trap>_closed`): for each refuted trap $T_d$, a $T_D$ of the same block with $D - s$
   at least the width $d + w$ of $T_d$ passes `WTrap.closedCheck`.
2. **The separation** (`sib_<trap>_cut`, `_holds`, `_avoids`): the states of $T_d$, as a set of windows of
   [ReachRefuted](ReachRefuted.md), hold them all, and no state of $T_D$, cut to $d + w$ cells, is in it at a label of
   the same phase.
3. **Entry is false** (`<trap>_not_absorption_sibling`): the right half of state 0 of $T_D$, white beyond, driven from
   the phase of that state's label, never enters $T_d$, by `not_absorption_fwd`.

| Module | Wall | $s$ | $q$ | Traps | Blocks of the background | Refuted by a sibling | Not refuted before | Siblings in Lean |
|---|---|---:|---:|---:|---:|---:|---:|---|
| NineTraps | $001011111$ | 10 | 135 | 21 | 13 | 13 | 6 | 107 to 123 cells, 233 states |
| TenTraps | $0000010001$ | 0 | 155 | 25 | 25 | 2 | 0 | |
| ElevenTraps | $00000011011$ | 23 | 143 | 33 | 13 | 13 | 1 | 90 cells, 313 states |
| ElevenTraps | $00110100111$ | 9 | 275 | 24 | 19 | 19 | 8 | 50 to 71 cells, 103 states |
| TwelveTraps | $001011100111$ | 41 | 60 | 37 | 1 | 1 | 1 | 113 cells, 119 states |
| TwelveTraps | $000110110011$ | 0 | 138 | 36 | 36 | 0 | 0 | |
| TwelveTraps | $000010011111$ | 7 | 138 | 10 | 5 | 5 | 0 | |
| ThirteenTraps | $0001110010011$ | 1 | 689 | 53 | 53 | 53 | 24 | 80 to 117 cells, 213 states |
| FourteenTraps | $00011100101011$ | 0 | 728 | 101 | 101 | 1 | 1 | 90 cells, 225 states |

A block of the background is a trap whose block repeats in some column of the background; the others are reached only
on the chain's way from the wall to its background.

The refuted traps not refuted before are `nine8`, `nine9`, `nine12`, `nine13`, `nine16`, `nine20`; `el0_35`, `el1_9`,
`el1_14`, `el1_24`, `el1_25`, `el1_26`, `el1_27`, `el1_28`, `el1_30`; `tw0_29`; `th0_11`, `th0_13`, `th0_16`, `th0_19`,
`th0_22`, `th0_23`, `th0_25` to `th0_30`, `th0_32` to `th0_35`, `th0_38`, `th0_39`, `th0_40`, `th0_42`, `th0_44`,
`th0_46`, `th0_47`, `th0_48`; and `fo0_13`. The other 66 were already refuted, by the tests of reach and of halves apart
or by wider traps ([what failed](../../negative-results/columns/missed-traps.md)).

## Argument

1. **The background half is outside the trap.** Let column $x \ge s$ of the background repeat the block of $T_d$. The
   background half beside it, driven by the block, stays the background forever, so it is periodic in time. Its first
   $d + w$ cells, at each label, are compared with the states of $T_d$ at the same phase (`inside_counts` in
   [computations/background_prefix.py](../../computations/background_prefix.py)). For every wall with $s > 0$ and every
   trap whose block is a column of the background, they match at no label. For the walls with $s = 0$ they match at
   every label beside the columns aligned with $d$ modulo the background's symmetries, and at none beside the other
   columns of three blocks, $0001001101$ and $0001010111$ of period 10 and $00010010110111$ of period 14.
2. **The sibling.** Take $D = x + i q$ with $D - s \ge d + w$, the least over the columns $x$ outside. The first
   $D - s$ columns of $T_D$ are the background beside $x$, so every state of $T_D$, cut to $d + w$ cells, is the
   background half beside $x$ at its label: never a state of $T_d$ at that phase. $T_D$ is closed, since carrying keeps
   a trap closed, and a half in it stays in it. The kernel checks the closure, the cut and the separation, so neither
   the chain nor the search is trusted (`lean_siblings`).
3. **A finite half.** State 0 of $T_D$ is a window of $D + w$ cells; as a right half, white beyond, it is finitely
   supported and in $T_D$ at step 0, so it never enters $T_d$.

## What it covers

The refutation is of entry into one trap. The siblings themselves are traps of the block, and the family does not stop:
for the four blocks tested (`nine8` with $D$ = 64, 199, 334; `el1_9` with 34, 309, 584; `th0_11` with 64, 753, 1,442;
and, at $s = 0$, `ten1` against 18, 173, 328), the trap and its siblings are pairwise apart as wholes for $s > 0$
(`apart_closed` both ways), so entry into any one of them, or into one of a list drawn from them, is false as well. At
$s = 0$ the siblings of one column class are nested instead (each holds the next one's cut), as the traps carried along
the kit's ether are members of one family. If the apartness goes on for every $i$, which is untested beyond $i = 2$, a
block of the background with $s > 0$ comes down to entry into some trap of the block (`WTrap.AbsorptionAny` of
[Traps001](Traps001.md)) or into an infinite family such as $\{T_{x + i q}\}$, the form of the kit's ether-and-wall
family, and not to entry into a finite list of carried traps. Whether these blocks keep another trap that passes the
tests of reach (natural traps of [NaturalTrapsWalls](NaturalTrapsWalls.md), census traps) is not rechecked here, so the
coverage table is not updated by this module.

## Relation to the kit

The kit refutes entry into its period-four certificates the same way: a right half that stays in a deeper member of its
ether-and-wall family never enters the certificate (`Rule30Ether.never_enters_S0001`). Here the deeper member is the
wall carried farther into its background. The kit has no trap for a block of period 9 to 14.

## Lean

`Rule30Open.Columns.BackgroundSiblings`: for each of the 41 traps, `sib_<trap>`, `sib_<trap>_closed`, `sib_<trap>_cut`
with `_holds` and `_avoids`, and `<trap>_not_absorption_sibling`. It builds in about 30 seconds with a peak below
0.5 GB. The tables come from `python -m computations.background_prefix --lean-siblings`.

## Reproduce

```bash
python -m computations.background_prefix --siblings
python -m computations.background_prefix --lean-siblings
```

The first lists, for each wall module, the traps that a background sibling refutes, checks each with `apart_closed`, and
says which were refuted before; it takes a few seconds.
