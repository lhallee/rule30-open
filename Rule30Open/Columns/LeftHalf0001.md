---
title: No left half within depth 88 keeps the kit's left-half pattern for 0001
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.LeftHalf0001
headline: [c3_0001_bounded, c3_0001_small, c3_0001_depth, c3_0001_of_checks]
kit: refines
kit_modules: [Rule30PeriodFourSkeleton, Rule30ZeroBoundaryLanes, Rule30ZeroBoundary, Rule30DrivenLeft]
evidence: [computations/held_map.py]
---

# No left half within depth 88 keeps the kit's left-half pattern for 0001

The kit reduces least period four of the center column to three open statements about the left half alone, one for
each word
([`Rule30PeriodFourSkeleton.C3`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30PeriodFourSkeleton.lean),
joined by `least_period_four_of_C3`). This module proves the case of `C3 w0001` in which the half, at the time from
which it keeps the pattern, has no black cell beyond depth 88. [The left-half
finding](../../findings/columns/left-half-c3.md) computes the same for every half of at most 80 cells, from time 0.

## Statement

A left half $s$ (cells $-1, -2, \dots$) runs as Rule 30 beside the kit's effective boundary for $0001$, which is the
white column (`effWord_0001`); $L_k(p)$ is the cell $p$ at time $k$. Column $-1$ *keeps the pattern* $P_{0001}$ from
time $K$ if for every $k \ge K$ it is white when $k \equiv 0$ or $2 \pmod 4$ and black when $k \equiv 3$; at
$k \equiv 1$ it is free. `C3 w0001` says that no finitely supported half keeps $P_{0001}$ from any time.

1. **The bounded case** (`c3_0001_bounded`). If column $-1$ keeps $P_{0001}$ from time $K$, then $L_K(-d)$ is black
   for some $d > 88$.
2. **Small halves** (`c3_0001_small`). If $s$ is white left of cell $-M$ and $M + K \le 88$, column $-1$ does not keep
   $P_{0001}$ from time $K$. In particular no half of at most 88 cells keeps it from time 0.
3. **Every phase** (`c3_0001_depth`). In the kit's zero-boundary form, with the phase at time $t$ read as
   $(t + \varphi) \bmod 4$: for each $\varphi$, every start white beyond depth 88 has column $-1$ off the pattern at
   some time $t < 114$.
4. **The checker** (`c3_0001_of_checks`). For any depth $W$, number of levels $K$ and phase $\varphi$: if every chunk
   passes `checkC W K φ n`, every start white beyond depth $W$ is off the pattern at some time below $K$.
5. **Sharpness** (`sharp20_0` to `sharp20_3`). At depth 20 the least $K$ that passes is one more than the latest first
   failure over the halves of at most 20 cells: 28, 27, 29 and 28 by phase.

## Argument

1. **Sideways reconstruction** (the kit). Column $-1$, $y(t)$, determines the whole zero-boundary half: the cell at
   depth $d$ and time $t$ is `recon y d t` (`history_eq_recon`). The cells with depth plus time equal to $k$ form
   antidiagonal $k$; antidiagonal $k + 1$ is a running XOR over antidiagonals $k$ and $k - 1$, started from $y(k)$,
   and its last entry is the start's cell at depth $k + 1$.
2. **One free reading in four.** The pattern fixes $y(t)$ at three phases in four. At a free time $t$ with
   $t + 1 \le W$ the reading is a free bit; there are $\lfloor (W + 2 + \varphi)/4 \rfloor - \lfloor \varphi/2 \rfloor$
   of them (`freeCount`), 22 at depth 88 in every phase. At a later free time the start's cell at depth $t + 1$ is
   white, and that fixes $y(t)$.
3. **The lanes.** The checker runs $2^n$ choices of the first $n$ free readings at once, one per bit position of a
   natural number, so each step is a bitwise operation on big numbers; a chunk index fixes the other free readings.
   At a fixed phase with $t + 1 > W$, a lane dies when the start's cell at depth $t + 1$ comes out black (`stepC`,
   `runC`).
4. **Soundness** (`runC_sound`). A start white beyond depth $W$ that keeps the pattern through time $K - 1$ is followed
   by its own lane, which never dies. So if every lane of every chunk dies within $K$ levels, every such start leaves
   the pattern before time $K$ (`c3_0001_of_checks`).
5. **The checks.** At depth 88 with $n = 18$: 16 chunks per phase, 64 in all, each of $2^{18}$ lanes and 114 levels,
   evaluated by the kernel (`decide +kernel`).
6. **The kit's form.** The kit's effective boundary for $0001$ is white (`drive_0001`), so its driven left half is the
   zero-boundary half (`L_eq_zrow`). A half that keeps the pattern from time $K$ gives, at time $K$, a start that
   keeps it from phase $K \bmod 4$ (`zrow_shift`, `fits_0001`), which step 5 forbids when that start is white beyond
   depth 88 (`c3_0001_bounded`). The support grows by at most one cell per step (`zrow_fin`), which gives
   `c3_0001_small`.

## The numbers

`python -m computations.held_map 88 --tree c3 --word 0001` follows the tree of readings the pattern allows
([computations/held_map.py](../../computations/held_map.py), `tree_failures`) and finds the latest first failure
over the halves of at most 88 cells at steps 112, 109, 113 and 113 by phase, so 114 levels suffice; in each phase
4,194,304 of them keep the pattern through step 87, and the search takes about seven minutes. At depths 20 and 24 the
least number of levels that passes the Lean check, in each phase, is one more than the search's latest failure;
`sharp20_0` to `sharp20_3` record depth 20. The module builds in about 70 seconds with a peak below 1 GB.

## What it covers

Each four cells of depth add one free reading, so the kernel's work doubles every four cells and grows further with
the number of levels: phase 0 alone at depth 92 took 53 seconds with 135 levels, so the four phases there need about
three minutes, and depth 100 over ten. The latest failure keeps growing past the half's length, by about a third of the
length ([the left-half finding](../../findings/columns/left-half-c3.md)), so a check of this kind settles bounded
cases only. `C3 w0001` asks for every finite half, whatever its depth at time $K$, and needs an argument that
uses the finiteness of the half.

## Relation to the kit

The checker is the kit's `Rule30ZeroBoundaryLanes`, built for its period-two statement `Q01`, which it proves for
every start of width at most 52 (`Rule30ZeroBoundaryWidth52`); here the period-two pattern, black at the even times, is
replaced by the pattern of $0001$ with a phase. `scanN`, `mapX`, `yFree`, `pat`, `pack`, `AD`, `level`,
`history_eq_recon`, `L_eq_zrow`, `zrow_shift` and `zrow_fin` are the kit's. The kit proves no case of `C3`, and its
equivalent forms do not mention it.

## Lean

`Rule30Open.Columns.LeftHalf0001`: `KeepsC3`, `freeIdx`, `freeTime`, `freeCount`, `stepC`, `runC`, `checkC`,
`runC_sound`, `c3_0001_of_checks`, `ChunksC` with `chunksC_one` and `chunksC_append`, the 64 checks `chunk<φ>_<c>`
with `chunks0` to `chunks3`, `c3_0001_depth`, `sharp20_0` to `sharp20_3`, `drive_0001`, `fits_0001`,
`c3_0001_bounded` and `c3_0001_small`. Elaboration is sequential, so the checks do not stack their memory.
