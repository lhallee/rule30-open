---
title: For 2 ≤ a ≤ 10 the a leftmost cells of the cone are pairwise distinguishable at every t ≥ a + 2, from a threshold on by white and single black cell completions, so left-to-right ordered decision diagrams of the center have width 2^a at level a for every such t
category: complexity
problems: [3]
status: proved
lean: Rule30Open.Complexity.LateSeedCut
headline: [late_seed_cut, late_seed_factor, late_seed_width, left_cut_every, left_cut_width_every, lateSep_all,
  lateSep_step, lateCen_shift, lateSep_of_check, nevo_two_pow, edgeFrame_periodic, nevo_mod, lateCen_eq]
kit: new
kit_modules: [Rule30Diagonals, Rule30FiniteDiagonals, Rule30Equivalents.AutomatonGroup]
evidence: [computations/late_seed_cut.py, tests/test_late_seed_cut.py]
---

# For 2 ≤ a ≤ 10 the a leftmost cells of the cone are pairwise distinguishable at every t ≥ a + 2, from a threshold on by white and single black cell completions, so left-to-right ordered decision diagrams of the center have width 2^a at level a for every such t

A row is a map from the integers to colors, one step of Rule 30 is $x'_j = x_{j-1} \oplus (x_j \lor x_{j+1})$, and
$c_t(x)$ is cell 0 after $t$ steps, a function of the cells $x_{-t}, \dots, x_t$. Write $\mathrm{splice}_b(x, z)$ for
the row equal to $x$ left of cell $b$ and to $z$ from cell $b$ on (`spliceAt` of [LeftCut](LeftCut.md)), and $\delta_m$
for the row white except a black cell at $m$ (`fun j => single (j - m)`).

## Statement

Let $2 \le a \le 10$, and let $t_A(a) = 3, 4, 6, 7, 10, 12, 14, 17, 17$ (`lateStart`) and $R_a = 0, 1, 3, 4, 7, 7, 8,
11, 14$ (`lateR`) for $a = 2, \dots, 10$.

- `late_seed_cut`: for every $t \ge t_A(a)$, if the rows $x$ and $y$ differ at some cell $i$ with
  $-t \le i \le -t + a - 1$, then $c_t(\mathrm{splice}_{-t+a}(x, z)) \ne c_t(\mathrm{splice}_{-t+a}(y, z))$ for $z$
  white, or for $z = \delta_m$ with $m = t - (a \bmod 2) - 2R - d$ for some $0 \le R \le R_a$ and $d \in \{0, 1\}$ with
  $R + d + \lceil a/2 \rceil \le t$ (then $-t + a \le m \le t$: the black cell is in the cone, right of the cut).
- `late_seed_factor`, `late_seed_width`: for every $t \ge t_A(a)$, if
  $c_t(\mathrm{splice}_{-t+a}(x, z)) = G(F(x), z)$ for all rows $x, z$, then $F(x) = F(y)$ forces $x_i = y_i$ for
  $-t \le i < -t + a$, and the rows carrying the bits of $P < 2^a$ on $x_{-t}, \dots, x_{-t+a-1}$ have pairwise
  different states: $S$ has at least $2^a$ elements.
- `left_cut_every`, `left_cut_width_every`: the same distinguishability, by some completion, and the same width, for
  every $t \ge a + 2$: [LeftCut](LeftCut.md) gives $a + 2 \le t \le 17$ and the late seeds give $t \ge t_A(a)$, and
  $t_A(a) \le 17$.

So the number $N_{\mathrm{L}}(t, a)$ of distinct functions that the center leaves after the $a$ leftmost cells of the
cone are fixed is $2^a$ for every $t \ge a + 2$ and $2 \le a \le 10$. Read as models of computation, as in
[LeftCut](LeftCut.md): an ordered binary decision diagram that reads $x_{-t}, x_{-t+1}, \dots$ in this order and
computes $c_t$ has at least $2^a$ nodes at level $a$, for every $2 \le a \le 10$ and every $t \ge a + 2$, and a one-way
protocol from the holder of the $a$ leftmost cells costs exactly $a$ bits. Every linear rule has at most 2 at every
level. LeftCut has these bounds for $t \le 17$ only.

The thresholds are those of the family: for $a + 1 \le t < t_A(a)$ the white and single black cell completions do not
separate the $2^a$ settings, except at $a = 7$, $t = 10$ (computed by `computations/late_seed_cut.py`, `--below`, with
every completion that has one black cell in the cone).

## Argument

**The number frame.** The cone is the number $N = \sum_k x_{-t+k} 2^k$, one step is $\mathrm{nstep}(N) = N \oplus ((N
\gg 1) \lor (N \gg 2))$ in a frame that moves one cell right, and $c_t$ is bit 0 of $\mathrm{nevo}(N, t)$ (`nstep`,
`nevo` and `evo_rowN` of [ConeScreening](ConeScreening.md); `evolve_splice_late`). The $a$ left cells are $P = N \bmod
2^a$ and the completion is $r = N \gg a$: $N = 2^a r + P$ (`lateCen`).

**1. The cut** (`nevo_shiftRight`, `nevo_mod`). The completion evolves on its own, $\mathrm{nevo}(N, s) \gg a =
\mathrm{nevo}(r, s)$, since bit $k$ of a step reads bits $k, k+1, k+2$ only. The left cells $A_s = \mathrm{nevo}(N, s)
\bmod 2^a$ follow $A_{s+1} = \mathrm{nstep}(2^a e_s + A_s) \bmod 2^a$ (`aliceStep`, `aliceRun`), driven by the letters
$e_s = \mathrm{nevo}(r, s) \bmod 4$, the completion's two cells next to the cut. This is the frozen-boundary automaton
of the kit's `AutomatonGroup` (`PhiS 0`, `PhiS 1`, `PhiS 3` for the letters 0, 2 and 1 or 3), written with the bits in
the other order.

**2. The horizon** (`nevo_local`, `lateCen_eq`). Bit $j$ of $\mathrm{nevo}(M, n)$ reads only bits $j, \dots, j + 2n$ of
$M$. With $n = \lceil a/2 \rceil - 1$, so that $2n + 1 \le a$, the center at $t = T + n$ is bit 0 of $\mathrm{nevo}(A_T,
n)$: the letters from time $T$ on never reach it.

**3. A black cell is the left-edge frame, shifted** (`nevo_two_pow`). Let $Z_0 = 1$ and $Z_{s+1} = 4 Z_s \oplus (2 Z_s
\lor Z_s)$ (`edgeFrame`): bit $j$ of $Z_s$ is the single black cell after $s$ steps, $j$ cells right of its left edge.
Then $\mathrm{nevo}(2^\mu, s) = (2^\mu Z_s) \gg 2s$, by induction, so the letters of the completion $r = 2^\mu$ are bits
$2s - \mu$ and $2s - \mu + 1$ of $Z_s$, and white while $2s + 2 \le \mu$ (`seed_letter_zero`). The late seed $(R, d)$ at
$t$ is $\mu = 2(t - \lceil a/2 \rceil - R) - d$ (`seedPos`): it reaches the cut diagonal at time $t - \lceil a/2 \rceil
- R - d$ and the center reads its letters at depth at most $2R + 2$.

**4. The left edge repeats** (`edgeFrameStep_mod`, `edgeFrame_periodic`). Bit $j$ of $Z_{s+1}$ reads bits $j - 2, j - 1,
j$ of $Z_s$, so the low $J$ bits follow a map of their own, and one repetition $Z_{s_0 + p} \equiv Z_{s_0} \pmod{2^J}$
gives $Z_{s+p} \equiv Z_s$ for every $s \ge s_0$. The kernel checks it for $(J, p, s_0) = (3, 1, 2), (5, 2, 2), (9, 4,
2), (11, 4, 6), (17, 4, 16), (19, 4, 20), (25, 4, 27), (31, 8, 33)$ (`edge_period_3` to `edge_period_31`); each $s_0$ is
the least one, and $p$ the least period, by `computations/late_seed_cut.py`.

**5. The shift** (`seed_letter_shift`, `lateCen_shift`, `lateCen_white`). If $2R + 3 \le J$ and
$t \ge t_0 = s_0 + R + 1 + \lceil a/2 \rceil$, then for every $P < 2^a$
$$c_{t+p}(2^a \cdot 2^{\mu + 2p} + P) = c_t(2^a \cdot 2^{\mu} + \mathrm{nevo}(P, p)),$$
the seed $(R, d)$ at $t + p$ being $2p$ cells further right. The seed at $\mu + 2p$ is white next to the cut for the
first $p$ steps, so the left cells run on their own to $\mathrm{nevo}(P, p)$; after that its letters at time $i + p$
are those of the seed at $\mu$ at time $i$, for every $i$ before the horizon: both are white, or both are bits of
$Z_{i+p}$ and $Z_i$ at depth at most $2R + 2 < J$ from a time $i \ge t - \lceil a/2 \rceil - R - 1 \ge s_0$ on. With the
horizon, the centers agree. The white completion gives the same identity at every $t$.

**6. Induction on $t$** (`nstep_inj`, `nevo_inj`, `lateSep_step`, `lateSep_all`). On $a$-bit numbers $\mathrm{nstep}$ is
injective (bit $j$ of $\mathrm{nstep}(P)$ is $P_j$ changed by the bits above it), so $P \mapsto \mathrm{nevo}(P, p)$ is.
Call $t$ *separated* (`LateSep`) when every two settings $P \ne Q$ have different centers at some probe: white, or a
late seed $(R, d)$ with $R \le R_{\max}$, $d \le 1$, inside the cone. If $t \ge t_0$ is separated, so is $t + p$: the
probe that separates $\mathrm{nevo}(P, p)$ and $\mathrm{nevo}(Q, p)$ at $t$ separates $P$ and $Q$ at $t + p$, by 5. So
separation at $t_A \le t < t_0 + p$ gives every $t \ge t_A$.

**7. The finite checks** (`nevo_split_white`, `lateCen_suffix`, `lateCheck`, `lateSep_of_check`). Let $m = \min(t,
\lceil a/2 \rceil + R_{\max} + 1)$ and $k = t - m$. Every probe is white next to the cut before time $k$, so the row
splits there, $\mathrm{nevo}(2^a r + P, k) = 2^a\,\mathrm{nevo}(r, k) + \mathrm{nevo}(P, k)$, and $c_t(2^a r + P)$ is
the center after $m$ steps of $2^a\,\mathrm{nevo}(r, k) + v$ with $v = \mathrm{nevo}(P, k)$. Since $P \mapsto v$ is
injective, it suffices that the probes separate the $2^a$ values of $v$. The kernel runs the $a$ left cells of all $2^a$
values at once in one number of $a$ blocks of $2^a$ bits, bit $v$ of block $j$ being bit $j$ of $v$: a step is
$\mathrm{nstep}$ with blocks for bits, and the completion's two cells next to the cut enter as two blocks of all ones or
all zeros (`bobPack`, `packStep`, `packRun`, `packRun_testBit`, `lateCol_testBit`). The columns split the mask of all
values as in [LeftCut](LeftCut.md) (`refineMasks`, `separates_of_refineMasks`). The checks `late_checks_2` to
`late_checks_10` cover $t_A(a) \le t < t_0 + p$ with $R_{\max} = R_a$ and $J = 2R_a + 3$, from 2 values of $t$ for $a =
2$ to 44 for $a = 10$; the module builds in about 40 seconds of processor time.

**Rows** (`evolve_eq_evo`, `evolve_splice_late`). The center of a spliced row is that of the number of its cone, by
`evo_local` and `evo_rowN`; the white completion is $r = 0$ and $\delta_m$ is $r = 2^\mu$ with $m = -t + a + \mu = t -
(a \bmod 2) - 2R - d$.

## What it means

LeftCut proves $N_{\mathrm{L}}(t, t - 2) = 2^{t-2}$ for $t \le 17$, and [the left
cut](../../negative-results/complexity/left-cut.md) shows that the exact statement at $k = t - 2$ fails for $18 \le t
\le 22$ ($t = 18$ in Lean, the rest by computation; open for $t \ge 23$), because alternating stripes ending next to the
cut fix the center. This module fixes the number $a$ of cells instead and proves $N_{\mathrm{L}}(t, a) = 2^a$ at every
$t \ge a + 2$ for $2 \le a \le 10$: lower bounds on $N_{\mathrm{L}}$ that hold for every $t$. The probes sit near the
right end of the cone, at distance about $2t$ from the cut, and enter through the left edge of a single black cell,
which is eventually periodic at bounded depth (step 4); this is how the argument avoids the collapse of every window of
fixed width next to the cut at $t = 2^j$ ([LeftCutRank](LeftCutRank.md), `center_two_pow`).

The bound is a constant for each $a$, so it does not by itself give width growing with $t$. Exponential width
$2^{\Omega(t)}$ at level $\Omega(t)$ would follow from a uniform version: for every $a$ the late seeds with $R \le c\,a$
separate the $2^a$ settings in each class of $t$ modulo the period, and the onset $s_0$ of the low $2ca + 3$ bits of the
left edge grows at most linearly in $a$, a statement about the frozen-boundary automaton and the eventual blocks of the
left edge only. The first part holds for $2 \le a \le 13$ with $c = 1.6$ (here and in
[LateSeedCutWide](LateSeedCutWide.md)); the onsets are computed for $J \le 64$ (`--edge 64`) and are at most 2985 for $J
\le 399$ (kit main's `Rule30LeftAntiPeriod`). Nothing here bears on the single black cell's own center column, which is
one row.

The pinned kit's `Rule30ColumnSeparation.left_bits` and `left_periodic` prove that the low 20 bits of the single cell's
left edge repeat with period 4 from time 20 (`left_cycle` is `edgeFrame (20 + 4) % 2^20 = edgeFrame 20 % 2^20` in this
module's terms), which is step 4 for $J \le 20$, that is $a \le 8$. Kit main's
`Rule30LeftAntiPeriod.D_zero_to_three_hundred_ninety_eight_eq_fullGate8` with
`Rule30TraceEdge.osc3State_add_eq_iter_mod_eight` gives period 8 for the low 399 bits from time 2985, which covers $J =
25$ and 31 with a later onset. The kernel checks `edge_period_J` give the least onsets, which set the range of the
finite checks. The kit's bound for every left diagonal, period $2^j$ (`Rule30Diagonals.D_periodic`; uniform onsets `2^i
- 1` in `Rule30FiniteDiagonals.Ld_uniform_period`), is far too weak for step 4. Its `AutomatonGroup` has the
frozen-boundary steps $\Phi_s$. It has no decision diagram, branching program or communication bound for Rule 30, so the
separation statement and its proof are new; step 4 overlaps the kit's left-edge results above.

## Reproduce

```bash
python -m computations.late_seed_cut --scan 2 10 --tmax 80    # t_f(a) = t_A(a) - 1 and R_a, a <= 10 (a few seconds)
python -m computations.late_seed_cut --edge 64                # periods and onsets of the low J bits of the left edge
python -m computations.late_seed_cut --lean 2 10 --check 2 10 # the parameters and the mirrored kernel checks (a few seconds)
python -m computations.late_seed_cut --below 2 10 --tmax 80   # below t_A(a): white and every single black cell
```
