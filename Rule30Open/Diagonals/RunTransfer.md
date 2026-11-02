---
title: A white run of a left diagonal is a run on which the two diagonals before it agree, and a black run is a white run two diagonals before; so the reset cost of a diagonal is at most two more than the longest agreement run of the pair before it
category: diagonals
problems: [2]
status: proved
lean: Rule30Open.Diagonals.RunTransfer
headline: [agree_of_white_run, white_run_of_agree, white_of_black_run, black_run_of_white, blackWithin_of_disagreeWithin, whiteWithin_of_blackWithin, D_blackWithin_of_disagreeWithin, D_whiteWithin_of_blackWithin]
kit: refines
kit_modules: [Rule30Diagonals, Rule30FiniteDiagonals]
evidence: [computations/settled_words.py]
---

# A white run of a left diagonal is a run on which the two diagonals before it agree, and a black run is a white run two diagonals before; so the reset cost of a diagonal is at most two more than the longest agreement run of the pair before it

The reset bound of [SettledSlope](SettledSlope.md) charges each settled diagonal $D_i$ its cost $c_i$, one more than
its longest white run, and the obstruction to a finite certificate for the seed onsets is the same white run
([seed finite certificate](../../negative-results/diagonals/seed-finite-certificate.md)). This module says exactly what
a white run, or a black run, of one diagonal forces on the two diagonals before it.

## Statement

Let $b(i, t)$ be an array with the left-diagonal step $b(i+2, t+1) = b(i, t) \oplus (b(i+1, t) \lor b(i+2, t))$ for
$t \ge T$ (`DiagStepFrom b i T` of [DrivenSkeleton](DrivenSkeleton.md)): the single cell's diagonals $D$, the
diagonals `Ld x lo` of any row white left of a cell, or a left half driven by any center column.

- `run_white_white_iff`, `run_black_black_iff`: if $b(i+2, t) = 0$ then $b(i+2, t+1) = 0$ exactly when
  $b(i, t) = b(i+1, t)$; if $b(i+2, t) = 1$ then $b(i+2, t+1) = 1$ exactly when $b(i, t) = 0$.
- `agree_of_white_run`, `white_run_of_agree`: for $s \ge T$, diagonal $i + 2$ is white at the $r + 1$ times
  $s, \dots, s + r$ if and only if it is white at $s$ and $b(i, t) = b(i+1, t)$ at the $r$ times $s, \dots, s + r - 1$.
- `white_of_black_run`, `black_run_of_white`: diagonal $i + 2$ is black at $s, \dots, s + r$ if and only if it is black
  at $s$ and diagonal $i$ is white at $s, \dots, s + r - 1$.
- `blackWithin_of_disagreeWithin`: if diagonals $i$ and $i + 1$ differ somewhere in every $m$ consecutive times from
  $T$ on (`DisagreeWithin`), diagonal $i + 2$ is black somewhere in every $m + 1$ consecutive times from $T$ on
  (`BlackWithin` of SettledSlope).
- `whiteWithin_of_blackWithin`: if diagonal $i$ is black somewhere in every $m$ consecutive times from $T$ on, diagonal
  $i + 2$ is white somewhere in every $m + 1$ consecutive times from $T$ on (`WhiteWithin`).
- `D_blackWithin_of_disagreeWithin`, `D_whiteWithin_of_blackWithin`: the two for the single cell's diagonals.

On the periodic parts: write $g_j$, $b_j$ for the longest cyclic white and black runs of the settled word of $D_j$, and
$a_j$ for the longest cyclic run of times at which the settled words of $D_j$ and $D_{j+1}$ agree. Then
$$g_{j+2} \le a_j + 1, \qquad b_{j+2} \le g_j + 1,$$
and the reset cost $c_{j+2} = g_{j+2} + 1$ of `pair_repeats_of_white_runs` is at most $a_j + 2$.

## Argument

1. **One step.** If $b(i+2, t) = 0$ the step reads $b(i+2, t+1) = b(i, t) \oplus b(i+1, t)$, which is 0 exactly when the
   two agree. If $b(i+2, t) = 1$ the OR is 1 and $b(i+2, t+1) = \lnot b(i, t)$, which is 1 exactly when $b(i, t) = 0$
   (`D_reset` of [LeftMemory](LeftMemory.md)). Each is a case check on two Boolean values.
2. **Runs.** A white run from $s$ is a white cell at $s$ followed by $r$ steps of the first kind, so the forward
   direction reads step 1 at each of the $r$ times and the converse is an induction on the length; the same for black.
3. **Within.** Take $t \ge T$ and a time $r \in [t, t + m)$ where diagonals $i$ and $i + 1$ differ. If diagonal $i + 2$
   were white at both $r$ and $r + 1$, step 1 would make them agree at $r$; so it is black at $r$ or at $r + 1$, both
   before $t + m + 1$. For black runs take $r$ with $b(i, r) = 1$: diagonal $i + 2$ cannot be black at both $r$ and
   $r + 1$.

## What it gives and where it stops

The two inequalities move a run from one diagonal to the two before it without shortening it: a white run of $r + 1$
in $D_{j+2}$ is an agreement run of $r$ between $D_j$ and $D_{j+1}$, and nothing in the step makes agreement runs
shorter than the period. They do not bound the white runs. On the single cell's settled words to depth 200,000
(`run_transfer` of `computations/settled_words.py`, words aligned at period 32), both inequalities hold at every
depth, with equality $g_{j+2} = a_j + 1$ at 65,855 of the 199,999 depths and $b_{j+2} = g_j + 1$ at 66,140; the
longest agreement run reaches 32 (two equal words), and diagonals with a single black cell per period, whose white run
is $P - 1$, occur in the regimes of period 4, 8 and 16. So the white runs are bounded by the period, $g_j \le P_j - 1$,
and by nothing smaller that the step alone forces;
[white-run potential](../../negative-results/diagonals/white-run-potential.md) records the routes to a better bound
and where each stops, and [settled words](../../findings/diagonals/settled-words.md) describes the words themselves.

## In Lean

`run_white_white_iff` and `run_black_black_iff` rewrite with the step and check the four cases of $b(i, t)$ and
$b(i+1, t)$ by `decide`. The run lemmas apply them at each time (forward) or by induction on the length (converse).
`blackWithin_of_disagreeWithin` and `whiteWithin_of_blackWithin` split on the two cells at $r$ and $r + 1$.
`D_diagStep` packages the kit's `Rule30Diagonals.D_step` as `DiagStep D`. The axioms are `propext` and `Quot.sound`.

## Relation to the kit

The pinned kit has the step (`Rule30Diagonals.D_step`, `Rule30FiniteDiagonals.Ld_step`). Its main branch, after the
pinned revision, proves the eventual form: if $D_{j+2}$ is white from some time on, then $D_j = D_{j+1}$ from that time
on (`Rule30LeftReset.D_white_of_eq`, `white_forces_eq`), and if $D_{j+1}$ is eventually white then $D_{j+2}$ is
eventually black (`Rule30LeftUnbounded.D_black_after_white`). The finite-run equivalences, the black-run transfer and
the bounds in the `BlackWithin` form of the reset bound are not in the kit at either revision.
