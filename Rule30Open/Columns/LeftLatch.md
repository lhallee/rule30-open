---
title: Every eventual period comes down to one statement about the left half
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.LeftLatch
headline: [column_not_eventually_of_leftLatch, not_eventually_of_leftLatch, kickOrbit_eq, leftLatch_one]
kit: refines
kit_modules: [Rule30DrivenLeft, Rule30MaskedJen, Rule30PeriodTwo, Rule30EtherThreeLeft, Rule30PeriodFourSkeleton]
evidence: [computations/left_halves.py]
---

# Every eventual period comes down to one statement about the left half

The kit reduces the eventual periods 2, 3 and 4 of the center column, word by word, to statements about the left half
alone. This module does the same for every block of every period, in one statement `LeftLatch b`, and adds the
readings that the cell right of the column forces. By computation no left half of up to 18 to 100 cells meets it, for
every block of period 3, 5, 6, 7 and 9 ([the survey](../../findings/columns/left-half-every-block.md)), the periods
that no window lock reaches.

## Statement

Write $u_j(t)$ for the cell $j + 1$ places left of a column $k$ at time $t$. A block $b$ of length $P$, repeated, reads
$b(t \bmod P)$ at step $t$ (`readAt`). The half moves by `held`, Rule 30 beside a column held at 0, with the cell next
to the column flipped at the steps where the block reads 1 at $t$ and at $t + 1$ (`kickStep`, `kickOrbit`).

`Keeps b φ u a t` asks, at step $t$ of the half $u$ beside a column that reads $b$ from phase $\varphi$, with a
sequence $a$ in place of the cell right of the column:

1. **the check**: at a 1 of the block, $u_0(t) = \lnot b(t + \varphi + 1)$;
2. **the cell right of the column, shown**: at a 0 of the block, $a(t) = b(t + \varphi + 1) \oplus u_0(t)$;
3. **its latch**: if $a(t) = 1$, then $a(t + 1) = \lnot b(t + \varphi)$.

`LeftLatch b` says that for every phase $\varphi$ and every finitely supported half $u$, no sequence $a$ keeps all
three at every step.

- `column_not_eventually_of_leftLatch`: in the orbit of a row with a leftmost 1, if `LeftLatch b` holds, no column
  repeats $b$ from any time on.
- `not_eventually_of_leftLatch`: the official form, for the single seed's center column.
- `kickOrbit_eq`: while column $k$ repeats $b$ from time $T$, the half left of it at time $T + t$ is the kicked orbit
  of the half at time $T$.
- `leftLatch_one`: `LeftLatch` holds for the black block $1$.

## Argument

1. **The kicked form.** In the orbit of any row the half left of a column follows `held`, flipped next to the column
   where the column reads 1 at $t$ and $t + 1$ ([KickedForm](KickedForm.md), `left_kicked_zero`,
   `left_kicked_succ`). While the column repeats $b$ from $T$, that kick at step $T + t$ is
   $b(t + T) \land b(t + T + 1)$, and induction on $t$ gives `kickOrbit_eq`.
2. **The three conditions hold in every orbit.** At a 1 of the column the cell left of it is the negation of the
   column's next value (`left_kicked_check`). At a 0 of the column its next value is the cell left of it XOR the cell
   right of it (`right_shown`). A black cell right of the column is followed by the negation of the column
   (`right_latch`). So the column right of $k$, read from time $T$, is a sequence $a$ that keeps all three.
3. **Finite support.** A row whose leftmost 1 is at $m$ has its leftmost 1 at $m - t$ at time $t$ (`left_edge`), so
   the half left of column $k$ at time $T$ is white beyond depth $k - m + T$.
4. **The black block.** With every phase black the check makes $u_0 = 0$ at every step and the kick fires at every
   step. Then `held` forces $u_1 = 1$ at every step, and cell by cell the half reads $0, 1, 0, 1, \dots$ at every step,
   which no finitely supported half does.

## What it covers

`LeftLatch b` is open for every block but the black one: it is one statement for each eventual period, not a proof
of any. For $01$, $001$, $011$ and $0111$ the checks are the patterns of the kit's `Q01`, `Q001`, `C3w` and `C3`, so
each of those statements implies `LeftLatch` of its word, by shifting the phase; that implication is not formalized
here. The latch adds readings only at a 0 of the block that is
not followed by two 1s: for $01$ it is the kit's golden condition (`period_two_golden` in
[KickedForm](KickedForm.md)), and for $011$ and $0111$ it adds nothing. For $0001$ and $0011$ the kit's `C3` fixes
more readings at the white phases, from the right half under those words, so it asks less than `LeftLatch`. The
computations in [the survey](../../findings/columns/left-half-every-block.md) search exactly these conditions.

## Relation to the kit

The kit has the driven left half and its effective boundary for the single seed
([`Rule30DrivenLeft`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30DrivenLeft.lean),
`cell_eq_L_effective`, from
[`Rule30MaskedJen`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30MaskedJen.lean))
and the word-by-word reductions
[`Rule30PeriodTwo`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30PeriodTwo.lean)
(`not_eventually_period_two_of_Q01`),
[`Rule30EtherThreeLeft`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30EtherThreeLeft.lean)
(`not_eventually_001_of_Q001`, `not_eventually_011_of_C3w`) and
[`Rule30PeriodFourSkeleton`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30PeriodFourSkeleton.lean)
(`least_period_four_of_C3`). Its `Rule30DrivenLeft.ones_fails` is the black block's case. This module states the
reduction once for every block, for every column of every row with a leftmost 1, and adds the latch.

## Lean

`Rule30Open.Columns.LeftLatch`: `readAt`, `kickStep`, `kickOrbit`, `Keeps`, `LeftLatch`, `kickOrbit_eq`,
`column_not_eventually_of_leftLatch`, `not_eventually_of_leftLatch` and `leftLatch_one`.
