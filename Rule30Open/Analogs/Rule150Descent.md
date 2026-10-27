---
title: The linear analog of period two is true
category: analogs
problems: [1]
status: proved
lean: Rule30Open.Analogs.Rule150Descent
headline: [held150_even_steps, held150_odd_steps, descent150]
kit: new
---

# The linear analog of period two is true

Replace Rule 30 by its linear part, Rule 150, $x' = x_{-1} \oplus x \oplus x_{+1}$, beside a column held at 0. The
analog of the open period-two question then has an answer: every finite half reads 0 next to the column at some even
step and at some odd step. The proof is a descent on width that uses a two-step identity Rule 150 has and Rule 30
lacks.

## Statement

Let `held150` be Rule 150 on the half left of a column held at 0, with bit $j$ the cell $j + 1$ places left of the
column.

- `descent150`: no finite line under Rule 150 has its center and the cell left of the center both reading 1 at every
  step $r \ge 1$.
- `held150_even_steps`: every finite half reads 0 next to the column at some step $4r$ or $4r + 2$ with $r \ge 1$.
- `held150_odd_steps`: and at some step $4r + 1$ or $4r + 3$ with $r \ge 1$.

## Argument

1. **Two steps are one step on each sublattice** (`step150_twice`, `iter150_double`). Over $\mathbb{F}_2$, two steps of
   Rule 150 give $y(x - 2) \oplus y(x) \oplus y(x + 2)$, because the cross terms cancel in pairs. So step $2r$ on the
   line, read at cells $2x + i$, is step $r$ of Rule 150 on the sublattice $z \mapsto y(2z + i)$.
2. **Halves inherit the property** (`halves150`). Suppose cells $0$ and $-1$ read 1 at every step $r \ge 1$. The
   rule at cell $-1$ at step $2r + 1$ gives cell $-2$ at step $2r$ as $1 \oplus 1 \oplus 1 = 1$, and the rule at cell
   0 gives cell 1 the same way. By step 1, the even half $z \mapsto y(2z)$ reads cells $0, -2$ of the line at even
   steps and the odd half $z \mapsto y(2z+1)$ reads cells $1, -1$, so both halves have the property.
3. **Descent** (`descent150`). A line supported on $w + 1$ consecutive cells has halves supported on at most
   $\lfloor w/2 \rfloor + 1$ cells. By induction on $w$, if every narrower line fails, so does this one. At $w = 0$ one
   of the two halves is zero everywhere, and the zero line reads 0 at every step.
4. **Back to the half** (`held150_even_steps`). Mirror the half about the held column to a line symmetric about cell
   $-1$, which stays 0 because the line is symmetric (`mirror_step`). Its even sublattice is a line symmetric about
   $-1/2$, whose cells 0 and $-1$ both read the cell next to the column at steps $4r$ and $4r + 2$. If those were all
   1, one step of that line would be a finite line contradicting step 3.
5. **Odd steps** (`held150_odd_steps`). Apply the even case to the half one step on.

Rule 30 has no identity like step 1, since its nonlinear term $x \land x_{+1}$ does not cancel over two steps, so the
descent has no Rule 30 counterpart.

## In Lean

`step150` and `iter150` are Rule 150 on the whole line, `mirror` reflects a half about cell $-1$, and `mirror_orbit`
carries the reflection along the orbit. `held150_orbit_one` checks the first twelve steps from a single 1: the cell
next to the column reads 0 at steps 2, 3, 10 and 11.

## Relation to the kit

Not in the kit. The kit's
[`Rule30Realization`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/7d665044b904117af9e82328aeb90a30692b2b85/lean/Ruliology/CellularAutomata/Rule30Realization.lean)
treats Rule 150 from the single cell, where the center column is constant.
