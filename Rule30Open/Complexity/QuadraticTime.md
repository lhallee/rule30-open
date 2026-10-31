---
title: A one-tape machine computes the center column in 2n² + 2n log n + O(n) steps, so the kit's Problem 3 asks for the exponent between 1 and 2
category: complexity
problems: [3]
status: proved
lean: Rule30Open.Complexity.QuadraticTime
headline: [simulator_time, simulator_computes, center_computes_quadratic]
kit: new
kit_modules: [Rule30Problem3]
evidence: [computations/one_tape.py]
---

# A one-tape machine computes the center column in 2n² + 2n log n + O(n) steps, so the kit's Problem 3 asks for the exponent between 1 and 2

The kit's formal Problem 3 says that no deterministic one-tape Turing machine, reading the binary digits of $n$,
computes $c(n)$ within $C (n + 1)$ steps for any constant $C$. The kit proves the chain from that statement down to
Problem 1, and checks its conventions on a machine that reads one digit, but it has no machine that computes $c$ at
all. This module builds one: `simulator`, with 17 states and 7 tape symbols, halts on the input $n$ with the answer
$c(n)$ after exactly

$$T(n) = 2 n^2 + 2 n \ell + 7 n + 3 \ell + 6$$

steps, where $\ell = \lfloor \log_2 n \rfloor + 1$ is the number of digits of $n$ ($\ell = 0$ for $n = 0$), and
$T(n) \le 6 (n + 1)^2$. So in the kit's own model the center column is computed in quadratic time, the class of
machines that Problem 3 quantifies over is not empty, and the problem asks whether the exponent 2 of one tape can
fall to 1.

## Statement

In the kit's model (`Rule30Problem3.Machine`: states $0, \dots, q$, symbols $0, \dots, s + 2$ with $0$ the blank and
$1, 2$ the digits, the digits of $n$ least significant first on the cells $0, 1, \dots$, the head on cell $0$, and a
halt by a transition that carries the answer):

- `simulator_time`: `simulator.run n (time n) = .inl (center n)` for every $n$, with `time n` the $T(n)$ above.
- `simulator_computes`: `Computes simulator center (fun n => 6 * (n + 1) ^ 2)`.
- `center_computes_quadratic`: there are a machine $M$ and a constant $C$ with `Computes M center (fun n => C * (n + 1) ^ 2)`.

## The machine

The tape holds three things, left to right: the input digits, reused as a binary counter, on the cells
$0, \dots, \ell - 1$; the blank at cell $\ell$ as a separator; and row $t$ of the single black cell on the cells
$\ell + 1, \dots, \ell + 1 + 2t$, cell $x$ of the row at $\ell + 1 + t + x$, the center carrying a mark. Row symbols
record a color and the mark. The run has four phases.

1. **Start** (`init_phase`, $2\ell + 4$ steps). Walk right over the digits, write the single black cell, marked, one
   cell past the separator, and walk back to cell $0$.
2. **Decrement** (`decrement_phase`, $\ell + 1$ steps). From cell $0$, turn each digit $0$ into $1$ until the lowest
   digit $1$, which becomes $0$: the counter drops by one. Walk on over the remaining digits and the separator to the
   row. If every digit was $0$ the counter is spent, and the machine goes to the last phase instead.
3. **Sweep** (`sweep_phase`, $2t + 3$ steps). Rewrite the row in place, one cell to the right: the state carries the
   old cells two and one places left of the head, and the cell written at the head is Rule 30 of those two and the
   old cell under the head. Two cells are written past the old right edge, so the stored row is row $t + 1$ on the
   cells $\ell + 1, \dots, \ell + 3 + 2t$, with the mark moved one cell right. Shifting right instead of growing left
   keeps the row region off the counter.
4. **Return** (`return_phase`, $2t + \ell + 4$ steps). Walk left over the row, the separator and the digits to cell
   $0$, and decrement again.
5. **Answer** (`final_phase`, $\ell + n + 2$ steps). With the counter spent, walk right over the row to the marked cell
   and halt with its color.

The iterations for $t = 0, \dots, n - 1$ take $\sum (4t + 2\ell + 8) = 2n^2 + 2n\ell + 6n$ steps (`loop`,
`loopTime`), which with the first and last phases gives $T(n)$ (`time_eq`).

## The proof in Lean

The machine is written with named states and symbols (`St`, `Sym`, the table `trans`) and coded into the kit's
`Fin` types (`St.code`, `Sym.code`); `cfg s h τ` is the kit configuration with state `s`, head `h` and the tape `τ`
read through the codes, and `step_go`, `step_halt` read one step of the kit's `Cfg.step` off the table. `iter`
iterates the kit's step and composes (`iter_add_of_inr`), and the kit's run is `iter` from the kit's input
configuration (`run_eq_iter`, `init_eq`).

The tapes between phases are explicit: `tape ℓ m t` holds the counter $m$ on $\ell$ digit cells and row $t$ in the row
region, with the digits read from `Nat.testBit` and the row from `evolve single`. Three walk lemmas (`walk_right`,
`walk_left`, `scan_walk`) move a state over cells it does not change, or whose zero digits it turns to ones; the
sweep is an induction over the old row with the invariant that the cells passed hold row $t + 1$ and the cells ahead
hold row $t$. The decrement uses the bits of $m - 1$ from the lowest set bit of $m$ (`testBit_pred`), and the rows
outside the light cone are white (`single_outside`), which is what makes the two cells past the old edge correct.
`loop` composes the phases by induction on $t \le n$, and `evolve_single_center` turns the marked cell's color into
the official `center n`.

[`computations/one_tape.py`](../../computations/one_tape.py) runs the same table in Python and checks the answer and
the exact step count against $c(n)$ and $T(n)$; `tests/test_one_tape.py` does so up to $n = 80$ and checks that the
Python table and the Lean table agree on the sweep.

## What it means

Problem 3 in the kit's model is a statement about the gap between the exponents 1 and 2 of one-tape time, with
constants $6$ and, on the lower side, nothing beyond reading the input ([the barrier](../../negative-results/complexity/problem-three-barrier.md)).
The quadratic bound is the cost of simulating the light cone cell by cell, $\sum_{t < n} (2t + 1)$ updates plus the
walks, and it is the best known for one tape: a shortcut would be a negative answer to Problem 3, which no search here
has found ([the complexity category](../../CATALOG.md#complexity)). In space the machine uses $\ell + 2n + 2$ cells,
linear in $n$, against the $O(\sqrt{n \log n})$ of tree evaluation ([the space ladder](../../findings/complexity/space-ladder.md)),
which trades time for space.

## Relation to the kit

The kit's [`Rule30Problem3`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Problem3.lean)
defines the model and the three statements, proves `Problem3 → Problem3Verbal → Problem3Robust`, and checks the
conventions on `lowBit`, a machine that answers with the last digit in one step. Its equivalent forms show that a
2-automatic sequence is computed in $\ell + 1$ steps and relate the kit's model to the one-tape model of
`OneTapeGap`. Neither part has a machine that computes `center`; a pull request on the kit's main branch
(`Rule30Problem3Bounds`) proves lower bounds of the order of $\ell$ in the same model
([the kit's pull requests](../../literature/kit-pull-requests.md#the-cost-of-the-center-cell)). This module adds the
upper bound.
