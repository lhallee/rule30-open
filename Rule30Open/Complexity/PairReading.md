---
title: Two columns read as one sequence cost every machine of the kit's model more than a steps on every window of 2^a inputs above 2^(a-1), at every scale by Jen's theorem, and the center column does up to a = 17
category: complexity
problems: [3, 1]
status: proved
lean: Rule30Open.Complexity.PairReading
headline: [pairOf_window_time, pair_window_time, pair_interval_time, column_window_time, column_window_time_or, center_window_time_le_seventeen, center_window_time_of_problem1, window_period, computes_eq_of_mod]
kit: refines
kit_modules: [Rule30Problem3, Rule30Jen, Rule30FiniteConfigs]
---

# Two columns read as one sequence cost every machine of the kit's model more than a steps on every window of 2^a inputs above 2^(a-1), at every scale by Jen's theorem, and the center column does up to a = 17

A machine of the kit's Problem 3 model reads the binary digits of $n$ from cell 0 on, so in $a$ steps it sees only
the lowest $a$ of them. If it answers that fast on $2^a$ consecutive inputs above $2^{a-1}$, the sequence it computes
has period $2^a$ from $2^{a-1}$ on. For the center column a lower bound of this kind at every scale is part of
Problem 1 and open ([the restricted models](../../negative-results/complexity/restricted-models.md), first rung). For
two different columns read as one sequence it holds at every scale, because by Jen's theorem the two columns are not
both eventually periodic.

## Statement

Write $x_t(p)$ for cell $p$ at time $t$ of Rule 30 from the row $x$ (`evolve x t p`), and for columns $j \ne k$ let
$\mathrm{pair}^x_{j,k}$ (`pairOf x j k`) be the sequence with
$$\mathrm{pair}^x_{j,k}(2t) = x_t(j), \qquad \mathrm{pair}^x_{j,k}(2t + 1) = x_t(k),$$
so that the lowest digit of the input says which column is asked. For the single black cell this is `pair j k`, with
$\mathrm{pair}_{j,k}(2t) = \mathrm{cell}(t, j)$ in the kit's `Rule30Jen.cell` (`pair_even`, `pair_odd`), and the even
inputs of `pair 0 k` read the official `center` (`pair_center`). Machines are the kit's `Rule30Problem3.Machine`, and
`Computes M f T` says that on every input $n$ the machine has halted with $f(n)$ by step $T(n)$.

1. **Locality** (`computes_eq_of_mod`). If `Computes M f T`, $n \ge 2^{a-1}$ and $T(n) \le a$, then $f(m) = f(n)$ for
   every $m \ge 2^{a-1}$ with $m \equiv n \pmod{2^a}$.
2. **A fast window forces a period** (`window_period`). If `Computes M f T` and $T(n) \le a$ for every $n$ in
   $[A, A + 2^a)$, where $A \ge 2^{a-1}$, then $f(m + 2^a) = f(m)$ for every $m \ge 2^{a-1}$.
3. **Two columns** (`pairOf_window_time`). Let the row $x$ have a leftmost black cell. For $j \ne k$, every machine
   $M$ and time $T$ with `Computes M (pairOf x j k) T`, every $a \ge 1$ and every $A \ge 2^{a-1}$, some
   $n \in [A, A + 2^a)$ has $T(n) \ge a + 1$. For the single black cell (`pair_window_time`), with $a$ the number of
   digits of $A$ (`pair_interval_time`): every interval $[A, 3A)$, $A \ge 1$, holds an input $n$ with
   $T(n) \ge \lfloor \log_2 A \rfloor + 2$, more steps than $A$ has digits.
4. **One column** (`column_window_time`, `column_window_time_or`). The bound of item 3 holds for column $p$ alone,
   from any row, whenever that column is not eventually periodic; of two different columns of a row with a leftmost
   black cell at least one has it, so every column but at most one has it, and which column could be the exception is
   not known. For the official center column it follows from Problem 1 (`center_window_time_of_problem1`).
5. **The center column up to level 17** (`center_window_time_le_seventeen`). For $1 \le a \le 17$ and every
   $A \ge 2^{a-1}$, every machine computing `center` takes at least $a + 1$ steps on some input of $[A, A + 2^a)$,
   so on infinitely many inputs.

## Proof

*Locality.* `step_agree`: two configurations with the same state and head, the head below $B$, and tapes that agree
below $B$, take the same step: both halt with the same answer, or both move to configurations with the same state and
head, the head at most one cell further right, and tapes that still agree below $B$. By induction (`run_agree`), runs
from initial tapes that agree below $B$ agree for $B$ steps, with the head at most at cell $t$ after $t$ steps. For
$m, n \ge 2^{a-1}$ with $m \equiv n \pmod{2^a}$ the initial tapes agree below cell $a$ (`init_tape_agree`): left of
cell 0 both are blank, and each cell $i < a$ holds a digit, since $2^i \le 2^{a-1}$, namely digit $i$, which $m$ and
$n$ share (`Nat.testBit_mod_two_pow`). So if the run on $n$ has halted by step $a$, the run on $m$ has halted with the
same answer, and a halted run has one answer (`run_inl_eq`).

*Window.* Given $m \ge 2^{a-1}$, the input $A + ((m + 2^a A - A) \bmod 2^a)$ lies in the window and is congruent to
$m$ and to $m + 2^a$ modulo $2^a$. Locality gives $f(m) = f(m + 2^a)$, both equal to $f$ at that input.

*Two columns.* If $T(n) \le a$ on the whole window, item 2 gives $\mathrm{pair}^x_{j,k}(m + 2^a) =
\mathrm{pair}^x_{j,k}(m)$ for $m \ge 2^{a-1}$. With $2^a = 2 \cdot 2^{a-1}$, the even inputs $m = 2t$ and the odd
inputs $m = 2t + 1$ give $x_{t + 2^{a-1}}(j) = x_t(j)$ and $x_{t + 2^{a-1}}(k) = x_t(k)$ for every $t \ge 2^{a-1}$:
both columns are eventually periodic, which the kit's Jen theorem for rows with a leftmost black cell
(`Rule30FiniteConfigs.jen`, through `evolve` $=$ the kit's `evol`) excludes. The single black cell has its leftmost
black cell at 0 (`single_leftmost`). For the interval form, $a = \lfloor \log_2 A \rfloor + 1$ gives $2^{a-1} \le A$
and $A + 2^a \le 3A$.

*One column.* A column that is not eventually periodic has no period $2^a$ from $2^{a-1}$ on, so item 2 excludes a fast
window; the kit's `Rule30FiniteConfigs.periodic_column_unique` says that at most one column of a row with a leftmost
black cell is eventually periodic, and Problem 1 says that the center column of the single black cell is not. For
$a \le 17$, `center_rung_le_seventeen` of [BinomialDuality](BinomialDuality.md) excludes the period $2^a$ from
$2^{a-1}$, from the window bound of [WideWindow](../Columns/WideWindow.md), so item 2 gives item 5.

## What it means

In the rungs that [the restricted models](../../negative-results/complexity/restricted-models.md) list for one-tape
machines that read the digits of $n$, the first, more than $a$ steps on some input of each window of $2^a$ inputs, is
equivalent to excluding the period $2^a$ from $2^{a-1}$ on. For the center column it is known for $a \le 13$ on the
kit's main branch, for $a \le 17$ in Lean here (item 5) and for $a \le 20$ by computation, and at every scale it is
part of Problem 1. For two columns it holds at every scale and on every window of that length above $2^{a-1}$, not
only the kit's canonical window $[2^{a-1}, 2^{a-1} + 2^a)$. So the model does not stand in the way of the rung: for $c$
what is missing is a form of Jen's theorem for one column. The next rungs are open for $\mathrm{pair}_{j,k}$ as for
$c$: time $\lfloor \log_2 n \rfloor + 2$ on every input says that the sequence is constant on no progression
$\{n + i \, 2^{\ell(n)}\}$, and $T(n) - \ell(n)$ unbounded, with $\ell(n)$ the number of digits, says that it is not
2-automatic, which Jen's theorem does not decide.

## Relation to the kit

The kit's main branch, `Rule30Problem3Bounds`
([4f4fb5a](https://github.com/WolframInstitute/Rule30PrizeKit/blob/4f4fb5ad6e84b73e10e2e467345dff82cd375e7b/lean/Ruliology/CellularAutomata/Rule30Problem3Bounds.lean),
unchanged at 2fdb1bb), proves the locality (`computes_eq_of_mod_two_pow_of_run_le`), the canonical window
(`period_of_canon_window_time_le`, `canon_window_time_ge_of_not_evPer_two_pow`, for every $f$), the center's
canonical window under Problem 1 (`canon_window_time_ge_of_problem1`) and, for each $a$, one left diagonal with the
bound at that scale (`diagonal_canon_window_time_ge`); it does not combine the window theorem with Jen's theorem. The
commit pinned here has neither the locality nor the window theorem, so `step_agree`, `run_agree` and
`init_tape_agree` prove the locality again; the window here is any $[A, A + 2^a)$ with $A \ge 2^{a-1}$. Jen's theorem
and `periodic_column_unique` are the kit's `Rule30Jen` for the single black cell and `Rule30FiniteConfigs` for rows
with a leftmost black cell. A finite form of Jen's argument for the center and its right neighbor, not both
$P$-periodic on $[n - P, 2n]$, is the kit's `Rule30MaskedJen.finitary_jen`; it is not needed here.
[The unary sandwich](../../findings/complexity/unary-sandwich.md) places the kit's Problem 3 between two statements
about unary input in the same model.
