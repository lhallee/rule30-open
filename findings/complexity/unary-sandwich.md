---
title: Exact one-tape converters make time O(n log n) the same question for unary and binary input, so on unary input the kit's Problem 3 lies between no time O(n log n) and no time o(n log n), which is Problem 1
category: complexity
problems: [3, 1]
status: paper
formalization: wanted
evidence: [computations/unary_sandwich.py, tests/test_unary_sandwich.py]
---

# Exact one-tape converters make time O(n log n) the same question for unary and binary input, so on unary input the kit's Problem 3 lies between no time O(n log n) and no time o(n log n), which is Problem 1

The kit states Problem 3 for one-tape machines that read the binary digits of $n$
([`Rule30Problem3`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Problem3.lean)),
and its equivalent forms prove that Problem 1 holds if and only if no one-tape machine that reads $1^n$ decides $c(n)$
in time $o(n \log n)$
([`OneTapeGap`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/equivalents/Rule30Equivalents/OneTapeGap.lean),
Hennie's theorem). Two converters with exact step counts join the two inputs. One-tape time $O(n \log n)$ is then the
same question for both, and the kit's Problem 3 lies between two statements about the one language
$L_1 = \{1^n : c(n) = 1\}$ that differ only in $O$ against $o$ at time $n \log n$.

Throughout, $\ell(n)$ is the number of binary digits of $n$ ($\ell(0) = 0$) and $s(n)$ the number of its digits 1.

## Statement

The two models are the kit's, unchanged.

- **Binary input** (`Rule30Problem3.Machine`). Finitely many numbered states, starting in 0, and numbered symbols,
  with 0 the blank and 1, 2 the digits 0, 1. The input $n$ puts digit $i$ of $n$ on cell $i$ for every $i$ with
  $2^i \le n$, so on the cells $0, \dots, \ell(n) - 1$ and on none for $n = 0$, blanks elsewhere, and the head on
  cell 0. A transition either halts with an answer, and that transition is a step, or writes, moves and changes state.
  `Computes M f T`: on every $n$ the run has halted with the answer $f(n)$ by step $T(n)$.
- **Unary input** (`OneTapeGap.TM`). Finitely many states and symbols, among them a blank and an input symbol; the
  input $1^n$ is the input symbol on the cells $0, \dots, n - 1$, with the head on cell 0 in the start state. A halting
  state is never left, and entering it is a step. `DecidesInTime M f T`: on every $n$ the state at step $T(n)$ is a
  halting state, and it accepts if and only if $f(n)$.

The time of a run is the least step at which it has halted. "Time $O(n \log n)$" means a bound
$T(n) \le C (n + 1)(\ell(n) + 1)$ for every $n$ and some constant $C$, which for integer-valued $T$ is the same as
$T(n) = O(n \log n)$ as $n \to \infty$.

1. **Converters.** Two one-tape tables, each started on cell 0 and ending with a transition into the start state of the
   machine that runs next, with the head on cell 0 and exactly that machine's input on the tape:
   - `u2b` turns $1^n$ into the kit's input $n$ in exactly
     $u(n) = (\ell + 1)(2n + \ell + 2) = 2n(\ell + 1) + \ell^2 + 3\ell + 2$ steps;
   - `b2u` turns the kit's input $n$ into $1^n$ in exactly $b(n) = 2(n + 1)(\ell + 3) - 2s(n) - 4$ steps, which is
     $2n\ell + 6n - 2s(n) + 2\ell + 2$ for $n \ge 1$ and $2$ for $n = 0$.

   Both are $2n \log_2 n + O(n)$, and $u(n) \le 3(n + 1)(\ell + 1)$, $b(n) + 1 \le 6(n + 1)(\ell + 1)$ for every $n$.
2. **Composites.** (a) For every binary machine $M$, the unary machine $U_M$ that runs `u2b` and then $M$, and enters a
   halting state carrying $M$'s answer where $M$ halts, satisfies: `Computes M f T` implies
   `DecidesInTime U_M f (T + u)`. (b) For every unary machine $U$, the binary machine $B_U$ that runs `b2u` and then
   $U$, and halts with $U$'s answer one step after $U$ reaches a halting state, satisfies: `DecidesInTime U f T` implies
   `Computes B_U f (T + b + 1)`. The times add exactly: $U_M$ takes $u(n) + t_M(n)$ steps and $B_U$ takes
   $b(n) + t_U(n) + 1$, where $t_M(n)$ and $t_U(n)$ are the times of $M$ and $U$.
3. **The sandwich.** Let
   - $B_O$: no binary machine computes $c$ in time $O(n \log n)$;
   - $U_O$: no unary machine decides $c$ in time $O(n \log n)$;
   - $U_o$: no unary machine decides $c$ in time $T$ with $T(n) = o(n \log n)$, the kit's form with real functions.

   Then
   $$U_O \iff B_O \implies \texttt{Problem3} \implies \texttt{Problem3Verbal} \implies \texttt{Problem3Robust}
   \implies \text{Problem 1} \iff U_o .$$
   The implications from `Problem3` on and the last equivalence are the kit's, in Lean; $U_O \iff B_O$ and
   $B_O \implies$ `Problem3` are proved below on paper.
4. **Exact order.** If Problem 1 holds and $B_O$ fails, as it does if the kit's `Problem3` fails, the one-tape time of
   $L_1$ has order exactly $n \log n$: some unary machine decides it in time $O(n \log n)$, and every unary machine that
   decides it takes at least $\varepsilon n \log n$ steps for infinitely many $n$, with $\varepsilon > 0$ depending on
   the machine. So `Problem3` follows from $U_O$, the statement that $c$ is not among the cheapest sequences for unary
   one-tape machines that are not eventually periodic.
5. **Linear time on unary input is Problem 1.** No unary machine decides $c$ in time $O(n)$ if and only if Problem 1
   holds: time $O(n)$ is $o(n \log n)$, and an eventually periodic sequence is decided in $n + 1$ steps (the kit's
   `periodicTM`). So the threshold of the kit's `Problem3`, moved to unary input, is Problem 1: unary input is "a
   different problem", as the kit's docstring says.
6. **Both conversions need order $n \log n$.** (i) Let a one-tape machine with $Q \ge 2$ states start on the kit's
   input $n$, and let its tape hold exactly the non-blank cells $0, \dots, n - 1$ at the first step at which it is in a
   given state. Then that step is at least $m(\log_Q m - 3)$, where $m = n - \ell(n) + 1$. (ii) No one-tape machine
   turns $1^n$ into the kit's input $n$ in time $o(n \log n)$. So running a binary machine of time $O(n)$ after
   `u2b` gives unary time $O(n \log n)$, no converter does better, and the gap between $O$ and $o$ in item 3 is the
   cost of the conversion.

## Proof

**`u2b`.** A cell of the unary region holds a one or a crossed-out one, and may also carry an output digit. Pass $k$,
for $k = 0, \dots, \ell - 1$, starts on cell 0 with $\lfloor n / 2^k \rfloor \ge 1$ ones left: it walks right to the
blank at cell $n$ crossing out the first, third, fifth, ... of them and keeping their parity, which is digit $k$ of
$n$ ($n + 1$ steps); walks left to the blank at cell $-1$ ($n + 1$); walks right over the $k$ cells that carry digits
and writes the digit on cell $k$, which lies in the region since $k < \ell \le n$ ($k + 1$); and walks back to cell 0
($k + 1$). That is $2n + 2k + 4$ steps, and $\lfloor n / 2^{k+1} \rfloor$ ones are left. The pass that finds no one
($n + 1$ steps) and the clean-up that walks left turning the digit cells into the kit's digits and every other cell
into a blank, and enters the next machine on cell 0 ($n + 1$), add $2n + 2$. In all
$\sum_{k < \ell} (2n + 2k + 4) + 2n + 2 = (\ell + 1)(2n + \ell + 2)$. The head never leaves the cells $-1, \dots, n$,
so the tape is then exactly the kit's input $n$; for $n = 0$ the two steps read two blanks.

**`b2u`.** The counter, $\ell$ cells least significant first, starts on the cells $0, \dots, \ell - 1$; a round that
starts with the value $v \ge 1$ on the cells $p, \dots, p + \ell - 1$, with ones on the cells $0, \dots, p - 1$,
subtracts one (the zeros below the lowest 1 become 1s and that 1 becomes 0: $\operatorname{tz}(v) + 1$ steps, with
$\operatorname{tz}$ the number of trailing zeros), walks left to cell $p - 1$ ($\operatorname{tz}(v) + 1$), takes the
lowest digit and writes a one on cell $p$ (1), carries each digit one cell right up to cell $p + \ell$ ($\ell$), and
walks back to the new lowest digit on cell $p + 1$ ($\ell$): $2 \operatorname{tz}(v) + 2\ell + 3$ steps. By Legendre's
formula the trailing zeros of $1, \dots, n$ add up to $n - s(n)$. The last round finds the counter zero on the cells
$n, \dots, n + \ell - 1$ ($\ell + 1$ steps), blanks it ($\ell + 1$), and walks over the $n$ ones to cell $-1$ and enters
the next machine on cell 0 ($n$): $n + 2\ell + 2$. In all $2(n - s(n)) + n(2\ell + 3) + n + 2\ell + 2 = b(n)$ for
$n \ge 1$, and $b(0) = 2$. The head never leaves the cells $-1, \dots, n + \ell$, and the tape is then exactly $1^n$.

For the bounds of item 1: $u(n) \le (\ell + 1)(3n + 2)$ since $\ell \le n$, and
$b(n) + 1 < 2(n + 1)(\ell + 3) \le 6(n + 1)(\ell + 1)$.

**Composites.** (a) $U_M$ has the states of `u2b`, the states of $M$ and two halting states, one per answer, which
accept according to the answer; its symbols are $M$'s symbols, with $M$'s blank as the blank, and the symbols of
`u2b`, with the unary one as the input symbol. The last transition of `u2b` enters $M$'s start state; in a state of
$M$, $U_M$ follows $M$'s table, and where $M$'s table halts with $b$ it enters the halting state of $b$. After
$u(n)$ steps the configuration is $M$'s initial one on $n$, so $U_M$ follows $M$ step for step and enters a halting
state at step $u(n) + t_M(n)$ with $M$'s answer; it stays there, so `DecidesInTime U_M f (T + u)`. (b) $B_U$ has the
states of `b2u`, numbered so that its start state is 0, and the states of $U$; its symbols are the blank, the two
digits, the unary one and one code for each symbol of $U$. In a state of $U$ it reads the blank as $U$'s blank, the
unary one as $U$'s input symbol and a code as its symbol, and writes codes, as the kit's `ProblemThree.OfTM.ofTM` does.
After $b(n)$ steps the tape reads as $U$'s initial tape on $1^n$; $B_U$ follows $U$ until $U$ is in a halting state,
at step $b(n) + t_U(n)$, and the next transition halts with that state's answer. With `Machine.run_add`, `Computes B_U
f (T + b + 1)`.

**The sandwich.** If a unary machine decides $c$ within $C(n + 1)(\ell + 1)$ steps, (b) gives a binary machine within
$(C + 6)(n + 1)(\ell + 1)$; if a binary machine computes $c$ within $C(n + 1)(\ell + 1)$, (a) gives a unary machine
within $(C + 3)(n + 1)(\ell + 1)$. So $U_O \iff B_O$. A machine within $C(n + 1)$ steps is within
$C(n + 1)(\ell + 1)$ (`Computes.mono`), so $B_O$ implies `Problem3`. The kit proves `problem3Verbal_of_problem3` and
`problem3Robust_of_problem3Verbal` (`Rule30Problem3`), `problem1_of_problem3Robust` (`ProblemThree`, and in core Lean
`Rule30Problem3Bounds` on the kit's main branch) and `problem1_iff_no_fast_one_tape_decider` (`OneTapeGap`), which is
Problem 1 $\iff U_o$.

**Exact order.** If $B_O$ fails, $U_O$ fails: some unary machine decides $L_1$ in time $O(n \log n)$. A unary machine
decides $L_1$ within its own times, and by $U_o$ these are not $o(n \log n)$, which is the second half of item 4.
Item 5 is `decidesInTime_periodicTM` with $U_o$.

**Optimality.** (i) For a boundary $b$ between the cells $b - 1$ and $b$, let $\sigma_b$ be the states just after each
crossing of $b$ before the given state is first entered. For $\ell(n) \le b \le n$ the cells from $b$ on start blank,
and the head starts left of $b$, so the run right of $b$ is determined by $\sigma_b$: each visit starts in the
recorded state at cell $b$, on the cells as the last visit left them, and runs until it crosses back or, on the last
visit, until the given state is entered. So the content of the cells from $b$ on at that moment, read from $b$
rightward, is the same function of $\sigma_b$ for every such $b$, and it has $n - b$ non-blank cells. The $m$
sequences $\sigma_b$ are therefore pairwise distinct. A step crosses at most one boundary, so the time is at least
$\sum_b |\sigma_b|$. At most $Q^L$ sequences over $Q$ states are shorter than $L$, so with $L^* = \lfloor \log_Q m
\rfloor$, $\sum_b |\sigma_b| \ge \sum_{L=1}^{L^*} (m - Q^L) \ge m L^* - \tfrac{Q}{Q - 1} m \ge m(\log_Q m - 3)$.
(ii) A converter in time $a(n) = o(n \log n)$, followed as in (a) by the binary machine that decides whether $n$ is a
power of two within $\ell(n) + 1$ steps (it walks over the zeros below the lowest 1 and answers yes exactly when the
next cell is blank), would decide $\{1^n : n \text{ is a power of } 2\}$ in time $o(n \log n)$, and Hennie's theorem
(`OneTapeGap.DecidesInTime.eventuallyPeriodic`) would make that sequence eventually periodic, which it is not.

## Prefix output

A *prefix printer* is a machine of the kit's form, its halting answer ignored, that on the kit's input $N$ halts with
$c(0), \dots, c(N - 1)$ on the cells $0, \dots, N - 1$ as the symbols 1 (white) and 2 (black), and blanks elsewhere.

- (i) Every prefix printer with $Q \ge 2$ states takes at least $m(\log_Q m - 3)$ steps on $N$, $m = N - \ell(N) + 1$:
  the argument of item 6 (i), with the halt in place of the given state.
- (ii) Some prefix printer takes $O(N^2)$ steps: it runs the row-by-row simulation of
  [the quadratic-time machine](../../Rule30Open/Complexity/QuadraticTime.md) with the rows stored so that the left edge
  of row $t$ is cell 0, its center then at cell $t$, keeps the counter and the rows on other tracks than the output,
  and writes the center of row $t$ on the output track at cell $t$ during the sweep of round $t$.
- (iii) If a binary machine computes $c$ with times $t(n)$, some prefix printer takes
  $O(\sum_{n < N} t(n) + N \ell(N))$ steps. Before round $n$ the cells $0, \dots, n - 1$ hold the output, and two
  counters, $n$ and $N - n$, lie on other tracks from cell $n$ on. Round $n$ copies the first counter, without leading
  zeros, as the machine's input on a further track from cell $n$ on, with the machine's tape folded at cell $n$ onto
  two tracks, so that each of its steps costs $O(1)$ and the region it uses reaches at most $t(n)$ cells right of
  $n$; runs it; walks back, erasing the cells it visited (each visited cell is marked); writes its answer on cell $n$;
  and moves both counters one cell right, adding one to the first and subtracting one from the second, in
  $O(\ell(N))$ steps.
- (iv) Hence, if every prefix printer takes at least $\varepsilon N^2$ steps for infinitely many $N$, with
  $\varepsilon > 0$ depending on the printer, the kit's `Problem3Verbal` holds: a machine in time $T$ with
  $k \, T(n) \le n$ from some $n$ on, for every $k$, has $\sum_{n < N} T(n) = o(N^2)$. The prefix form gives nothing
  more: a binary machine within $C(n + 1)$ steps gives by (iii) a printer in $O(N^2)$ steps, which (ii) already
  achieves. On unary input the printer's time changes by $O(N \log N)$ (the converters), which is $o(N^2)$, so (iv)
  holds there too.

## What it means

On unary input every sequence that is not eventually periodic needs time that is not $o(n \log n)$, and by item 2 (a)
every sequence that a binary machine computes in time $O(n \log n)$, for example every 2-automatic sequence and every
sequence computed in time polynomial in $\ell(n)$, is decided in time $O(n \log n)$. The kit's `Problem3` sits between
"$c$ is outside that class" ($U_O$) and "$c$ is not eventually periodic". The unary form makes neither end easier: the
lower end is Problem 1 itself, and the upper end is equivalent to the binary statement $B_O$. Crossing sequences stop
at the lower end. Hennie's count applies to every sequence that is not eventually periodic, and some of them, the
indicator of the powers of two for one, are decided in time $O(n \log n)$; within $C n \log n$ steps the crossing
sequences on $1^n$ have average length $O(\log n)$, and the $Q^{O(\log n)}$ sequences of that length outnumber the
$n$ boundaries, so no two need be equal and nothing can be cut out. On binary input the same method stops at $\ell^2$
([the crossing-sequence barrier](../../negative-results/complexity/one-tape-crossing.md)).

In the prefix form, `Problem3Verbal` follows from a lower bound of order $N^2$ for printing the first $N$ cells, a
depth statement in Bennett's sense (a heuristic reading: a program of constant size prints the prefix only in time of
the order of simulation), while every sequence costs at least about $N \log_Q N$ to print with $Q$ states; the kit's
`Problem3` is out of reach of that form. In the binary model itself, two columns read as one sequence need more than
$a$ steps on every window of $2^a$ inputs above $2^{a-1}$, at every scale, by Jen's theorem, while for $c$ alone that
bound is part of Problem 1 ([PairReading](../../Rule30Open/Complexity/PairReading.md), in Lean).

## Relation to the kit

The kit has both models, the chain `Problem3` $\implies$ `Problem3Verbal` $\implies$ `Problem3Robust` $\implies$
Problem 1, Hennie's theorem for unary input, and `OfTM.ofTM`, which runs a machine of `OneTapeGap` on binary digits in
the kit's model one step slower. The docstring of `Rule30Problem3` says that unary input "is a different problem", on
which every machine needs more than $n$ steps because $c$ is not eventually constant; item 5 says how far that goes:
time $O(n)$ on unary input is excluded exactly when Problem 1 holds.
Neither the pinned commit nor the main branch (checked at
[4f4fb5a](https://github.com/WolframInstitute/Rule30PrizeKit/blob/4f4fb5ad6e84b73e10e2e467345dff82cd375e7b/lean/Ruliology/CellularAutomata/Rule30Problem3Bounds.lean)
and 2fdb1bb) has a converter between unary and binary input, a statement in time $O(n \log n)$, or a prefix printer.
The converters are the textbook constructions and the crossing-sequence counts are Hennie's method; the exact step
counts, the sandwich and the prefix form are what this entry adds.

A Lean proof of items 1 to 3 would follow [QuadraticTime](../../Rule30Open/Complexity/QuadraticTime.md): named
states and symbols coded into the kit's types, walk lemmas, and the tape between passes written out. The unary model
is in the kit's equivalent forms, which depend on Mathlib, and this repository builds only against the kit's core.

## Reproduce

```bash
python -m computations.unary_sandwich --max-n 120 --sample 65536    # 7 s
```

For every $n \le 120$ it runs both converters as transition tables and checks that each leaves exactly the other
model's input with the head on cell 0, that every pass of `u2b` and every round of `b2u` takes the steps the proof
gives, and that the totals are $u(n)$ and $b(n)$. It checks that $U_M$ for the quadratic-time machine $M$ decides
$c(n)$ in $u(n) + t_M(n)$ steps and that $B_{U_M}$ computes $c(n)$ in $b(n) + u(n) + t_M(n) + 1$ steps, against the
center column of `computations.rule30`. At $n = 4^j - 1, 4^j, 4^j + 1$ up to $65{,}537$ it runs the converters alone:

| $n$ | 256 | 1,024 | 4,096 | 16,384 | 65,536 |
|---|---:|---:|---:|---:|---:|
| $u(n)$ | 5,230 | 24,732 | 114,898 | 524,560 | 2,359,638 |
| $u(n) / (n \log_2 n)$ | 2.554 | 2.415 | 2.338 | 2.287 | 2.250 |
| $b(n)$ | 6,162 | 28,694 | 131,098 | 589,854 | 2,621,474 |
| $b(n) / (n \log_2 n)$ | 3.009 | 2.802 | 2.667 | 2.572 | 2.500 |

[tests/test_unary_sandwich.py](../../tests/test_unary_sandwich.py) checks the converters, their passes and rounds and
both closed forms for $n \le 128$, the bounds of item 1 and Legendre's count for $n < 2^{16}$, $U_M$ for the
quadratic-time machine and for the kit's `lowBit` for $n \le 48$, $B_U$ for the kit's `periodicTM` of a sequence with
period 3 for $n \le 100$, and the round trip $B_{U_M}$ for $n \le 32$, against `computations.rule30` and the step
counts of `computations.one_tape`.
