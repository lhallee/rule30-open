---
title: A random left window gives a fair center window, for every row
category: random-rows
problems: [1, 2]
status: proved
lean: Rule30Open.RandomRows.LeftWindow
headline: [cone_left_xor, count_centerWindow, centerWindow_unique, count_adapted, count_periodic, seed_window]
kit: refines
kit_modules: [Rule30Realization]
---

# A random left window gives a fair center window, for every row

Replace the $n$ cells left of the center of any row by a uniformly random word. Then the center cells at times
$1, \dots, n$ are independent fair coins, so the analogs of Prize Problems 1 and 2 hold for random rows. Freeing only
some of those cells still makes each center cell at a freed depth a fair coin given the column before it, and a center
column that repeats from some time on becomes rare as soon as infinitely many depths are free. None of this reaches the
single cell: it is one of the rows counted, the all-white window, and the counts do not single it out.

## Statement

Write $a_t(x)$ for cell $x$ at time $t$ and $c(t) = a_t(0)$ for the center column. Depth $s$ is cell $-s$. For a row
$r$ and a word $\ell$ of $n$ cells, let $r_\ell$ be $r$ with cells $-n, \dots, -1$ replaced by $\ell$, and
$c_\ell = (c_\ell(1), \dots, c_\ell(n))$ the center column of $r_\ell$ at times $1, \dots, n$.

1. **The leftmost cell of a cone** (`cone_left_xor`). If two rows agree on cells $x - t + 1, \dots, x + t$, then
   $a_t(x) \oplus a'_t(x) = a_0(x - t) \oplus a'_0(x - t)$.
2. **Exact distribution** (`count_centerWindow`, `centerWindow_unique`). For every row $r$ and every $n$, the map
   $\ell \mapsto c_\ell$ is a bijection of $\{0, 1\}^n$: for every set $E$ of words of length $n$, exactly $|E|$
   windows $\ell$ have $c_\ell \in E$.
3. **Partial randomization** (`count_adapted`). Free the cells at the depths of a finite set $S$ and keep the rest of
   $r$. At each depth $s \in S$ with $Q(s)$, ask that $c(s) = g_s(c)$, where $g_s$ reads $c$ only before time $s$.
   Exactly $2^{|S| - |\{s \in S : Q(s)\}|}$ of the $2^{|S|}$ rows meet every condition.
4. **A periodic center is rare** (`count_periodic`). In the same setting, with $S \subseteq [0, M]$ and $p \ge 1$,
   at most $2^{|\{s \in S \,:\, s < T + p\}|}$ of the $2^{|S|}$ rows have $c(t) = c(t - p)$ for all $t$ with
   $T + p \le t \le M$.
5. **The seed** (`seed_window`). The single cell is $r_\ell$ for $r$ the single cell and $\ell = 0^n$, and its window
   is the official center column, `Rule30Prize.center` at times $1, \dots, n$.

Statement 2 makes the center window of a uniformly random left window uniform: its cells are independent fair coins.
So $k$ black cells among $c_\ell(1), \dots, c_\ell(n)$ come from $\binom{n}{k}$ windows, and a window that repeats with
period $p$ from time $T$ (with $T \ge 1$ and $T + p - 1 \le n$) from $2^{T + p - 1}$ of them.

## Argument

1. By induction on $t$. One step reads $a_t(x - 1) \oplus \bigl(a_t(x) \lor a_t(x + 1)\bigr)$. The cones of
   $(t, x)$ and $(t, x + 1)$ lie inside the cells where the rows agree, so those two cells agree (`cone_congr`). The
   cone of $(t, x - 1)$ has the same leftmost cell, $x - t - 1$, and agrees elsewhere, so by induction $a_t(x - 1)$
   differs between the rows exactly when that cell does; the XOR passes the difference on.
2. By induction on $n$. Cell $-(n + 1)$ lies outside the cone of every center cell before time $n + 1$, so the two
   ways to extend a window $\ell'$ of $n$ cells by an outer cell give $c_{\ell'}$ again at times $1, \dots, n$
   (`centerWindow_cons`). At time $n + 1$ the cell is the leftmost of the center's cone, so by statement 1 the two
   extensions give opposite values (`centerWindow_flip`). The extensions of $\ell'$ therefore give the words
   $(c_{\ell'}, 0)$ and $(c_{\ell'}, 1)$ in some order, and counting over $\ell'$ with the induction hypothesis,
   once for each value of the last letter, gives $|E|$.
3. By induction on $S$, from its deepest depth $s$. Conditions at shallower depths read the center only before time
   $s$, and cell $-s$ lies outside those cones, so they do not depend on it. The condition at $s$, if $Q(s)$, compares
   $c(s)$, which flips with cell $-s$ by statement 1, with $g_s(c)$, which reads the column only before $s$ and so does
   not. Exactly one value of the cell meets it, and with no condition at $s$ both values do. Each depth with a
   condition halves the count and each depth without one doubles it.
4. Statement 3 with $Q(s)$ true exactly when $s \ge T + p$, and $g_s(c) = c(s - p)$, which reads $c$ before $s$
   because $p \ge 1$. A column that repeats meets every condition.
5. The single cell is white at every depth, so writing white cells at depths $1$ to $n$ changes nothing
   (`setLeft_white`), and `evolve_single_center` identifies its column with the official one.

## What it gives, and what it does not

With infinitely many free depths the bound in statement 4 tends to 0 as $M$ grows, for each of the countably many pairs
$(T, p)$. So a row whose cells at an infinite set of depths are independent fair coins has an eventually periodic
center column with probability 0, however sparse the set. With finitely many free depths the bound stays above a fixed
fraction. And when the other cells are the single cell's, the statement that no row of the family has an eventually
periodic center column contains Prize Problem 1, since the single cell is the row with every free cell white. The
general limit argument and the matching statement for Problem 2 are in
[the negative result on random-row arguments](../../negative-results/random-rows/almost-every-row.md).

The counts treat every window alike, and some windows give a center column that repeats from time 1 to time $n$. That
is why counting cannot separate the single cell: for every $n$, one row that agrees with it outside cells $-n$ to $-1$
has $n$ white center cells at times 1 to $n$, and the kit's `seed_perturbation` gives a row that agrees with it from
cell $-n$ rightward and whose center is constant from time $n$ on.

## In Lean

`setLeft init l` writes the word `l` outermost first, and `centerWindow init l` lists the center cells latest first, so
the outermost cell and the cell it decides head their lists and the induction runs on `List.cons`. `allLists n`, from
[RightHalf.md](../Foundations/RightHalf.md), enumerates the words of $n$ cells, and every count is a `List.countP` over
it. `assign init S a` writes the values `a` at the depths `S`, which `count_adapted` and `count_periodic` ask to be
listed deepest first (`S.Pairwise (fun a b => b < a)`); `meets` is the conjunction of the conditions and
`periodicUpTo` the repetition. Two spot checks run by `decide`: the single cell's window of three cells is $1, 0, 1$,
latest first, and the eight windows of three cells give eight different center windows. The binomial and periodic
counts after statement 2 are counts of words, stated in the text and not in Lean.

## Relation to the kit

The kit's
[`Rule30Realization`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/7d665044b904117af9e82328aeb90a30692b2b85/lean/Ruliology/CellularAutomata/Rule30Realization.lean)
proves that for every right half and every column there is exactly one configuration with that right half and that
column 0 (`column_realizable_unique`), and that a configuration agreeing with the single cell from $-n$ rightward can
have a center column constant from time $n$ on (`seed_perturbation`). Statement 2 is the finite, counted form of the
first, for every row rather than every right half; statements 3 and 4, on partial randomization, are not in the kit.
The literature's form of the same fact is that Rule 30, being onto, keeps the uniform measure
([measure-and-analogs.md](../../literature/measure-and-analogs.md)).
