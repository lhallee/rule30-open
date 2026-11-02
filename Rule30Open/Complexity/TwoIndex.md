---
title: A 2-automatic array of two indices with eventually periodic rows has row periods O(j), so Rule 30's diagram of right diagonals is not 2-automatic if the right-edge cycles grow faster than linearly; Rule 90's is 2-automatic
category: complexity
problems: [3]
status: proved
lean: Rule30Open.Complexity.TwoIndex
headline: [twoIndex_row_period_le, twoIndex_row_period_le_of_periodic, twoIndex_diag_automatic, rule30_twoIndex_not_recognizable, rule30_twoIndex_not_recognizable_of_leastExp, rule30_twoIndex_not_recognizable_of_white_runs, rule30_twoIndex_center_automatic, rule90_twoIndex_recognizable, rule90_spacetime_recognizable]
kit: new
kit_modules: [Rule30RightPeriods, Rule30Diagonals, Rule30Realization, Rule30Equivalents.BuchiArithmetic, Rule30Equivalents.TFunctionCycles, Rule30Equivalents.Automatic]
evidence: [computations/two_index.py, tests/test_two_index.py]
---

# A 2-automatic array of two indices with eventually periodic rows has row periods O(j), so Rule 30's diagram of right diagonals is not 2-automatic if the right-edge cycles grow faster than linearly; Rule 90's is 2-automatic

Every model in [restricted models](../../negative-results/complexity/restricted-models.md) that reads the digits of
$n$ makes an eventually periodic center column cheap, so a lower bound there past the cost of reading the digits
implies Problem 1. This entry takes a model in which periodicity of the column does not help: a finite automaton that
reads the binary digits of two indices, the diagonal $j$ and the time $t$, and outputs the cell. For Rule 30 the
question whether such an automaton exists becomes a question about the growth of the cycles of the right edge, which
the center column does not enter; for Rule 90 the automaton exists.

## Statement

An array $b : \mathbb{N}^2 \to \{0, 1\}$ is *2-recognizable* (2-automatic in two indices) when its 2-kernel
$$\{(v, w) \mapsto b(2^e v + r,\ 2^e w + s) : e \ge 0,\ 0 \le r, s < 2^e\}$$
is finite. By the two-index form of Eilenberg's criterion (Salon; Allouche and Shallit 2003, chapter 14, whose text
was not read here) this is the same as being the output of a finite automaton that reads the digits of $j$ and $t$ in
pairs; the Lean definition `TwoIndex.Recognizable b` asks for one list that contains every section,
which is finiteness without a finite-set library (the repository builds without Mathlib). For a sequence the same
definition, `TwoIndex.Automatic`, is equivalent to the kit's `Automatic.IsAutomatic 2`. Write
$R(j, t) = \mathrm{cell}(t, t - j)$ for the single black cell of Rule 30 (the kit's `Rule30Diagonals.R`): row $j$ is
the $j$th diagonal from the right edge, periodic from time 0 with a period dividing $2^j$ (`R_periodic`).

1. **The kernel lemma** (Lean, `twoIndex_row_period_le`). If $b$ is 2-recognizable and every row $t \mapsto b(j, t)$
   is eventually periodic, there is $C$ such that every row $j$ has an eventual period at most $C(j + 1)$. If every row
   is periodic from time 0, so is that period (`twoIndex_row_period_le_of_periodic`).
2. **Diagonals** (Lean, `twoIndex_diag_automatic`). The diagonal $n \mapsto b(n, n)$ of a 2-recognizable array is
   2-automatic.
3. **Rule 30, conditional** (Lean). If for every $C$ some diagonal $R_j$ has no period at most $C(j + 1)$, then $R$
   is not 2-recognizable (`rule30_twoIndex_not_recognizable`). Two equivalent forms of the hypothesis give the same
   conclusion:
   - `rule30_twoIndex_not_recognizable_of_leastExp`: $2^{e_j}/(j + 1)$ is unbounded, $e_j$ the kit's
     `Rule30RightPeriods.leastExp j`, so that $2^{e_j}$ is the least period of $R_j$ (`two_pow_leastExp_le`) and equals
     $L_{j+1}$, the cycle length of 1 under $\Phi(x) = x \oplus (2x \lor 4x)$ modulo $2^{j+1}$.
   - `rule30_twoIndex_not_recognizable_of_white_runs`: for every $C$ some row $2^k$ has a black cell on the diagonal
     $j + 1$ with $C(j + 1) < 2^k$, that is the white run $W(2^k)$ beside the right edge at time $2^k$ is shorter
     than $2^k / C$.
4. **Rule 30, the center** (Lean, `rule30_twoIndex_center_automatic`). If $R$ is 2-recognizable, the center column
   $c(t) = R(t, t)$ is 2-automatic.
5. **Rule 90** (Lean). Its array of right diagonals $(j, t) \mapsto \mathrm{cell}_{90}(t, t - j)$ is 2-recognizable,
   with at most four kernel elements (`rule90_twoIndex_recognizable`), and so is its diagram in time and column,
   $(t, x) \mapsto \mathrm{cell}_{90}(t, x)$ for $x \ge 0$, with at most six (`rule90_spacetime_recognizable`); the left
   half is the mirror image (the kit's `Rule30Realization.run_symm`). Row $2m$ of the first array is
   $\binom{t}{m} \bmod 2$ and row $2m + 1$ is white (`rule90_diag_eq`).

The hypothesis of item 3 is open. It is the conjecture of [right-edge cycles](../../findings/complexity/right-edge-cycles.md),
which holds on the computed range $n \le 61$, where $L_n/n$ reaches 550,072; the kit's lower bounds on $L_n$ are
linear (`Rule30RightPeriods.period_gt`, `per_bound`).

## Proof

**Item 1.** Let $K$ be the finite kernel. A section $g(v, w) = b(2^e v + r, 2^e w + s)$ has row 0
$t \mapsto b(r, 2^e t + s)$, row $r$ of $b$ read along an arithmetic progression; if row $r$ has period $p$ from $T$,
then $2^e p$ is also a period from $T$ and so $g$'s row 0 has period $p$ from $T$ (`per_mul_from`). Finitely many
eventually periodic sequences share an eventual period, the product of theirs from the largest threshold
(`common_period`); let $P$ and $T$ serve every row 0 of a section in $K$. For row $j$ take $e = \lfloor \log_2 j
\rfloor + 1$, so $j < 2^e \le 2(j + 1)$ (`exists_exp`). Write $t = 2^e q + s$ with $s < 2^e$. Then
$b(j, t) = g_s(0, q)$ for the section $g_s(v, w) = b(2^e v + j, 2^e w + s)$, which is in $K$ because $j < 2^e$; so
$b(j, t + 2^e P) = g_s(0, q + P) = g_s(0, q) = b(j, t)$ once $q \ge T$, that is once $t \ge 2^e T$. The period
$2^e P$ is at most $2P(j + 1)$, so $C = 2P$. If row $j$ is also periodic from time 0 with some period $q'$, an
eventual period $p$ is a period from time 0: $f(t + p) = f(t + p + Tq') = f(t + Tq') = f(t)$
(`per_of_eventual`).

**Item 2.** The section $n \mapsto b(2^e n + r, 2^e n + r)$ of the diagonal is the diagonal of the section
$(e, r, r)$ of $b$, so the list of diagonals of $K$ contains every one.

**Item 3.** Every row of $R$ is periodic from time 0 with period $2^j$, so a 2-recognizable $R$ would give, by item 1,
$C$ with a period of $R_j$ at most $C(j + 1)$ for every $j$, against the hypothesis. For the first form, a period $p$ of
$R_j$ and its period $2^j$ give the period $\gcd(p, 2^j)$ (the kit's `PerF.gcd`), a power of two $2^k$
(`dvd_two_pow_eq`), so $e_j \le k$ and $2^{e_j} \le p$. For the second, the cell $R_{j+1}(2^k)$ is black and
$R_{j+1}(0)$ is white, so $2^k$ is not a period of $R_{j+1}$, hence $e_{j+1} \ge k + 1$ and every period $p$ of $R_{j+1}$
has $p \ge 2^{k+1} > 2C(j + 1) \ge C(j + 2)$.

The two forms are equivalent to the first on paper. $2^{e_j} = L_{j+1}$: the first $j + 1$ diagonals return to their
values at time 0 exactly at the multiples of $L_{j+1}$ (the kit's `TFunctionCycles.seed_rows_return_iff`), and a period
of $R_j$ is a period of every $R_i$, $i \le j$ (`Rule30RightPeriods.per_mono_all`). And $L_n \le 2^m$ if and only if
$W(2^m) \ge n - 1$ (`Rule30RightPeriods.per_iff_gap`), so $L_n / n$ is unbounded if and only if
$\liminf_m W(2^m)/2^m = 0$: if $L_{j+1} = 2^{k+1} > C(j + 1)$, then $R_j$ does not have period $2^k$, so
$W(2^k) < j$ and $W(2^k)/2^k < 2/C$; conversely the computation in Lean above.

**Item 4.** $R(t, t) = \mathrm{cell}(t, 0)$, and item 2.

**Item 5.** Let $\mathrm{bsub}(m, t)$ say that every binary digit of $m$ is a digit of $t$, defined digit by digit
(`bsub`): $\mathrm{bsub}(m, 0) = [m = 0]$ and $\mathrm{bsub}(m, t) = [m_0 \le t_0] \land \mathrm{bsub}(\lfloor m/2
\rfloor, \lfloor t/2 \rfloor)$. Two properties are proved from the definition, without binomial coefficients:

- Pascal's rule, $\mathrm{bsub}(m + 1, t + 1) = \mathrm{bsub}(m + 1, t) \oplus \mathrm{bsub}(m, t)$ and
  $\mathrm{bsub}(0, t) = 1$ (`bsub_pascal`, `bsub_zero_left`), by induction on $t$ over the four parities of $m$ and
  $t$; so $\mathrm{bsub}(m, t) = \binom{t}{m} \bmod 2$, which is Lucas's theorem modulo 2.
- Digit splitting, $\mathrm{bsub}(2^e v + r, 2^e w + s) = \mathrm{bsub}(r, s) \land \mathrm{bsub}(v, w)$ for
  $r, s < 2^e$ (`bsub_split`), by induction on $e$.

Rule 90's update $x' = x_{-1} \oplus x_{+1}$ gives, in the coordinates of the right diagonals,
$R_{90}(j, t + 1) = R_{90}(j, t) \oplus R_{90}(j - 2, t)$ (white for $j < 2$, by the light cone), with
$R_{90}(j, 0) = [j = 0]$, so $R_{90}(j, t) = [j \text{ even}] \land \mathrm{bsub}(j/2, t)$ by Pascal's rule
(`rule90_diag_eq`). A section at level $e + 1 \ge 1$ halves the first index:
$(2^{e+1} v + r)/2 = 2^e v + \lfloor r/2 \rfloor$, and splitting $2^{e+1} w + s = 2^e (2w + \tau) + (s \bmod 2^e)$ at
the top digit $\tau$ of $s$ gives the section
$[r \text{ even}] \land \mathrm{bsub}(\lfloor r/2 \rfloor, s \bmod 2^e) \land \mathrm{bsub}(v, 2w + \tau)$
(`rd90_sect_succ`): a constant times one of two arrays. With the level-0 section, $R_{90}$ itself, the kernel has at most
four elements.

In time and column, $\mathrm{cell}_{90}(t, x) = [x \le t] \land [t - x \text{ even}] \land \mathrm{bsub}((t - x)/2, t)$
(`st90_eq`). At level $e + 1$ write $t = 2^{e+1} v + r$, $x = 2^{e+1} w + s$ and $\beta = [r < s]$, the borrow. Then
$x \le t$ exactly when $w + \beta \le v$, and in that case $t - x = 2^{e+1}(v - w - \beta) + d$ with
$d = r + 2^{e+1}\beta - s < 2^{e+1}$, so the section is a constant depending on $r, s$ times
$[w + \beta \le v] \land \mathrm{bsub}(v - w - \beta, 2v + \tau)$, $\tau$ the top digit of $r$ (`st90_sect_succ`):
four arrays, and with $\mathrm{cell}_{90}$ and the white array six.

## Checks

`computations/two_index.py` computes $L_n$ by level lifting and $W(2^m)$ from the integer rows, and runs the kernel
lemma's bound on controls (`python -m computations.two_index`). For $j < 64$ the least row period over $j + 1$ is at
most 1.00 for Rule 90 in these coordinates, 1.94 for Rule 150, 1.94 for the 2-automatic array
$\mathrm{popcount}(j \land t) \bmod 2$ and 3.00 for $[t \equiv j \pmod 3]$, while for Rule 30 it reaches 73 by $j = 27$ and
550,072 at $j = 60$. The number of distinct $16 \times 16$ windows of the kernel elements at level $e \le 7$ is 1, 3, 3,
... for Rule 90, 1, 3, 4, 4, ... for Rule 150 and $4^e$, every window distinct, for Rule 30. The test checks that every
window of a section of Rule 90 in both coordinate systems has the form that `rd90_sect_succ` and `st90_sect_succ` give.

## What it means

Two-index automaticity separates Rule 90 from Rule 30 conditionally on one statement about the right edge: Rule 90's
diagram is 2-automatic outright, and Rule 30's is not if $L_n / n$ is unbounded. That statement is about the cycles of
the right edge, which hold every diagonal at a fixed distance from it; it neither implies nor follows from Problem 1 by
any argument here, and no argument here makes $R$ recognizable from an eventually periodic center column. So it is a rung on which
periodicity of $c$ does not help, as [restricted models](../../negative-results/complexity/restricted-models.md) asks.
It is also weaker than the statement about $c$ that Problem 3 needs: computing $R(j, t)$ from both indices is at least
as hard as computing $c(t) = R(t, t)$, and item 4 shows that "$c$ is not 2-automatic", which implies Problem 1, already
implies that $R$ is not recognizable. The remaining gap is a superlinear lower bound for the right-edge cycles, about
which [right-edge cycles](../../findings/complexity/right-edge-cycles.md) records the data and
[automaton-group sections](../../negative-results/complexity/automaton-group-sections.md) one route that stops.

Linear cellular automata from a finite row give automatic diagrams (Allouche, von Haeseler, Peitgen and Skordev 1996;
with Petersen 1997 for the two-index form; Rowland and Yassawi 2020, in
[measure and analogs](../../literature/measure-and-analogs.md)), so item 5 is a known case, proved here in Lean. A
search found no statement that Rule 30's diagram is not 2-automatic, and none that its right-diagonal periods (OEIS
A094605) grow faster than linearly; the kernel lemma is an elementary consequence of the definition, and no source
stating it was found.

The kit has the definition in its Mathlib-based form, `BuchiArithmetic.Recognizable` (a relation on $\mathbb{N}^\iota$
whose sections are finitely many) with closure lemmas, `Automatic.IsAutomatic`, and Lucas's theorem modulo 2
(`DiophantineGraph.sub_iff_odd_choose`); it has no two-index statement about a cellular automaton's diagram, no bound on
row periods, and no Rule 90 diagram. A pair-alphabet form of the kit's `OneTapeRegular.isRegular_digitLang_iff` would
turn non-recognizability of $R$ into a one-tape time bound not $o(\ell \log \ell)$ for computing $R(j, t)$ from the
interleaved digits; it is not proved here.

## Reproduce

```bash
lake build Rule30Open.Complexity.TwoIndex
python -m computations.two_index
```

The computation takes about nine seconds and 200 MB.
