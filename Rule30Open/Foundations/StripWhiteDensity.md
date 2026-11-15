---
title: In every Rule 30 orbit every strip of J >= 5 adjacent columns has at least 2J(n - 1)/5 white cells in its first n rows, sharp at the orbit of (11001)^infinity; four columns are at least 11/28 white (computed)
category: foundations
problems: [2]
status: proved
lean: Rule30Open.Foundations.StripWhiteDensity
headline: [StripWhiteDensity.strip_white_ge5, StripWhiteDensity.strip5_white, StripWhiteDensity.strip6_white, StripWhiteDensity.strip7_white, StripWhiteDensity.strip8_white, StripWhiteDensity.strip9_white]
kit: new
kit_modules: [Rule30Jen]
evidence: [computations/strip_cycle_mean.py, computations/strip_potentials.py, tests/test_strip_white_density.py]
---

# In every Rule 30 orbit every strip of J >= 5 adjacent columns has at least 2J(n - 1)/5 white cells in its first n rows, sharp at the orbit of (11001)^infinity; four columns are at least 11/28 white (computed)

Let $x_0, x_1, \dots$ be any orbit of Rule 30, from any initial row. Write $W$ for the white cells of the columns
$a, \dots, a + J - 1$ at the times $0, \dots, n - 1$.

**Theorem.**

1. *(Widths 5 to 9, in Lean.)* For $J = 5, 6, 7, 8, 9$: $2J n \le 5W + 2J$, that is $W \ge 2J(n - 1)/5$
   (`strip5_white` to `strip9_white`).
2. *(Every width $J \ge 5$, in Lean.)* $2Jn \le 5W + 2J$, that is $W \ge 2J(n - 1)/5$ (`strip_white_ge5`). By induction on
   $J$: widths 5 to 9 are part 1, and a strip of width $J \ge 10$ is a strip of width 5 followed by one of width
   $J - 5 \ge 5$, whose white counts add (`stripW_add`).
3. *(Sharp.)* The orbit of $(11001)^\infty$ attains $2/5$ on every strip. Rule 30 maps the row to its shift by two cells
   (`RowWhiteDensity.period_five_shift`, in Lean), and $\gcd(2, 5) = 1$, so in 5 consecutive steps each column runs
   through all five phases and has exactly 2 white cells. A strip of $J$ columns then has exactly $2Jn/5$ white
   cells when $5 \mid n$ (checked in the test for $J \le 11$; the argument is on paper).

So for every $J \ge 5$ the sharp lower white density of $J$ adjacent columns over all orbits is exactly $2/5$.

**Four columns.** The method of part 1 gives only $3/8$ with the strip alone, and $11/28$ with four remembered columns
to the right ($3/8$ with up to three), all below $2/5$ (`python -c "from computations.strip_cycle_mean import cycle_mean;
print(cycle_mean(4, 0), cycle_mean(4, 4))"`; these are computed, not in Lean). Spatially periodic orbits of period at
most 12 do not go below $2/5$ on four columns (`row_white_density.periodic_strip_min`). So the sharp constant for
$J = 4$ lies in $[11/28, 2/5]$ and is open, as it is for two columns
([PairWhiteDensity](PairWhiteDensity.md): $[5/18, 1/3]$). Three columns are exactly $1/3$.

*Meaning.* A block of at least five columns around the center column is at least $2/5$ white in every orbit, hence in
the single cell's orbit, and no argument valid for every orbit gives more. The center column alone gets nothing,
since $(10)^\infty$ has a column that is black at every time, and black cells get nothing.

## Proof of part 1

The proof telescopes in time on the fixed strip, as for three columns in [PairWhiteDensity](PairWhiteDensity.md). For
each width there is a table $\varphi_J$ on the $2^J$ contents of the strip, with values in $[0, 2J]$, such that for every
content $s$ of the strip and every value of the two cells beside it,
$$\varphi_J(s') + 2J \le \varphi_J(s) + 5 \cdot \#\{\text{white cells of } s\},$$
where $s'$ is the next content of the strip (`step5` to `step9`, by `decide` over $2^{J+2}$ cases). Summing over the
times $0, \dots, n - 1$ gives $2Jn + \varphi_J(s_n) \le \varphi_J(s_0) + 5W$ (`aux5` to `aux9`).

The tables are the shortest-path potentials of the graph whose states are the strip's contents and whose edges are
the steps for every value of the two outside cells, with edge weight $5 \cdot \text{whites} - 2J$
(`strip_cycle_mean.potential(J, 0, 2, 5)`; `computations/strip_potentials.py` prints them and writes the module). They exist because the minimum cycle mean of white cells per cell is
exactly $2/5$ for $J = 5, 6, 7, 8, 9$ (`strip_cycle_mean.cycle_mean`).

## Reproduce

    lake build Rule30Open.Foundations.StripWhiteDensity      # about 35 s, most of it the 2^11 cases of width 9
    python -m computations.strip_potentials --tables 5 6 7 8 9   # the potential tables
    python -m computations.strip_potentials --emit-lean > Rule30Open/Foundations/StripWhiteDensity.lean
    python -m pytest tests/test_strip_white_density.py
