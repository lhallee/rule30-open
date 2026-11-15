---
title: In the orbit of (11001)^infinity every strip of J columns has exactly 2Jn white cells in its first 5n rows, so the strip bound 2/5 is sharp
category: foundations
problems: [2]
status: proved
lean: Rule30Open.Foundations.StripWhiteSharp
headline: [StripWhiteSharp.strip_sharp, StripWhiteSharp.f_orbit]
kit: new
kit_modules: [Rule30Jen]
---

# In the orbit of (11001)^infinity every strip of J columns has exactly 2Jn white cells in its first 5n rows, so the strip bound 2/5 is sharp

**Theorem.** Let $f(t, p) = x(p + 2t)$ with $x = (11001)^\infty$. Then $f$ is an orbit of Rule 30 (`f_orbit`), and for
every column $a$, every width $J$ and every $n$, the columns $a, \dots, a + J - 1$ have exactly $2Jn$ white cells at the
times $0, \dots, 5n - 1$ (`strip_sharp`). So the lower bound $W \ge 2J(n - 1)/5$ of
[StripWhiteDensity](StripWhiteDensity.md) (`strip_white_ge5`, every $J \ge 5$) cannot be improved beyond its additive
constant, and $2/5$ is the sharp lower white density of every strip of at least five columns over all orbits.

## Proof

Rule 30 maps $x$ to its shift by two cells ([RowWhiteDensity](RowWhiteDensity.md), `period_five_shift`), so row $t$
of the orbit is $x$ shifted by $2t$ (`f_orbit`). Column $c$ at the times $5m, \dots, 5m + 4$ reads
$x(c'), x(c' + 2), x(c' + 4), x(c' + 6), x(c' + 8)$ with $c' = c + 10m$: these are the five residues modulo 5, since
$\gcd(2, 5) = 1$, and the period $11001$ has two white cells (`col_five`, five cases). Summing over the $J$ columns
gives $2J$ white cells in every block of five rows (`block_eq`), and summing over the $n$ blocks gives $2Jn$
(`strip_sharp`).
