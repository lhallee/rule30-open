---
title: The linear complexity is n/2, the most a sequence can have
category: complexity
problems: [1, 3]
status: negative
kind: no-signal
evidence: [computations/linear_complexity.py]
---

# The linear complexity is n/2, the most a sequence can have

**Question.** Does a short linear recurrence over GF(2) produce the center column, or an eventual period hide behind a
long preperiod?

**Method.** Berlekamp-Massey gives the order of the shortest linear recurrence that produces each prefix. An
eventually periodic sequence has linear complexity at most its preperiod plus its period, and a random one tracks
$n/2$.

**Outcome.** The first $2^{20}$ cells have linear complexity 524,288, and over every prefix the profile stays within
9.5 of $n/2$ (ChaCha20: within 8.5). So no linear recurrence of order below 524,288 produces them, and the column is not
eventually periodic with preperiod plus period below 524,288 within them. Controls: the two shift registers give exactly
31 and 1,279, and automatic controls stay within 1 to 11 of $n/2$.

**What it means.** The column has no linear structure over GF(2) at this length. It bounds Problem 1 only inside the
computed range. The kit's equivalent forms prove in Lean that Problem 1 is the statement that this profile is
unbounded, since a sequence is eventually periodic exactly when its generating function over GF(2) is rational
([`PowerSeriesF2`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/equivalents/Rule30Equivalents/PowerSeriesF2.lean): `problem1_iff_linear_complexity_unbounded`), and that a random sequence has profile $n/2 + O(\log n)$, the behavior
seen here ([`LinearComplexity`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/equivalents/Rule30Equivalents/LinearComplexity.lean)).

**Reproduce.** [computations/linear_complexity.py](../../computations/linear_complexity.py) runs Berlekamp-Massey on
Python integers: $2^{14}$ cells in under a second (complexity 8,192, largest gap 6), $2^{16}$ in seconds; its cost
grows with $n^2$, so the $2^{20}$ result came from compiled code that is not in this repository.

```bash
python -m computations.linear_complexity 65536
```
