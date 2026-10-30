---
title: The period-four certificates are traps, and entry into one excludes its word
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.PeriodFourCertificate
headline: [cert0001_check, cert0011_check, cert0111_check, not_eventually_0001_of_certificate,
  not_eventually_0011_of_certificate, not_eventually_0111_of_certificate]
kit: new
kit_modules: [Rule30Ether, Rule30MaskedJen]
evidence: [computations/lock_certificate.py]
---

# The period-four certificates are traps, and entry into one excludes its word

[The period-four certificate](../../findings/columns/period-four-certificate.md) computes, for each word of least
period four, the greatest family of windows of the right half, one set per phase, that the driven rule never leaves
whatever the cell beyond the window does, and on which column 1 is fixed at the white phases: at width 16 for $0001$
and 14 for $0011$ and $0111$. Here those families are checked in Lean as labelled traps of
[WordTraps](WordTraps.md), and each gives the kit's reduction to entry for its word.

## Statement

1. **The traps** (`cert0001_check`, `cert0011_check`, `cert0111_check`). `cert0001` has 2,611 windows of 16 cells,
   `cert0011` 1,915 and `cert0111` 4,898 of 14 cells, with labels modulo 4; each passes the check of
   [WordTraps](WordTraps.md): every window steps into a window of the set for both values of the cell beyond, with the
   label one more, and column 1 has one value at each white label.
2. **The reduction** (`not_eventually_0001_of_certificate` and the two others). If every finitely supported right
   half driven by the word, from any phase, enters its certificate (`WTrap.Absorption`), the center column does not
   eventually repeat the word.

## Argument

1. **The sets.** For each assignment of column 1 at the white phases, the finding's removal passes give the greatest
   family inside it that the rule maps into itself; for each word exactly one assignment leaves a nonempty family, at
   the widths above (`certificate_tables` in [computations/lock_certificate.py](../../computations/lock_certificate.py)).
   The kernel checks the family, so the passes are not trusted.
2. **The reduction** is [WordTraps](WordTraps.md)'s `absorption_excludes`: entry fixes column 1 at the white times,
   which masked Jen and Jen's theorem on adjacent columns rule out beside a column that repeats the word.

## What it covers

Being the greatest such family at its width, each certificate contains every trap of that width with labels modulo 4
and the same values of column 1 at the white phases. The kit's ether-and-wall family puts its wall at any distance
from the center, so no family of one width contains it, and the two entry statements differ: each, if every finite
half satisfies it, excludes the word. By computation, 30 of 31 sample
starts enter the certificate of $0001$ at width 16, 17 of 31 enter that of $0011$ at width 14, and 29 of 31 that
of $0111$ ([the finding](../../findings/columns/period-four-certificate.md)), while every right half of up to 20
cells enters the kit's family ([the census](../../findings/columns/absorption-census.md)). Entry for every finite half
stays open for both.

## Relation to the kit

The kit's reduction of the words of period four goes through its ether-and-wall family
([`Rule30Ether`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Ether.lean))
and masked Jen
([`Rule30MaskedJen`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30MaskedJen.lean));
the certificates are not in the kit.

## Lean

`Rule30Open.Columns.PeriodFourCertificate`: `cert0001`, `cert0011`, `cert0111`, their checks and the three reductions.
The tables come from `python -m computations.lock_certificate --lean`.
