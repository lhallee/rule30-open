---
title: The three words of period four lock the right half
category: columns
problems: [1]
status: conjecture
formalization: wanted
evidence: [computations/right_half.py]
---

# The three words of period four lock the right half

Drive a finite right half with a center column that repeats a word $w$. For the three primitive words of period 4,
$0001$, $0011$ and $0111$, column 1 at the white times of $w$ becomes periodic with period 4 from every start tried.
Two other words lock from some starts only, and the remaining 34 primitive words of period 2 to 7 from none. If the
locking holds for every finite right half, masked Jen excludes least period 4 for the center column. That is a
concrete open lead.

## Observation

From the empty right half and from 30 random right halves of 64 cells, over 12,000 steps, testing whether column 1 at
the white times repeats over the second half with some multiple of the word's period:

- $0001$, $0011$, $0111$: column 1 locks for all 31 starts, with period 4.
- $001$ locks for 3 starts (period 21) and $01111$ for 9 (period 10).
- The other 34 primitive words of period 2 to 7, $01$ and $011$ among them: it locks for none.

The same test at longer periods counts the primitive words that lock for all 31 starts:

| period | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| primitive words | 1 | 2 | 3 | 6 | 9 | 18 | 30 | 56 | 99 | 186 | 335 |
| lock for every start | 0 | 0 | 3 | 0 | 0 | 0 | 8 | 0 | 17 | 35 | 46 |

The eight of period 8 are $00000001$, $00000011$, $00000101$, $00011101$, $00011111$, $00111101$, $00111111$ and
$01111111$. No word of period 9 locks for more than one start, although periods 8, 10 and 11 lock often; that gap is
unexplained.

## A finite certificate

A bounded window does certify the lock from most starts. For each of the three words there is a finite, nonempty set of
states of columns 1 to 16, one set per phase, that the rule never leaves whatever the cell beyond column 16 does, and on
which column 1 at the white times is fixed. Of the 31 starts, 30 enter it under $0001$ and $0011$ and 29 under $0111$;
at width 20 all 31 enter under $0111$. One start under $0001$ locks but never enters, with a periodic plug next to the
center. [The certificate finding](period-four-certificate.md) gives the sets, the entry times and the outliers.

This corrects an earlier reading of the evidence, which held that the lock is not a finite shield: that the conditions
holding column 1 fixed at a white phase run down a chain of OR updates into the chaotic part of the right half, so that
no bounded window certifies it. The chain is real. The cells forced at each phase do not sustain themselves under the
rule, and the forced values further out are held by relations among cells that are not themselves forced. What was
wrong is the conclusion: a nonlinear invariant set of width 16 contains the chain, so a bounded window does certify
the lock from its own states. What it does not certify is that every right half reaches those states.

## Why it would matter

The kit's masked form of Jen's theorem
([`Rule30MaskedJen`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/7d665044b904117af9e82328aeb90a30692b2b85/lean/Ruliology/CellularAutomata/Rule30MaskedJen.lean),
`masked_jen`) says that if the center column has period $P$ from some time, column 1 does not have period $P$ at the
white times of the center. The single cell's right half at any time is finite. So a proof that every finite right half
locks under $w$ excludes $w$ as the center's eventual period, and doing so for the three words above excludes least
period 4 entirely. The finite game ([FiniteGame.md](../../Rule30Open/Columns/FiniteGame.md)) cannot do it, because
it lets the free cell break the lock. With [the certificate](period-four-certificate.md), what remains is attraction:
that every finite right half enters a certificate set. The kit states attraction into its ether-and-wall family, which
contains the certificate, as the open `Rule30Ether.Absorption`, and
[the absorption census](absorption-census.md) finds that every right half of up to 20 cells enters that family, for
each word and phase. For $0001$, [EtherDomain.md](../../Rule30Open/Columns/EtherDomain.md) reduces the same question
on the left half to an integer condition.

## Reproduce

```bash
python -m computations.right_half 12000 30 --max-period 7
python -m computations.right_half 12000 30 --min-period 8 --max-period 12
```

[computations/right_half.py](../../computations/right_half.py) runs the first in about 15 s and the second in about
5 min.
