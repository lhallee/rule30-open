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

The lock is not a finite shield. The conditions that hold column 1 fixed at a white phase run down a chain of OR
updates into the chaotic part of the right half, so no bounded window of cells next to the center certifies it.

## Why it would matter

The kit's masked form of Jen's theorem
([`Rule30MaskedJen`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/7d665044b904117af9e82328aeb90a30692b2b85/lean/Ruliology/CellularAutomata/Rule30MaskedJen.lean),
`masked_jen`) says that if the center column has period $P$ from some time, column 1 does not have period $P$ at the
white times of the center. The single cell's right half at any time is finite. So a proof that every finite right half
locks under $w$ excludes $w$ as the center's eventual period, and doing so for the three words above excludes least
period 4 entirely. The finite game ([FiniteGame.md](../../Rule30Open/Columns/FiniteGame.md)) cannot do it, because
it lets the free cell break the lock.

## Reproduce

```bash
python -m computations.right_half 12000 30 --max-period 7
```

[computations/right_half.py](../../computations/right_half.py) runs in about 15 s.
