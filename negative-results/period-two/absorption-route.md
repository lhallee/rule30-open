---
title: The ether-and-wall family does not catch the right half beside an alternating center
category: period-two
problems: [1]
status: negative
kind: dead-end
evidence: [computations/absorption.py, computations/lock_word.py]
---

# The ether-and-wall family does not catch the right half beside an alternating center

**Idea.** The kit aligns the alternating word with its ether: $0101$ is ether column $B_4$
(`Rule30Ether.aligned_0101_3`, and the same column two steps later). The kit's `absorption_excludes` takes any word and
any list of alignments, so `Absorption w0101 [(3, 0), (3, 2)]`, every finite right half driven by an alternating center
entering the ether-and-wall family, would exclude an eventual period two, just as the three absorption statements
exclude period four. Under the words of period four every right half of up to 20 cells enters
([the absorption census](../../findings/columns/absorption-census.md)).

**Where it stops.** Beside an alternating center almost no right half enters. Of the 16,384 right halves of at most
14 cells, 484 enter within 4,000 steps when the center reads 0 first and 453 when it reads 1 first, all by step 122;
the other 97% stay out for the whole run. The white right half stays out for 20,000 steps in every phase. Under the
words of period four, by contrast, the fraction still outside falls by a steady factor every 100 steps; here it stays
at 0.97 from step 100 to step 400 and beyond.

The kit's open pull request #39 claims a Lean proof that the white right half never enters, in every alignment
(`not_absorption_alt`), so `Absorption` is false for the alternating word
([the kit's pull requests](../../literature/kit-pull-requests.md#period-two)).

**Not even with help from the right.** Let the column right of a window of $W$ columns take any values at all. Under
each word of period four, every window from the least width at which the family fits up to 21 columns can be brought
into it, within at most 114 steps, and [LockWord](../../Rule30Open/Columns/LockWord.md) turns one such sequence into a
theorem. Beside an alternating center, 45% to 48% of the windows of 19 columns, by phase, 49% to 52% of those of 20
and 83% to 84% of those of 21 can never enter, whatever that column does
(`python -m computations.lock_word --reach 19 20 21`, from
[computations/lock_word.py](../../computations/lock_word.py)). The obstruction sits in the columns next to the center,
not in the far right half.

**Why.** Column 1 beside an alternating center nearly locks into a pattern of period 36 and keeps slipping, about once
per 145 steps ([the right channel](../../findings/period-two/right-channel.md)). Inside the family column 1 would repeat
at the white times, which the slips never allow, so the family is out of reach for almost every start. The halves that
do enter are absorbed at once rather than after a wait.

**What it means.** For period two the right half keeps sending fresh information into column 1, and the left half has
to absorb it: the kit's `Q01` and `CQ01`. The first case of the coupled question shows the split. Against a white right
half, absorption settles the words of period four outright ([EmptyRight.md](../../Rule30Open/Columns/EmptyRight.md)),
while for the alternating center the one candidate left half looks random to depth $2^{20}$
([the white right half](../../findings/period-two/white-right-half.md)).

**Evidence.** `python -m computations.absorption census --cells 14 --words 0101` (about 3 min) and
`python -m computations.absorption census --cells 0 --steps 20000 --words 0101`, in
[computations/absorption.py](../../computations/absorption.py).
