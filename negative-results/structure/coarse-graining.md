---
title: Rule 30 has no coarse-graining with blocks of up to 8 cells
category: structure
problems: [1, 3]
status: negative
kind: no-signal
---

# Rule 30 has no coarse-graining with blocks of up to 8 cells

**Question.** Is there a coarse-graining of Rule 30: a partition of blocks of $b$ cells into classes that commutes with
$T$ steps of the rule, so that a simpler automaton computes the coarse pattern? Israeli and Goldenfeld coarse-grained
240 of the 256 elementary rules and could not do Rules 30, 45, 106, 154 and their symmetries, which they suspected was a
limit of computing power ([Phys. Rev. E 73, 026203, 2006](https://arxiv.org/abs/nlin/0508033)).

**Method.** Every valid partition other than the identity contains the closure of some merged pair of block states
(the finest valid partition merging it), so the closures of all pairs decide existence exactly. They were computed for
$b = 2$ to 8 with $T = b$, and every $T$ from 1 to $b$ for $b \le 5$; the closure code was checked against exhaustive
enumeration of every partition at $b = 2$ and 3 on nine rules.

**Outcome.** Every one of the 6, 28, 120, 496, 2,016, 8,128 and 32,640 pair closures at $b = 2$ to 8 collapses to a
single class: no nontrivial coarse-graining exists. On the block triples the single cell's orbit actually shows (to
$t = 4{,}096$), none exists for $b = 2$ to 7; one apparent merge at $b = 8$ disappeared with more steps, an artifact of
coverage. The controls are found: Rules 90 and 150 to themselves at $b = 2$, Rule 105 to Rule 150, Rule 146 to Rule 128
at $b = 3$, and 3-state coarse-grainings of Rules 184 and 232. Rule 30's three-color square roots are exactly the three
in *A New Kind of Science*, which differ only on an unused pair; their intermediate state encodes the pair 00, 01 or 1*
and adds no structure.

**What it means.** The question Israeli and Goldenfeld left open is settled negatively for blocks up to 8 cells.

**Evidence.** Quoted from a C kernel for the closures that is not in this repository.
