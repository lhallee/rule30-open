---
title: Every truncation of the aligned ether, followed by any word of up to six cells, enters the ether-and-wall family
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.EtherPrefixSix
headline: [prefix_of_tails_len, etherPrefixSix_0001, etherPrefixSix_0011, etherPrefixSix_0111, prefixSixRight_0001, prefixSixRight_0011, prefixSixRight_0111]
kit: refines
kit_modules: [Rule30Ether, Rule30EtherThreeReach]
evidence: [computations/ether_prefix.py]
---

# Every truncation of the aligned ether, followed by any word of up to six cells, enters the ether-and-wall family

[EtherPrefix](EtherPrefix.md) proves that the right half which is the aligned ether on cells $1, \dots, K$, then any
word of at most four cells, then white, enters the kit's ether-and-wall family for every $K$. Here the word has up to
six cells, four times as many tails, by the same argument and new certificates.

## Statement

Drive a right half with the center repeating a word $w$ of least period four from phase $\varphi$, and let $x_{K,u}$
be the ether aligned through one of the kit's alignments of $w$ on cells $1, \dots, K$, then the word $u$, then white
(`prefixHalf`).

1. **The three words** (`etherPrefixSix_0001`, `etherPrefixSix_0011`, `etherPrefixSix_0111`). For each word, each of
   its alignments and every phase, $x_{K,u}$ enters the family for every $K$ and every word $u$ of at most six cells.
2. **The exclusion** (`prefixSixRight_0001`, `prefixSixRight_0011`, `prefixSixRight_0111`). No finite configuration
   whose right half is such an $x_{K,u}$ has a center column that repeats the word, whatever its left half.
3. **Any number of tails** (`prefix_of_tails_len`). EtherPrefix's `prefix_of_tails` for a checked list of any length.

## Argument

As in [EtherPrefix](EtherPrefix.md): seven more columns of ether in front of a half that enters, with column 1 the
ether's until then, give a half that enters at the same step (`shift7_family`), so one base per residue of $K$ modulo
7 and a direct check of every shorter truncation give every $K$ (`prefix_absorption`). The kernel checks the 64 tail
words for each of the 24 pairs of alignment and phase, one computation per pair (`six0001_5_0_ok` and the others).
Over the 64 tails $B$ is at most 46, the bases enter by step 246 and the shorter truncations by step 784, the numbers
that EtherPrefix reports for this extension from `python -m computations.ether_prefix --tail 6`. The module builds in
about ten minutes with a peak near 1.8 GB.

## What it covers

Statement 1 contains EtherPrefix's first statement, since a word of at most four cells is a word of at most six. The
argument still does not reach the infinite ether, nor the halves that enter last in the census, which agree with a
rotation of the ether on at most their first 7 cells.

## Relation to the kit

The family, the trap, the alignments and masked Jen are the kit's
([`Rule30Ether`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Ether.lean)),
and the packed half is its `Rule30EtherThree.rowN`, as in EtherPrefix.

## Lean

`Rule30Open.Columns.EtherPrefixSix`: `prefix_of_tails_len`, the certificate lists `six<word>_<j0>_<phase>` with their
24 kernel checks, `etherPrefixSix_*`, `PrefixSixRight` and `prefixSixRight_*`.
