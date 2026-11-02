---
title: Right halves whose first 18 cells lie in the forced basin enter the period-four family whatever lies beyond
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ForcedBasin18
headline: [forcedBasin_0001_18, forcedBasin_0011_18, forcedBasin_0111_18]
kit: refines
kit_modules: [Rule30Ether, Rule30WhiteEndNine, Rule30StripCertificates]
evidence: [computations/forced_basin.py]
---

# Right halves whose first 18 cells lie in the forced basin enter the period-four family whatever lies beyond

The statement of [ForcedBasin](ForcedBasin.md) at width 18, for the three words of least period four: every driven
right half, finite or infinite, whose first 18 cells form a window of the forced basin enters the kit's ether-and-wall
family by step $R$; for every $n \ge 18$ the halves of $n$ cells that do are $|B_{18}| \cdot 2^{n - 18}$; and no finite
configuration that starts with such a window at an onset of the word has a center that repeats it.

| word | $\lvert B_{18} \rvert$ at phases 0, 1, 2, 3 | of $2^{18}$ | $R$ | theorem |
|---|---|---|---|---|
| $0001$ | 21,588, 21,096, 19,829, 18,456 | 7.0% to 8.2% | 42 | `forcedBasin_0001_18` |
| $0011$ | 60,151, 59,169, 57,797, 55,883 | 21.3% to 22.9% | 53 | `forcedBasin_0011_18` |
| $0111$ | 87,964, 86,442, 84,527, 85,589 | 32.2% to 33.6% | 64 | `forcedBasin_0111_18` |

## Argument

As in [ForcedBasin](ForcedBasin.md), with the kernel's rounds cut into parts. At width 18 one round holds tables of
$2^{22}$ bits, and the kernel keeps every intermediate table of a check, so all rounds in one check would take too much
memory. The rounds are cut into parts of at most 16: the module stores the set of nodes of rank at most the end of
each part but the last, as $4 \cdot 2^{18}$ bits (`ck0001_18_1` and the rest, eight sets, about 2.1 MB of
hexadecimal), and the kernel checks that each part, run from the stored set before it, ends exactly at the next
(`ck0001_18_1_ok` and the rest). The last part ends with the counts. `ForcedBasin.basinFrom_add` joins the parts, so
each theorem is about the basin after all $R$ rounds from the target, as at widths 14 and 16. The stored sets come from
`python -m computations.forced_basin lean --width 18 --size 16`, which writes the module; the kernel recomputes each
of them, so they carry no trust.

The module builds in about 9 minutes with a peak near 3.3 GB, its checks one at a time (`Elab.async false`). Width 20
would need parts of about 4 rounds and sets of 1 MB each, about 40 MB for the three words, so it is left to the
computation: the shares there and up to width 24 are in [ForcedBasin](ForcedBasin.md).

## Lean

`Rule30Open.Columns.ForcedBasin18`: the stored sets `ck<word>_18_<i>`, their checks `ck<word>_18_<i>_ok`, the counts
`counts<word>_18`, and `forcedBasin_0001_18`, `forcedBasin_0011_18`, `forcedBasin_0111_18`, each a
`ForcedBasin.Covers`.
