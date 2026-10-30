---
title: One word in a column beside the center forces the period-four lock, for each of the three words
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.LockWord
headline: [lockWord_column, family_contra, lock_0001, lock_0011, lock_0111, center_lock_0001, center_lock_0011, center_lock_0111, center_not_0001_of_word, center_not_0011_of_word, center_not_0111_of_word]
kit: new
kit_modules: [Rule30Ether, Rule30FiniteMaskedJen, Rule30StripCertificates]
evidence: [computations/lock_word.py]
---

# One word in a column beside the center forces the period-four lock, for each of the three words

Suppose the center column repeats $0001$, $0011$ or $0111$ from time $T$. The kit reduces the exclusion of these words
to its open `Absorption`: every finite right half should enter its ether-and-wall family, and entry gives a
contradiction by masked Jen. Here one fixed sequence of values in one column brings the cells between it and the center
into the family, from every state and every phase. For $0001$ it is a sequence of 1,193 values in column 17, for $0011$
one of 955 values in column 15, and for $0111$ one of 381 values in column 14. So once the center repeats the word, that
column never reads that sequence again, and if the column reads it at arbitrarily late times, the center does not
eventually repeat the word. This is the deterministic form of [the coin lock](../../findings/columns/coin-lock.md).

## Statement

Let $w$ be one of the three words, and let column $K + 1$ be column 17, 15 or 14 for $w = 0001$, $0011$, $0111$, with
sequences `word0001`, `word0011`, `word0111` of $L$ = 1,193, 955 and 381 values.

1. `lock_0001`, `lock_0011`, `lock_0111`: in the orbit of a row with a leftmost 1, if the center reads
   $w[(t - T) \bmod 4]$ at every time $t \ge T$, then for every $t_0 \ge T$ column $K + 1$ differs from the sequence at
   one of the times $t_0, \dots, t_0 + L - 1$.
2. `center_lock_0001`, `center_lock_0011`, `center_lock_0111`: the same for the center column of the single cell.
3. `center_not_0001_of_word`, `center_not_0011_of_word`, `center_not_0111_of_word`: if column $K + 1$ of the single
   cell's orbit reads the sequence from arbitrarily late times, the center column does not eventually repeat $w$, in
   any rotation.
4. `lockWord_column`: the general form, for any word, alignment and depth at which the kit's family fits in the
   $K$ columns, when the kernel check `lockCheck` holds for the sequence.
5. `family_contra`: entry into the family excludes the word for every row with a leftmost 1, the kit's
   `ether_wall_trap` stated beyond the single cell through its masked Jen for such rows.

## Argument

1. **The family** (the kit). Columns $1, \dots, k$ carry the ether aligned with the center, column $k$ is a $B_3$
   column, and columns $k + 1, \dots, k + 13$ are one of the kit's 109 wall states. The rule never leaves this set,
   whatever happens beyond column $k + 13$ (`trap_invariant`), and in it column 1 repeats with period 4 at the white
   times of the center, against masked Jen (`family_contra`). With $K = 16$, 14 and 13 columns the family fits at depth
   $k = 3$, 1 and 0 for the alignments $(6, 0)$ of $0001$, $(1, 3)$ of $0011$ and $(2, 2)$ of $0111$; these are the
   least $K$ at which an alignment of the word fits.
2. **The window.** Columns $1, \dots, K$ at time $t + 1$ follow from the same columns at time $t$, the center, and
   column $K + 1$ (`codeFrom_succ`). From $t_0 \ge T$ the center is known, so if column $K + 1$ reads the sequence, the
   window at time $t_0 + L$ is a known function of the window at $t_0$ and of the phase $(t_0 - T) \bmod 4$
   (`codeFrom_wrun`).
3. **All windows at once** (`sinit`, `sstep`, `srun_spec`). Slice $j$ is one number whose bit $p \cdot 2^K + r$ is
   column $j + 1$ of the window that started as $r$ at phase $p$, for all $4 \cdot 2^K$ starts. One step of every
   window is Rule 30 on the $K$ slices, with the center of each start's phase and the value of column $K + 1$ as masks.
4. **Entry** (`trapHit`, `trapHit_spec`, `lockCheck`). For each wall state, the family's window (the ether columns,
   then the wall cells) is matched against the slices by $K$ masked ANDs, restricted to the starts whose final phase is
   the wall state's. The kernel checks that every bit is matched, so every window ends in the family, and step 1 gives
   the contradiction.

## The sequences

[computations/lock_word.py](../../computations/lock_word.py) finds them greedily: from the window closest to the
family, by the shortest path of values of column $K + 1$, it moves every window along and repeats until all are in.
It checks the result with the same slices. The sequences are mostly white: $0001$'s has 142 black values, the longest
black run 2 and a white run of 197; $0011$'s has 181, after 82 white values; $0111$'s has 37, after 120. They need not
be the shortest. The kernel checks all three in about 90 seconds with a peak near 5 GB, most of it in $0001$'s 1,193
steps on slices of $2^{18}$ bits.

## What it means

Before the center repeats one of the three words for good, every right half must keep column $K + 1$ off one specific
sequence forever. A column that contains every finite word at arbitrarily late times, as a normal sequence does, would
exclude the word, so least period four is excluded for the single cell if columns 14, 15 and 17 of its orbit are normal;
that is a statement of the same kind as Problem 2 for those columns, and open. [The coin
lock](../../findings/columns/coin-lock.md) shows that a fair coin in column 17 reaches its certificate with probability
1, while some of Rule 30's own right halves stay out of it for 12,000 steps and enter the kit's family through ether
plugs deeper than the window. So the condition here is sufficient, not necessary: the open `Absorption` asks for entry
at any depth, and this result reads only the first $K$ columns. Beside an alternating center no such sequence exists at
19 to 21 columns, the widths where the family first fits: about half the windows of 19 or 20 columns, and more of 21,
can never enter it, whatever the next column does ([the absorption route for period
two](../../negative-results/period-two/absorption-route.md)).

## Relation to the kit

The family, its invariance and the alignments are the kit's (`Rule30Ether`); masked Jen for rows with a leftmost 1 is
`Rule30FiniteMaskedJen.masked_jen`, and the step on window codes is `Rule30StripCertificates.stripStep`. The kit proves
entry under $0001$ for one black cell and for halves white on columns 1 to 30 (`Rule30EtherSingleCell`), and states
entry for every finite half as the open `Absorption`; it has no condition on one column that forces entry.
[EmptyRight](EmptyRight.md), [TenCells](TenCells.md), [SparseRight](SparseRight.md), [WhiteGap](WhiteGap.md) and
[EtherPrefix](EtherPrefix.md) prove entry for classes of right halves; this module proves it for every half whose column
$K + 1$ reads the sequence.

## Lean

`Rule30Open.Columns.LockWord`: `evolve_eq_evol`, `family_contra`; in `Rule30Open.LockWord`, the masks `ones`, `sel`,
`sel_testBit`, `bitOf_eq`, the slices `sinit`, `sstep`, `srun`, `wrun`, `sinit_spec`, `sstep_spec`, `srun_spec`,
`wrun_mod`, the entry check `matchS`, `etherBits`, `listBits`, `code`, `code_low`, `code_high`, `trapHit`,
`trapHit_spec`, `lockCheck`, and the sequences `word0001`, `word0011`, `word0111` with `bitsOf`; then
`codeFrom_wrun`, `lockWord_column`, the checks `check_0001`, `check_0011`, `check_0111`, `lock_of_check`,
`lock_0001`, `lock_0011`, `lock_0111`, `center_lock_0001`, `center_lock_0011`, `center_lock_0111`,
`center_not_0001_of_word`, `center_not_0011_of_word` and `center_not_0111_of_word`.
