---
title: One sequence in one column forces a lock of the finite game, for a block of any period
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.LockBlocks
headline: [lockBlock_column, center_lockBlock, center_lock_steered, not_eventually_steered]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable, Rule30ZeroBoundaryLanes]
evidence: [computations/locks.py]
---

# One sequence in one column forces a lock of the finite game, for a block of any period

Suppose column $k$ of a row with a leftmost 1 repeats a block $b$ of period $P$ from time $T$. Call a window of the
$K$ cells right of column $k$ locked when, whatever column $k + K + 1$ does from then on, column $k - 1$ reads one value
at each phase of $b$. A locked window makes column $k - 1$ repeat with period $P$ beside column $k$, which Jen's theorem
on adjacent columns forbids. This module proves that a check the kernel evaluates turns one fixed sequence of values
into a contradiction: if every window, started at any phase, ends locked after column $k + K + 1$ reads the sequence,
then once column $k$ repeats $b$, column $k + K + 1$ never reads the sequence again.
[LockWord](LockWord.md) proves this for the three words of period four with the kit's ether-and-wall family as the
lock; here the lock is computed for the block, so any block whose finite game has such a sequence qualifies.
[LockBlocks11](LockBlocks11.md) and [LockBlocks12](LockBlocks12.md) check the sequences of 50 blocks of period 4 to 12.

## Statement

Let `lockCheckB b K us groups fuel` hold, where $u_0, \dots, u_{L-1}$ is the sequence `us` and `groups` lists, for each
final phase, the windows where the sequence leaves the starts.

1. `lockBlock_column`: in the orbit of a row with a leftmost 1, if column $k$ reads $b[(t + s) \bmod P]$ at every time
   $t \ge T$, there is no $t_0 \ge T$ with column $k + K + 1$ reading $u_i$ at time $t_0 + i$ for every $i < L$.
2. `center_lockBlock`: the same for the center column of the single cell ($k = 0$), with the sequence given as the bits
   of a number: column $K + 1$ differs from the sequence at one of the times $t_0, \dots, t_0 + L - 1$.
3. `center_lock_steered`, `not_eventually_steered`: for an entry `Steered` (a block `wordOf P bits`, a sequence, its
   length and the final windows) whose check at width 13 passes, column 14 never reads the sequence once the center
   repeats the block; so if column 14 reads the sequence at arbitrarily late times, the center column does not
   eventually repeat the block, in the kit's form `EventuallyWord`.

## Argument

1. **The window.** Columns $k + 1, \dots, k + K$ at time $t + 1$ follow from the same columns at time $t$, column $k$,
   and column $k + K + 1$. From $t_0 \ge T$ column $k$ is known, so if column $k + K + 1$ reads the sequence, the window
   at time $t_0 + L$ is a known function of the window at $t_0$ and of the phase $(t_0 + s) \bmod P$ (`codeFrom_wrunB`,
   `wrunB`).
2. **All windows at once** (`sinitP`, `goStep`, `strict`, `srunB`, `srunB_spec`). Slice $j$ is one number whose bit
   $p \cdot 2^K + r$ is cell $k + j + 1$ of the window that started as $r$ at phase $p$, for all $P \cdot 2^K$ starts.
   One step of every window is Rule 30 on the $K$ slices, taken in one pass along them, with column $k$ at each start's
   phase and the sequence's value as masks. `strict` makes the kernel evaluate each step before the next, so a sequence
   of 1,749 steps does not build a chain of unevaluated steps that overflows its recursion.
3. **Where the windows end** (`hitsB`, `hitsB_spec`). Each listed window is matched against the slices by $K$ masked
   comparisons, restricted to the starts whose final phase is the window's. The kernel checks that every bit is
   matched, so the true window at $t_0 + L$ is one of the listed windows of its phase.
4. **The lock** (`seedAll`, `closeAll`, `phaseDet`). [BitGame](BitGame.md)'s search `fwdClose` collects, from the
   listed windows of each phase, every node reachable under both values of column $k + K + 1$; `fwdOk` checks that the
   union holds the listed windows and is closed, so the true play stays in it from $t_0 + L$ on (`play_fwd`), and
   `phaseDet` checks that column $k - 1$, a function of the node, takes one value at each phase on it
   (`phaseDet_spec`).
5. **The contradiction.** So column $k - 1$ repeats with period $P$ from $t_0 + L + 1$ on, beside column $k$, which
   repeats with period $P$: Jen's theorem on adjacent columns ([AdjacentColumns](AdjacentColumns.md)) rules this
   out.

The module itself is quick to check; the instances in [LockBlocks11](LockBlocks11.md) and
[LockBlocks12](LockBlocks12.md) take about three and a half minutes each.

## Relation to the kit

The kit's bitmask strip certificates (`Rule30StripCertificates.stripCert`) are locks that every play enters: from all
strips, a few periods with both values of the unknown cell lead into a closed set on which column 1 is constant at the
white phases. A block that has such a certificate is excluded outright. The locks here are entered only along one
sequence of the unknown column, so they give a constraint on that column rather than an exclusion. The kit has no
result of this conditional form; [LockWord](LockWord.md) gives it with the kit's period-four family as the lock. The
contradiction uses [AdjacentColumns](AdjacentColumns.md), this repository's form of Jen's theorem for any row with a
leftmost 1, which the kit proves for the single cell in `Rule30Jen`.
