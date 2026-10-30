---
title: Once the center repeats one of 26 blocks of period 4 to 11, column 14 never reads that block's steering sequence
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.LockBlocks11
headline: [steered11_check, center_lock_steered11, not_eventually_steered11]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/locks.py]
---

# Once the center repeats one of 26 blocks of period 4 to 11, column 14 never reads that block's steering sequence

For each of 26 blocks $b$ of period 4 to 11 there is a sequence of 93 to 1,749 values with this property: once the
center column of the single cell repeats $b$, in any rotation, column 14 never reads the sequence again
(`center_lock_steered11`). So if column 14 reads the sequence at arbitrarily late times, the center column does not
eventually repeat $b$ (`not_eventually_steered11`). Neither the finite game nor the kit excludes any of the 26, and 7
of them have no run of more than four equal values.

## Statement

`steered11` lists the 26 blocks of period at most 11 that neither the finite game at width 14 nor the kit excludes and
whose game at width 13 has locked windows that every window can be steered into ([steerable
locks](../../findings/columns/steerable-locks.md)); the kit excludes a 27th such block, $0^9 1$, as a padded word. Each
entry holds the block as its least rotation, the sequence as the bits of a number, its length, and the windows
where it leaves each start. `steered11_check` says the check of [LockBlocks](LockBlocks.md) passes for each, and
`center_lock_steered11` and `not_eventually_steered11` are that module's center forms for the entries. With their
longest runs and the lengths of their sequences, the blocks are:

- period 4: $0111$ (run 3, 323 values);
- period 8: $00000101$ (5, 398), $00011101$ (3, 903), $00011111$ (5, 280), $00111101$ (4, 332), $00111111$ (6, 93);
- period 10: $0000000101$ (7, 254), $0000011101$ (5, 449), $0001111111$ (7, 275), $0011111101$ (6, 199),
  $0111011111$ (5, 655);
- period 11: $00000000101$ (8, 222), $00000011101$ (6, 141), $00000110001$ (5, 1,409), $00000110011$ (5, 554),
  $00001001101$ (4, 863), $00001101011$ (4, 513), $00001111111$ (7, 289), $00011111111$ (8, 314), $00101101111$
  (4, 1,725), $00110011111$ (5, 620), $00111111101$ (7, 250), $01010101011$ (2, 534), $01011111011$ (5, 711),
  $01110111111$ (6, 466), $01111011111$ (5, 1,749).

For $0111$, [LockWord](LockWord.md) has a sequence of 381 values in the same column with the kit's family as the lock.
The target here, every locked window, contains the family, and the greedy sequence for it has 323 values.

## Argument

The same as [LockBlocks](LockBlocks.md): the kernel runs `lockCheckB` on each entry at width 13 (`Steered.check`), and
`center_lock_steered` turns a passing check into the statement. The sequences and windows come from `steering` in
[computations/locks.py](../../computations/locks.py), which builds each sequence greedily, as
`lock_word.universal_word` does, with the locked windows as the target. They need not be the shortest. The module
builds in about 195 seconds with a peak near 2.6 GB, most of it in the longest sequences on slices of $11 \cdot 2^{13}$
bits; [LockBlocks12](LockBlocks12.md) holds period 12, so the two build side by side.

## Relation to the kit

The kit excludes none of the 26 blocks and has no statement that ties a column beyond the center to a repeating center
for them. Its certificates for blocks are unconditional locks ([LockBlocks](LockBlocks.md#relation-to-the-kit)).
