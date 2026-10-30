---
title: Once the center repeats one of 23 blocks of period 12, column 14 never reads that block's steering sequence
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.LockBlocks12
headline: [steered12_check, center_lock_steered12, not_eventually_steered12]
kit: new
kit_modules: [Rule30StripCertificates, Rule30StripCertificateTable]
evidence: [computations/locks.py]
---

# Once the center repeats one of 23 blocks of period 12, column 14 never reads that block's steering sequence

For each of 23 blocks $b$ of period 12 there is a sequence of 71 to 1,098 values with this property: once the center
column of the single cell repeats $b$, in any rotation, column 14 never reads the sequence again
(`center_lock_steered12`). So if column 14 reads the sequence at arbitrarily late times, the center column does not
eventually repeat $b$ (`not_eventually_steered12`). Neither the finite game nor the kit excludes any of the 23, and 9
of them have no run of more than four equal values.

## Statement

`steered12` lists the 23 blocks of period 12 that neither the finite game at width 14 nor the kit excludes and whose
game at width 13 has locked windows that every window can be steered into ([steerable
locks](../../findings/columns/steerable-locks.md)). Each entry holds the block as its least rotation, the sequence as
the bits of a number, its length, and the windows where it leaves each start. `steered12_check` says the check of
[LockBlocks](LockBlocks.md) passes for each, and `center_lock_steered12` and `not_eventually_steered12` are that
module's center forms for the entries. With their longest runs and the lengths of their sequences, the blocks are
$000000001011$ (8, 81), $000000010001$ (7, 165), $000000011101$ (7, 179), $000000110011$ (6, 321), $000001001101$
(5, 946), $000001101011$ (5, 197), $000010010001$ (4, 646), $000010101001$ (4, 1,098), $000011011011$ (4, 483),
$000011111111$ (8, 71), $000100111101$ (4, 632), $000101011111$ (5, 621), $000101101011$ (3, 769), $000111001101$
(3, 808), $001001101111$ (4, 281), $001011011111$ (5, 502), $001011111011$ (5, 370), $001100111111$ (6, 569),
$001110111101$ (4, 1,034), $001111111101$ (8, 173), $010101010111$ (3, 523), $010111111011$ (6, 376) and
$011101111111$ (7, 362).

## Argument

The same as [LockBlocks11](LockBlocks11.md#argument): the kernel runs `lockCheckB` on each entry at width 13, and
`center_lock_steered` turns a passing check into the statement; the sequences and windows come from `steering` in
[computations/locks.py](../../computations/locks.py). The module builds in about 215 seconds with a peak near 2.5 GB.

## Relation to the kit

The kit excludes none of the 23 blocks and has no statement that ties a column beyond the center to a repeating center
for them ([LockBlocks](LockBlocks.md#relation-to-the-kit)).
