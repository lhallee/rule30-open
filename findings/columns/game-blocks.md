---
title: The finite game excludes 76 of the 2,538 blocks up to period 14
category: columns
problems: [1]
status: computed
formalization: partial
evidence: [computations/game.py]
---

# The finite game excludes 76 of the 2,538 blocks up to period 14

[The finite game](../../Rule30Open/Columns/FiniteGame.md) was run on every primitive block of period at most 14, at
widths 6, 10 and 14 in turn. It excludes 76 of the 2,538 blocks as the eventual period of any column of any row with a
leftmost 1, the center column of the single cell included. Lean checks the method and two of the certificates; for the
other 74 blocks the computation is the proof.

## Result

The excluded blocks are both constant blocks, 3 of period 8 ($00000001$, $00000011$, $01111111$), 3 of period 10, 7 of
11, 9 of 12, 21 of 13 and 31 of 14. None of period 2 to 7 or 9 is excluded. Every excluded block has a run of at least
six 0s or seven 1s, and the 15 blocks whose runs of 1s all last at least nine steps are among them, as
[the long-runs theorem](../../Rule30Open/Columns/LongRuns.md) requires.

For blocks with only short runs, $01$ among them, the game fails at every width tried: some component of the game that
can hold a play shows the column left of the repeating one taking both values at one phase. A long run synchronizes
the cells beside the column; short runs leave the free cell's influence alive.

## Reproduce

```bash
python -m computations.game --max-period 14 --widths 6,10,14
```

This takes about 2.5 minutes on a laptop and prints the 76 blocks with the first width that excludes each.

`game_certificate` in [computations/game.py](../../computations/game.py) exports a certificate for Lean when the ranks
fit in 8 bits; `lean_certificate` prints it in the form `FiniteGame.lean` uses.

## Open

Exporting the other 74 certificates to Lean, with a more compact encoding where the ranks exceed 8 bits, would make
every one of these exclusions kernel-checked.
