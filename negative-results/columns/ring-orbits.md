---
title: Periodic orbits on rings explain the finite game's failure only for the alternating block
category: columns
problems: [1]
status: negative
kind: no-signal
evidence: [computations/ring_orbits.py, computations/game.py]
---

# Periodic orbits on rings explain the finite game's failure only for the alternating block

**Idea.** [The finite game](../../Rule30Open/Columns/FiniteGame.md) fails for most blocks at every width tried, all
blocks with only short runs among them ([the game blocks](../../findings/columns/game-blocks.md)). A proof that it fails
at every width would mark where right-side methods stop. Periodic orbits of Rule 30 on a ring give such proofs. Lift an
orbit on $M$ cells to the line: every column repeats. If column $k$ repeats a block $b$ and column $k - 1$ does not
repeat with the period of $b$, then the cells right of $k$, read at any width $K$, make a closed walk of the game for
$b$ that shows the column left of $k$ taking both values at one phase. A closed walk lies in one strongly connected
component that holds a play, so the game does not exclude $b$ at any width. Jen's theorem, which the game relies on,
does not apply to the lifted row, since it has no leftmost 1. The question is which blocks these witnesses cover.

**Outcome.**

- **Rings have few periodic orbits.** Up to rotation there are 1, 2, 1, 3, 2, 2, 3, 4, 3, 4, 3, 5, 5, 9, 7, 7, 7, 7,
  5, 11, 8, 9, 4, 11 and 8 periodic orbits on rings of 1 to 25 cells, 131 in all, found by iterating the step map past
  every transient.
- **Only the ether witnesses a block.** The only column of period at most 16 whose left neighbor breaks its period is
  the ether's alternating column $B_4 = 0101$, on the ring of 7 cells (the ether of the kit's `Rule30Ether`) and its
  double on 14: its left neighbor $B_3 = 1101$ has period 4. So the game fails at every width for $01$, and for no
  other block of period at most 16 do rings of up to 25 cells show why.

**What it means.** For the other blocks the walks that defeat the game do not come from a ring of at most 25 cells,
and their lengths may grow with $K$. A barrier for the game has to come from right halves that are not spatially
periodic, or from rings larger than those searched, and the ring orbits, being few and long, say almost nothing about
them. For $01$ the
witness is the ether itself, which carries an alternating column (the kit's `aligned_0101_3`).

## Reproduce

```bash
python -m computations.ring_orbits --max-cells 25 --max-block 16
```

[computations/ring_orbits.py](../../computations/ring_orbits.py) takes about 2 minutes to 25 cells and 2 seconds to
20; its test compares the orbit counts with a step-by-step search on small rings.
