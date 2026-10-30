---
title: Right halves driven by blocks of period 5, 6 and 7 almost never enter a trap
category: columns
problems: [1]
status: negative
kind: no-signal
evidence: [computations/lock_chain.py, computations/right_half.py]
---

# Right halves driven by blocks of period 5, 6 and 7 almost never enter a trap

**Question.** [WordTraps](../../Rule30Open/Columns/WordTraps.md) proves traps in Lean for $01111$, $001011$ and
$0011101$, the first for blocks of period 5, 6 and 7, and one for $001011101$ of period 9 with the phase counted modulo
18: once a column repeating the block has one of the trap's windows beside it, Jen's theorem on adjacent columns is
contradicted. Each reduces its block to entry, the statement that every finitely supported right half driven by the
block enters the trap, as the kit reduces $001$ to entry into `t001` and the words of period four to entry into its
ether-and-wall family. For those, computation supports entry: every right half of up to 20 cells enters the
period-four family within 1,959 steps ([the absorption census](../../findings/columns/absorption-census.md)), and every
half of up to ten cells enters `t001`, a median of about 16,000 steps in ([the census for
001](../../findings/columns/t001-census.md)). So does the wall of period 9 of
[NineTraps](../../Rule30Open/Columns/NineTraps.md). Do right halves driven by the new blocks enter their traps, or any
trap?

**What was done.** Two tests, both in [computations/lock_chain.py](../../computations/lock_chain.py).

- *Entry into the Lean traps* (`entry_steps`). Every right half with support in cells 1 to 8, driven by the block from
  each of its phases, is stepped for 50,000 steps, and the first step at which its first cells are a state of the trap
  at the block's phase is recorded. The trap is closed, so a half that enters stays.
- *Any trap* (`natural_scan`). The empty right half and 30 random halves of 64 cells (`right_half.random_starts`) are
  driven by every primitive word of period 2, 3, 5, 6, 7 and 9 for 20,000 steps. A half inside any trap has column 1
  periodic at the word's white times, so the scan first asks whether it is, over the second half of the run
  (`right_half.locked_period`). For each half that passes, it closes the true window at steps 12,000, 16,000 and
  19,999 under both values of the cell beyond (`closure`), at widths 16 to 64 and with the phase counted modulo the
  lock's period or twice it, and asks whether the closure fixes column 1 at the white phases (`natural_trap`). This is
  how the kit built `t001`, and the scan rebuilds it: for $001$, six of the 31 halves lock and each is inside a trap of
  1,363 states of 48 cells modulo 21 at step 12,000 (`test_natural_trap` checks that the closure at 47 cells is
  `t001`).

**Outcome.**

*Entry into the Lean traps*, over the right halves with support in cells 1 to 8, from every phase:

| trap | block | period, phase modulo | halves and phases | entered by step 50,000 | when |
|---|---|---|---|---|---|
| `trap01` | $01$ | 2, 8 | 512 | 15 | all by step 10 |
| `trap001fifteen` | $001$ | 3, 15 | 768 | 0 | |
| `trap01111` | $01111$ | 5, 20 | 1,280 | 0 | |
| `trap001011` | $001011$ | 6, 12 | 1,536 | 10 | all by step 20 |
| `trap0011101` | $0011101$ | 7, 14 | 1,792 | 10 | steps 8,856 to 8,859 |
| `trap001011101` | $001011101$ | 9, 18 | 2,304 | 16 | steps 42,751 to 46,470 |
| `trap001011111` | $001011111$ | 9, 9 | 2,304 | 247 | median 17,403, latest 49,425 |

The entries by step 20 are halves that start next to the trap. The ten into the trap of $0011101$ come from four phases
and distinct halves but land within four steps of each other, as one late event would. The white right half, which the
census includes, enters none of these traps; under $001011111$ it enters no trap within 100,000 steps from any phase,
and its column 1 does not repeat over steps 30,000 to 60,000.

*Any trap.* Column 1 locks for none of the 31 halves driven by any word of period 2, 5, 6 or 7, nor by $011$, except
$01111$, for 2 halves, whose windows close into no trap. For $001$ it locks for 6, all inside the kit's family of
`t001`. At period 9 six words lock for one half each, and five of them are then inside the traps of the wall of
[NineTraps](../../Rule30Open/Columns/NineTraps.md); the sixth, $001010011$, locks with period 27 but its window closes
into no trap up to 160 cells.

**What it means.** The traps of [lock chains](../../findings/columns/lock-chains.md) show that what keeps windows of up
to 18 cells from locking at periods 5, 6 and 7 is not the absence of a trap: wider ones exist for a block of each
period. The obstruction is dynamical. Driven by these blocks, the right half next to the center almost never settles:
column 1 does not repeat at the white times for any random half, and the small halves enter the Lean traps only from
next to them or in one late event, so for these blocks the reduction to entry has almost no computational support; its
hypothesis may well be false. Period 9 shows that this is not a matter of the period alone: there a wall exists that
about one small half in nine enters within 50,000 steps, with entries still coming at the end, as under $001$. The runs
cover only small halves and 50,000 steps: entry later, or by larger halves, is not excluded, and `t001` shows that entry
can take $10^5$ steps.

**Reproduce.**

```bash
python -m computations.lock_chain --entry trap01,trap001fifteen,trap01111,trap001011,trap0011101,trap001011101 --cells 8 --steps 50000
python -m computations.lock_chain --entry trap001011111 --cells 8 --steps 50000
python -m computations.lock_chain --natural 2,3,5,6,7,9 --steps 20000
```

The first takes about 40 minutes with one process per trap, the second about 15 and the third about 5.
