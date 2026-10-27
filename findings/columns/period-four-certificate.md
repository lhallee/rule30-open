---
title: A width-16 window certifies the period-four lock from most starts
category: columns
problems: [1]
status: computed
formalization: wanted
evidence: [computations/lock_certificate.py]
---

# A width-16 window certifies the period-four lock from most starts

For each of the three primitive words of period 4, there is a finite, nonempty set of windows of the right half (the
states of columns 1 to $W$, one set per phase) that the driven rule never leaves, whatever the cell beyond column $W$
does, and on which column 1 at the white times is fixed. A right half whose window ever enters the set locks for good,
as [the locking conjecture](period-four-locking.md) needs. The set exists from $W = 16$ for $0001$ and from $W = 14$ for
$0011$ and $0111$, and 29 or 30 of 31 sample starts enter it at $W = 16$. That every finite right half enters it
(attraction) is not proved, and with a free beyond cell the window alone does not force entry at any width tried.

## Setting

Drive a finite right half with the center repeating $w$. Bit $j$ of a window is column $j + 1$; the phase of time $t$ is
$t \bmod 4$, and the center applied from $t$ to $t + 1$ is $w[t \bmod 4]$. The starts are those of
[the locking finding](period-four-locking.md): the empty half and 30 random halves of 64 cells from
`numpy.random.default_rng(30)`.

Given a seed condition on the window at each phase, the certificate is the greatest family $(S_0, S_1, S_2, S_3)$ of sets
of windows inside the seed with $\mathrm{step}_{w[\varphi]}(s, b) \in S_{\varphi + 1}$ for every $s \in S_\varphi$ and
both values $b$ of column $W + 1$. It is computed by removing windows that can leave until nothing changes, and its
invariance is then checked again by enumeration: $2^W$ windows, 4 phases, 2 beyond values. Two seeds:

- **Core** (for $0001$): columns 1 to 3 read $001$, $011$, $110$, $101$ at phases 0 to 3 (column 1 first), the values the
  empty start settles into.
- **Jen**: column 1 takes a fixed value at each white phase (where $w$ reads 0), nothing else. The certificate is the
  union over all such assignments; a union of invariant families is invariant, and a run that enters one assignment's
  family stays in it. This is exactly what masked Jen
  ([`Rule30MaskedJen.masked_jen`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/7d665044b904117af9e82328aeb90a30692b2b85/lean/Ruliology/CellularAutomata/Rule30MaskedJen.lean))
  needs: `cell (t + P) 1 = cell t 1` at every white time $t \ge T$, whatever the values.

## The certificates

| word | seed | $W$ | sizes at phases 0 to 3 | entered by (of 31 starts) |
|---|---|---|---|---|
| $0001$ | core | 8 to 14 | empty | |
| $0001$ | core | 16 | 433, 533, 344, 605 | 30, by step 207 |
| $0001$ | core | 18 | 2,584, 3,155, 2,044, 3,550 | 30, by step 207 |
| $0001$ | core | 20 | 12,562, 15,274, 9,789, 17,249 | 30, by step 207 |
| $0001$ | Jen | 12, 14 | empty | |
| $0001$ | Jen | 16 | 433, 533, 944, 701 | 30, by step 206 |
| $0001$ | Jen | 20 | 18,278, 22,302, 41,792, 30,579 | 30, by step 206 |
| $0011$ | Jen | 12 | empty | |
| $0011$ | Jen | 14 | 605, 433, 533, 344 | 17, by step 629 |
| $0011$ | Jen | 16 | 4,660, 3,950, 5,583, 3,873 | 30, by step 629 |
| $0011$ | Jen | 20 | 108,121, 92,943, 136,058, 93,424 | 30, by step 629 |
| $0111$ | Jen | 12 | empty | |
| $0111$ | Jen | 14 | 878, 1,544, 1,110, 1,366 | 29, by step 172 |
| $0111$ | Jen | 16 | 4,499, 7,917, 5,716, 7,028 | 29, by step 170 |
| $0111$ | Jen | 20 | 91,594, 165,476, 120,678, 144,192 | 31, by step 164 |

The core certificate for $0001$ took 21 to 45 removal passes to empty at $W = 8$ to 14, and 51, 66 and 78 passes at
$W = 16$, 18 and 20. Every set passed the enumeration check. Entry was searched for 12,000 steps (6,000 for the core
rows). Under $0011$ the starts lock column 1 to one of two patterns, $0110$ (14 starts) or $1110$ (17 starts); the Jen
seed covers both, with nonempty families for the white-phase values $(0, 1)$ and $(1, 1)$ at $W = 16$. At $W = 14$ only
the family for $(1, 1)$ is nonempty.

So from any right half whose window lies in one of these sets, column 1 at the white times is periodic with period 4
forever. That is a finite certificate for the lock from those halves, decidable by a check over $2^{16} \cdot 4 \cdot 2$
cases.

## The starts that do not enter

Each start that misses the set at some width tried has a periodic plug next to the center: a block of columns that are
periodic with period 4, ending in a column that repeats the drive word in phase, followed by columns that agree with
the start of the word's phase table.

- $0001$, start 4 (bits for columns 1 to 64:
  `1100111001010101110100110101010000001100000011101110000010000110`): columns 1 to 10 read $0011$, $0110$, $1101$,
  $0101$, $0011$, $0001$, $0001$, $0011$, $0110$, $1101$. Column 7 repeats the drive word and columns 8 to 10 repeat the
  core. Columns 11 to 16 have period 8, not 4 (column 11 reads $00010100$, column 12 $11110001$, column 15 the word
  $00000001$). It locks with period 4 but enters no set up to $W = 20$ in 12,000 steps.
- $0011$, start 24: columns 1 to 9 are those of the $0001$ outlier from column 2 on; column 7 reads $0011$. It enters no
  set up to $W = 20$.
- $0111$, starts 8 and 18: column 7 reads $0111$. They enter at $W = 20$ but not at $W \le 18$.

The certificate is seeded at column 1 and tested with an adversarial beyond cell, so a half whose structure beyond the
plug is itself a shifted driven half is covered only when the window holds the plug and enough of the copy. Heuristic:
this suggests an induction on the plug, since the half beyond a column that repeats the drive word is the same problem
shifted.

## Structure behind the certificate

These are the observations that located it, from the core run of $0001$ (times 1,000 to 19,999).

- **Phase tables.** From the empty start, column $j$ at each phase is constant (`*` where it varies): columns 1 to 11
  read $0011$, $0110$, $1101$, $0{*}0{*}$, ${*}{*}{*}1$, $01{*}{*}$, ${*}{*}{*}1$, $000{*}$, ${*}{*}11$, $0{*}{*}0$,
  $11{*}1$. The forced cells are the same for the empty start and the first two random starts: 4, 4, 4, 2, 1, 2, 1, 3,
  2, 2 and 3 per period in columns 1 to 11, 28 in all, and none in columns 12 to 120.
- **One lattice for three words.** From the empty start, the phase table of $0011$ is the $0001$ table from column 2 on,
  and the table of $0111$ is the $0001$ table from column 4 on with the phases rotated by two, through column 40 of the
  $0001$ table. Column 1 under $0001$ reads $0011$, and column 3 reads $1101$, a rotation of $0111$. The spacetime diagrams
  themselves differ; the tables agree.
- **The forced cells are not self-sustaining.** Read the 28 forced cells as a three-valued pattern (0, 1, unknown) and
  apply the rule with $\mathrm{OR}(1, \text{unknown}) = 1$ and $\mathrm{XOR}(\text{unknown}, x) = \text{unknown}$.
  Columns 1 to 3 are reproduced at every phase. Outer forced cells are not: from phase 0 to 1 at columns 6 and 8, from 1
  to 2 at 4, 8 and 9, from 2 to 3 at 5, 7, 10 and 11, and from 3 to 0 at none. For example column 6 at phase 1 is always
  1, but its inputs at phase 0 are (unknown, 0, unknown), so $c_5 \oplus c_7 = 1$ holds at phase 0 without either cell
  being forced. The chain of OR updates that [the locking finding](period-four-locking.md) describes consists of
  relations among free cells, not of forced values.
- **No affine invariant.** The GF(2) affine hull of the windows seen at each phase, over the empty half and six random
  halves, has dimension $W - 9$, $W - 8$, $W - 9$, $W - 8$ at phases 0 to 3 for $W = 12$, 14, 16 and 18: 9, 8, 9 and 8
  affine constraints, all in columns 1 to 11, the same for every $W$. The hull is not forward invariant: over all hull
  points and both beyond values, the fraction of successors outside the next hull is 0.25, 0.5, 0.25 and 0.56 at phases 0
  to 3, at every $W$. The invariant set is nonlinear, as the OR in the rule suggests. Three-valued propagation from an
  all-unknown window learns nothing, since the OR of two unknowns is unknown.

## Attraction is open

The lock for every finite right half needs every such half to enter a certificate set. With the beyond cell free, the
windows from which entry is forced (the least family containing the set that holds every window whose successors for
both beyond values lie in it) are a minority:

| word | $W = 14$ | $W = 16$ | $W = 18$ | $W = 20$ |
|---|---|---|---|---|
| $0001$ | | 2.5% to 3.4% | 7.0% to 8.2% | 11.8% to 13.1% |
| $0011$ | 4.1% to 5.4% | 13.9% to 15.2% | 21.3% to 22.9% | 27.8% to 29.6% |
| $0111$ | 13.0% to 14.5% | 22.1% to 23.5% | 32.2% to 33.6% | 41.2% to 42.5% |

(range over the four phases, of $2^W$ windows each, Jen seed). The fraction grows with $W$, but at these widths the
window with a free beyond cell does not force entry, so attraction needs information about the cells beyond the window.

## What the kit has

The kit's bitmask strip certificates
([`Rule30StripCertificates`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/7d665044b904117af9e82328aeb90a30692b2b85/lean/Ruliology/CellularAutomata/Rule30StripCertificates.lean))
run the strip forward from all states with a free beyond cell and ask column 1 to be constant at the white phases on
the closure, which is entry and invariance together. For the period-four words,
[`Rule30PeriodFourSkeleton`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/7d665044b904117af9e82328aeb90a30692b2b85/lean/Ruliology/CellularAutomata/Rule30PeriodFourSkeleton.lean)
proves, if the center is eventually $w^\infty$, that the strip eventually stays in an exempt class where column 1 at
the white times is not periodic, and reduces least period 4 to open statements `C3 w` about the left half. The sets
here are the complementary object: windows from which the lock is certain. If every finite right half entered one, the
true history could not stay in the exempt class, and masked Jen would exclude $w$. The kit's module docstrings describe
no certificate of this kind for the period-four words.

## Reproduce

```bash
python -m computations.lock_certificate 0001 --widths 14 16 --steps 20000
python -m computations.lock_certificate 0001 --seed jen --widths 12 14 16 18 20 --hull-widths --entry-steps 12000
python -m computations.lock_certificate 0011 --seed jen --widths 12 14 16 18 20 --hull-widths --entry-steps 12000
python -m computations.lock_certificate 0111 --seed jen --widths 12 14 16 18 20 --hull-widths --entry-steps 12000
```

[computations/lock_certificate.py](../../computations/lock_certificate.py) runs each in under a minute. The core rows
at $W = 8$ to 20 use `--widths 8 10 12 14 16 18 20`.
