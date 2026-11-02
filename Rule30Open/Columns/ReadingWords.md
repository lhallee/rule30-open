---
title: Beside a center column repeating one of 15 blocks of period 5 to 7, column 1 at one white step avoids a list of words
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.ReadingWords
headline: [readings_00011, readings_00011_evolve, readings_00101, readings_00101_evolve, readings_00111,
  readings_00111_evolve, readings_01011, readings_01011_evolve, readings_000001, readings_000001_evolve,
  readings_000011, readings_000011_evolve, readings_000111, readings_000111_evolve, readings_001101,
  readings_001101_evolve, readings_010111, readings_010111_evolve, readings_0000001, readings_0000001_evolve,
  readings_0000101, readings_0000101_evolve, readings_0001001, readings_0001001_evolve, readings_0001011,
  readings_0001011_evolve, readings_0011011, readings_0011011_evolve, readings_0110111, readings_0110111_evolve]
kit: new
kit_modules: [Rule30Ether, Rule30EtherThree, Rule30StripCertificates]
evidence: [computations/reading_certificates.py, computations/reading_modules.py, computations/gap_traps.py]
---

# Beside a center column repeating one of 15 blocks of period 5 to 7, column 1 at one white step avoids a list of words

Let the center column repeat one of the 15 blocks of the table and let it drive the right half, from any initial right
half, finite or not. At one white step of each period, read column 1. From the reading of the table on (readings
counted from 0), these readings never contain a word of the block's list. Each list is the forced list of lowest
entropy that `reading_certificates.strongest` finds at a single white phase within 120,000 states; the sequences that
avoid it carry 0.465 to 0.831 bits per reading in place of 1. Each block is a rank certificate on a strip of 2 to 10
columns, checked by the kernel, as in [Runs00001](Runs00001.md): whatever the cells beyond the strip do, the strip
falls within the largest rank of steps into a closed set of states on which no reading completes a word of the list.

## Statement

For a block $b$ of period $P$, the center is $c_{ph}(t) = b_{(t + ph) \bmod P}$ (`ctr ph t` in the namespace
`ReadingWords.B<b>`) and $F = \mathrm{drv}(c_{ph}, R)$ is the kit's driven right half: column 0 is $c_{ph}$, column
$p \ge 1$ starts as $R(p)$ and follows Rule 30. The read phase $q$ is a white phase of $b$ ($b_q = 0$); the read steps
are the $t$ with $(t + ph) \bmod P = q$, the $i$-th of them is $t_i = P i + ((q + P - ph \bmod P) \bmod P)$, and the
$i$-th reading is $F(t_i, 1)$ (`reading R ph i`). `Avoids x i0` says that no word of the list occurs in $x$ at an index
$i \ge i_0$.

| block | read at the white step (phase $q$) | words | from reading | largest rank | width | states | entropy |
|---|---|---|---:|---:|---:|---:|---:|
| $00011$ | first (0) | $00$, $01010$ | 5 | 28 | 7 | 10,240 | 0.651 |
| $00101$ | first (0) | $010$, $101$, $1111$ | 1 | 15 | 6 | 2,560 | 0.582 |
| $00111$ | first (0) | $11$, $1001$ | 4 | 22 | 8 | 10,240 | 0.597 |
| $01011$ | second (2) | $11$ | 0 | 5 | 2 | 40 | 0.694 |
| $000001$ | first (0) | $11$, $101$ | 2 | 14 | 7 | 3,072 | 0.551 |
| $000011$ | first (0) | $010$, $101110$ | 4 | 31 | 7 | 24,576 | 0.784 |
| $000111$ | first (0) | $11$, $101$, $1001$ | 4 | 26 | 8 | 12,288 | 0.465 |
| $001101$ | first (0) | $11$, $101$ | 2 | 18 | 6 | 1,536 | 0.551 |
| $010111$ | first (0) | $111$, $1101$ | 2 | 22 | 6 | 3,072 | 0.811 |
| $0000001$ | third (2) | $00$, $0110$ | 5 | 37 | 10 | 57,344 | 0.597 |
| $0000101$ | fifth (5) | $11$ | 1 | 8 | 6 | 896 | 0.694 |
| $0001001$ | first (0) | $11$ | 4 | 34 | 9 | 7,168 | 0.694 |
| $0001011$ | first (0) | $101$, $1001$, $10001$ | 5 | 45 | 9 | 57,344 | 0.613 |
| $0011011$ | first (0) | $000$, $00111$ | 7 | 59 | 10 | 114,688 | 0.831 |
| $0110111$ | first (0) | $11$, $101$ | 4 | 35 | 10 | 28,672 | 0.551 |

The entropy, in bits per reading, is that of all sequences without the words (`gap_traps.word_entropy`). For each block:

1. `readings_<b>`. For every $R : \mathbb{N} \to \mathrm{Bool}$ and every $ph$, `Avoids (reading R ph) i0` with
   $i_0$ the reading of the table.
2. `readings_<b>_evolve`. For every row `init` and time $T$ with `evolve init t 0 = w<b>.getD ((t - T) % P) false`
   for all $t \ge T$, the readings $j \mapsto$ `evolve init (T + P j + q) 1` (the term $+ q$ is absent for $q = 0$)
   satisfy `Avoids _ i0`.
3. `no_<word>_time_<b>`, one per word. If $(u + ph) \bmod P = q$ and the last reading $u + P(|word| - 1)$ is at the
   largest rank or later, then $F(u, 1) F(u + P, 1) \cdots$ is not the word.
4. `ReadingWords.B<b>.rank_bound`. Along every driven right half, the rank of the state at time $t$ is at most the
   largest rank minus $t$.

At a white step the next center cell is column $-1$ xor column 1, so for a row whose center repeats $b$, column $-1$
at the read steps is the reading, or its complement when $b_{q + 1} = 1$, and carries the same constraint. That
corollary is not stated in Lean here.

## Argument

The argument is that of [Runs00001](Runs00001.md), block by block.

1. **A finite state.** Columns $1, \dots, W$ at time $t + 1$ are a function of columns $1, \dots, W$ at time $t$, the
   center at time $t$ (known from the phase) and column $W + 1$ at time $t$, which is unknown. A state is a phase
   $p < P$, a window $w < 2^W$ (bit $i$ is column $i + 1$) and the last $L - 1$ readings $s < 2^{L - 1}$ (newest in bit
   0), $L$ the longest word. A step goes to phase $p + 1 \bmod P$, to the window `stripStep W (b.getD p false) z w` for
   column $W + 1$ equal to $z$, and at phase $q$ it appends the reading $w \bmod 2$, column 1 before the step, to $s$.
2. **The closed good set and its ranks.** The good states form the greatest set that is closed under both successors
   and on which no step at phase $q$ completes a word. Rank it 0, and give rank $k$ to a state outside the lower ranks
   whose two successors both have rank below $k$. For each block every state gets a rank; the largest is in the table.
3. **The kernel check** (`nodeOK`, `ok_p`, `parts_ok`). For every state: its rank is at most the largest; at rank 0 both
   successors have rank 0 and, at phase $q$, the reading does not complete a word (`badB`); at positive rank both
   successors have smaller rank. The ranks are packed per window into one number per phase and readings, and each
   phase is checked by `decide +kernel`. The check needs neither the construction of step 2 nor its claim of greatest
   set; any table that passes it proves the theorem.
4. **The driven half follows the states** (`win`, `win_enc`, `win_succ`, `suf`). The window of $F$ at time $t$ is the
   kit's `EncF F W t 0`, moved one step by the kit's `encF_step` with column $W + 1$ as the unknown cell; the center at
   time $t$ is letter $(t + ph) \bmod P$ of the block; the readings start as $s = 0$.
5. **Rank falls to 0** (`rank_bound`): a positive rank drops by at least 1 per step and rank 0 stays 0.
6. **No word after the largest rank** (`no_bad`, `suf_period`). From then on the state has rank 0, so a reading at
   phase $q$ completes no word against the stored readings, and $P$ steps after a phase-$q$ step the stored readings
   have shifted by exactly that reading, so they are the true readings (`bad_<word>`).
7. **Indices and rows** (`readings_<b>`, `evolve_eq_drv`, `readings_<b>_evolve`). The reading $i + k$ is at time
   $t_i + P k$, and $t_i \ge P i$; from time $T$ on, the cells $p \ge 1$ of a row whose center repeats $b$ from $T$
   are the right half driven by $c_0$ from the row at time $T$.

## Relation to the kit and to masked Jen

The kit's strip certificates (`Rule30StripCertificates`, `Rule30StripCertificateTable`) force column 1 to be
eventually periodic at the white phases of a block, and masked Jen then excludes the block; neither they nor the kit's
equivalents state a constraint on words of column 1 that leaves it aperiodic, and none of the 15 blocks is in the
kit's strip certificate tables. The theorems here are of the kind of [ThreeRuns](ThreeRuns.md) and
[Runs00001](Runs00001.md): each list read at one phase has positive entropy (at least 0.465 bits per reading), so none
of them makes the readings eventually periodic, and none excludes its block. Masked Jen needs column 1 eventually
periodic at every white phase; a forced list read at all white phases whose sequences have entropy 0 would do that.

[Reading constraints](../../findings/columns/reading-constraints.md) reads all white phases at width 14, which is not
kernel-checked here. For 10 of the blocks entry is forced there into lists of entropy 0.135 to 0.586 bits per reading
(a reading there is one white step of any phase, so the numbers are per reading of a different sequence). For $00111$,
$01011$, $000001$, $010111$ and $0011011$ entry into the learned lists is not forced there, and the forced sublists
have entropy 0.694 to 0.913; the lists here are forced for every right half at one phase.

## Reproduce

```bash
python -m computations.reading_modules ReadingWords --check   # the module is the generator's text, about 1 s
python -m computations.reading_certificates --block 0011011 --phases 0 --width 10 --words 000 00111   # one block
lake build Rule30Open.Columns.ReadingWords
```

The lists come from `reading_certificates.strongest(block, (q,), sample_readings(block, 40, 6000), 120_000)` at every
white phase $q$ of each block, keeping the phase of lowest entropy; `reading_modules.READING_WORDS` holds them.
`tests/test_reading_words.py` checks that the sections of two blocks are the generator's text, the ranks of the two
smallest certificates ($01011$ at width 2, $0000101$ at width 6) against a naive fixed point with a cell-by-cell step,
and direct runs of random halves of every block from every phase against the words from the reading of the table on.
