---
title: Every head of up to 16 cells on the ether settles, so (R) holds for every 2-adic rational whose tail from cell 16 on is the ether
category: period-two
problems: [1]
status: proved
lean: Rule30Open.PeriodTwo.EtherCensus16
headline: [ether_tail_clear_16, ether_tail_eventually_periodic_16, ether_tail_itinerary_16, descCensus, runDesc_sound, descend, headsBelow_block, headsBelow_chunk, headsBelow_12, defect_shift]
kit: new
kit_modules: [Rule30Ether, Rule30ZeroBoundary, Rule30ZeroBoundaryLanes, Rule30PeriodTwoCoupled]
evidence: [computations/ether_descent.py, computations/ether_certificate.py]
---

# Every head of up to 16 cells on the ether settles, so (R) holds for every 2-adic rational whose tail from cell 16 on is the ether

[EtherCensus](EtherCensus.md) proves conjecture (R) of [the shift model](../../findings/period-two/shift-model.md) for
every 2-adic integer whose bits from cell 12 on are the ether at one of its 28 alignments, with a census of the heads of
12 cells that the kernel runs. This module extends it to the heads of 16 cells, 1,835,008 of them over the 28
alignments. It reuses the checker of `EtherCensus` and its soundness, and adds one more way for a head to settle,
descent to a smaller head, which cuts the rounds the kernel runs by a factor of about 2.6.

## Statement

With $e_a(j)$, the defect $D_t$ and "an ether tail from cell $p$ at the alignment $(a, o)$" as in
[EtherCensus](EtherCensus.md):

- `ether_tail_clear_16`: if $u$ has an ether tail from cell $p \le 16$ at $(a, o)$, then for every $t$ and every
  $j \ge 79$, cell $j$ of $H^t(u)$ is $e_{a+t}(j + o)$. The defect never reaches cell 79.
- `ether_tail_eventually_periodic_16`: then $H^{t+P}(u) = H^t(u)$ for some $P > 0$ and every $t \ge T$.
- `ether_tail_itinerary_16`: then the itinerary $\beta_s$ = bit 0 of $H^{2s}(u)$ is eventually periodic. This is (R)
  for every point of $K$ with such a tail, and the same holds for every $u$ outside $K$.
- `descCensus`: at each offset $o < 7$ and every phase, every half whose defect at step 0 is a number below $2^{16}$
  has its defect clear from cell 79 on at every step (`HeadsBelow o 79 (2 ^ 16)`).
- `defect_shift`, `descend`: the defect of $H^T(u)$ at the alignment $(a + T, o)$ is the defect of $u$ from step $T$
  on, so a defect that falls below a bound under which every head is bounded stays bounded.
- `runDesc_sound`, `headsBelow_block`, `headsBelow_chunk`, `headsBelow_12`: the checker with descent, its soundness,
  the step from one block of heads to the next, and the start from the census of `EtherCensus`.

## Argument

**Descent.** Write `HeadsBelow o L lo` for: at the offset $o$ and every phase $a$, every half $v$ whose defect at step
0 is a number $m < lo$ has its defect clear from cell $L$ on at every step. The defect of $H^T(u)$ at the alignment
$(a + T, o)$ is, cell by cell and step by step, the defect of $u$ from step $T$ on, since
$H^s(H^T(u)) = H^{T+s}(u)$ and the ether at phase $(a + T) + s$ is the ether at phase $a + (T + s)$
(`defect_shift`). So if the defect of $u$ is a number $n < lo$ at step $T$, then `HeadsBelow o L lo` applied to
$H^T(u)$ at the phase $a + T$ bounds the defect of $u$ at every step after $T$, and the steps up to $T$ are bounded
by what the checker has seen (`descend`). The phase $a + T$ is any phase, which is why `HeadsBelow` speaks of all four
phases at once.

**The checker with descent.** `runDesc` is `runHead` of `EtherCensus` with one more parameter, the bound $lo$, and one
more test after each of the four steps of a round: a defect below $lo$ settles the head. Its soundness
(`runDesc_sound`) is the induction of `runHead_sound` on the rounds, with the closed strips (`stripInv_of_cand`,
`stripInv_forever`) and the repeats (`heldOrbit_eq_of_enc`, `clear_of_repeat`) of `EtherCensus` as they are, and a
fourth case for a descent after the step $t + 1$, $t + 2$, $t + 3$ or $t + 4$, closed by `descend` with the bound up
to that step (`bound_succ`).

**Blocks and chunks.** If `HeadsBelow o L lo` holds and every head $h$ with $lo \le h < lo + B$ passes `runDesc` with
the bound $lo$ at the four phases of $o$, then `HeadsBelow o L (lo + B)` holds (`headsBelow_block`): a head below $lo$
is bounded already, and a head of the block is settled by a closed strip, a repeat or a descent below $lo$. The phase
of the half is reduced modulo 4 (`enc_phase`, `defectClear_phase`) to meet the census, which runs the phases
$0, \dots, 3$. `descChunk` runs 16 blocks of $B = 256$ heads, each with the bound at its own first head, as one kernel
computation, and `headsBelow_chunk` chains its blocks by induction on their number. The chain starts from
`headsBelow_12`: the heads below $2^{12}$ pass `runHead` with the bound 61 (`census` of `EtherCensus`), so
`runHead_sound` bounds them with 61, hence with 79. For each of the 7 offsets the 15 chunks from $2^{12}$ to $2^{16}$,
each checked at the 4 phases, give `HeadsBelow o 79 (2 ^ 16)` (`descUpTo_o_k`, `descCensus`), 420 kernel checks in all.

**The theorems.** A half $u$ with an ether tail from cell $p \le 16$ at $(a, o)$ has its defect at step 0 below
$2^{16}$ at the alignment $(a, o \bmod 7)$, so `descCensus` bounds it, and `ether_tail_clear_16` reads off the cells of
$H^t(u)$. `eventually_periodic_of_clear` and `itinerary_of_eventually_periodic` of `EtherCensus` give the other two.

**Why blocks.** A bound shared by the heads of a block costs few rounds: on the heads from $2^{12}$ to $2^{14}$,
descent below the head itself takes 2,166,087 rounds, and descent below the first head of a block of 64, 256, 1,024 or
4,096 heads takes 2,167,489, 2,173,644, 2,263,946 and 2,765,786. A shared bound is also a little cheaper per round in
the kernel. On the 4,096 heads from $2^{12}$ at the alignment $(0, 0)$, the kernel took 4.6 s for `runHead` (67,976
rounds), 2.4 s for `descChunk` with blocks of 256 (9,932 rounds), 2.1 s with blocks of 16 and 3.2 s with blocks of 1
(9,369 rounds each), as `profiler` reports them. So a round of the checker with descent costs the kernel more than a
round of `runHead`, and on this chunk descent saves a factor of about 2 in kernel time against 6.8 in rounds. The
timings come from one machine with another Lean build running; they are a measurement, not a cost model.

## The census

`python -m computations.ether_descent` runs the same checker, step for step, on every head $h$ with
$2^{12} \le h < 2^{16}$ at the 28 alignments, with the bound 79, 110 rounds and blocks of 256:

| heads | settled by a closed strip | by a repeat | by descent | highest top | last settling step | most rounds of one head | rounds |
|---|---|---|---|---|---|---|---|
| 1,720,320 | 754,621 | 389 | 965,310 | 78 | 432 | 109 | 11,000,618 |

Without descent, the checker `runHead` of `EtherCensus` takes 28,393,972 rounds on the same heads with the same bound
and fuel (5,596,364 against 2,173,644 on the heads below $2^{14}$), so descent cuts the rounds by a factor of about
2.6. The highest top, 78, is the census entry's for heads of 16 cells, and every head settles with the bound 79; the
census to heads of 20 cells in the [census entry](../../findings/period-two/ether-defect-census.md) remains a
computation. `lake build Rule30Open.PeriodTwo.EtherCensus16` took 1,682 s of wall time on 4 cores with another Lean
build running, and its Lean process stayed under 1.1 GB of resident memory (sampled every 5 s), since the module
elaborates its 420 kernel checks one at a time (`Elab.async false`). Heads of 18 cells would cost about four times as
many rounds, since the rounds grow by a factor of about 4 from the heads below $2^{14}$ to those below $2^{16}$ (an
estimate, not a run).

```bash
python -m computations.ether_descent                                  # the census above, about a minute
python -m computations.ether_descent --bits 14 --block 1              # heads below 2^14, descent below the head
python -m computations.ether_descent --lean                           # the census section of the module
lake build Rule30Open.PeriodTwo.EtherCensus16
```

`tests/test_ether_descent.py` checks each way of settling against direct runs with `step` (a descent reaches a head
below the bound at the step it names), the bound against direct runs of 500 steps, the cost of descent against the
checker without it and with blocks, and the census section against the module.

## What it means

(R) holds for every 2-adic integer whose tail from cell 16 on is the ether, at any phase and offset, in $K$ or not:
its orbit under $H$ is eventually periodic, and its defect never reaches cell 79. Like `EtherCensus`, this is a
statement about finitely many heads. Descent turns the census into an induction on the head, which is a step toward a
proof for all heads only if the defect of every head falls below its head or enters a closed strip, and the census
entry's items 3 and 4 say why the local routes to that fail. Nothing here uses $K$.

## The kit

As for [EtherCensus](EtherCensus.md): the kit has no statement about the zero-boundary left half with an ether tail
below a head. Its `Rule30Ether` certifies the wall traps of the ether in the right half with a kernel closure check,
and its `Rule30ZeroBoundaryLanes` runs a chunked census in the kernel; neither settles one head by the bound on
smaller heads.
