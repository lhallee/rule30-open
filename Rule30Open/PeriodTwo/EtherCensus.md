---
title: Every head of up to 12 cells on the ether settles, so (R) holds for every 2-adic rational whose tail from cell 12 on is the ether
category: period-two
problems: [1]
status: proved
lean: Rule30Open.PeriodTwo.EtherCensus
headline: [ether_tail_clear, ether_tail_eventually_periodic, ether_tail_itinerary, closedOK_true, closed_count, stripInv_forever, runHead_sound, census, eventually_periodic_of_clear, eth_eq_kit_ether]
kit: new
kit_modules: [Rule30Ether, Rule30ZeroBoundary, Rule30ZeroBoundaryBarriers, Rule30ZeroBoundaryLanes, Rule30PeriodTwoCoupled]
evidence: [computations/ether_certificate.py, computations/defect_potential.py]
---

# Every head of up to 12 cells on the ether settles, so (R) holds for every 2-adic rational whose tail from cell 12 on is the ether

Let $H(U) = (U \gg 1) \oplus (U \lor (U \ll 1))$ be the held map (`held`, `heldOrbit` of
[HeldColumn](HeldColumn.md)) and $K$ the set of 2-adic $U$ with $H^t(U)$ odd at every odd $t$ (`InK` of
[ShiftModel](ShiftModel.md)). Conjecture (R) of [the shift model](../../findings/period-two/shift-model.md) says that every
rational point of $K$ has an eventually periodic itinerary. This module proves it, with no use of $K$, for every
2-adic integer whose bits from cell 12 on are the ether at one of its 28 alignments: the kernel runs the
[ether defect census](../../findings/period-two/ether-defect-census.md) over the heads of 12 cells, 114,688 of them, and
checks the closed strips of 13 cells that settle most of them.

## Statement

Write $e_a(j)$ for cell $j \bmod 7$ of ether state $a \bmod 4$ (`eth`; the states are 64, 97, 19 and 126 as 7-bit
words), and say that $u$ has an ether tail from cell $p$ at the alignment $(a, o)$ when $u_j = e_a(j + o)$ for every
$j \ge p$.

- `ether_tail_clear`: if $u$ has an ether tail from cell $p \le 12$ at $(a, o)$, then for every $t$ and every
  $j \ge 61$, cell $j$ of $H^t(u)$ is $e_{a+t}(j + o)$. The defect never reaches cell 61.
- `ether_tail_eventually_periodic`: then $H^{t+P}(u) = H^t(u)$ for some $P > 0$ and every $t \ge T$.
- `ether_tail_itinerary`: then the itinerary $\beta_s = $ bit 0 of $H^{2s}(u)$ is eventually periodic. This is (R)
  for every point of $K$ with such a tail, and the same holds for every $u$ outside $K$.
- `closedOK_true`, `closed_count`: the 1,915 closed strips, 433, 533, 344 and 605 at the four phases, each closed
  under one step for both values of the cell below it.
- `stripInv_forever`: a defect clear above a cell $c \ge 12$, with its strip at $c$ closed, stays so forever.
- `runHead_sound`, `census`: the checker of one head, and its run over every head of 12 cells at the 28 alignments.
- `eventually_periodic_of_clear`: a defect clear from a fixed cell on at every step gives an eventually periodic orbit.
- `eth_eq_kit_ether`: $e_a(j)$ is the kit's `Rule30Ether.ether` at column $1 - j$ modulo 7 and phase $a$.

## Argument

**The ether and the defect.** The four states of `eth` form a cycle of the held rule on the whole line:
$e_{a+1}(j) = e_a(j + 1) \oplus (e_a(j) \lor e_a(j - 1))$, with $j - 1$ read modulo 7 (`eth_step`, checked on the 28
cells of the cycle). The defect $D_t(j) = H^t(u)_j \oplus e_{a+t}(j + o)$ (`defect`) then follows

$$D_{t+1}(j) = D_t(j+1) \oplus \big((x_t(j) \lor x_t(j-1)) \oplus (B_t(j) \lor B_t(j-1))\big),
\qquad x_t = D_t \oplus B_t,\ B_t(j) = e_{a+t}(j + o),$$

with the held 0 at cell $-1$ entering as $D_t(-1) = B_t(-1)$ (`defect_succ`, `defect_succ_zero`). A defect clear from
cell $W$ on is clear from $W + 1$ on one step later (`defect_clear_succ`), and $D_0$ is clear from cell $p$ on for a
tail from $p$.

**The defect as a number.** `Enc u a o t n` says that bit $j$ of $n$ is $D_t(j)$. With the ether cells 0 to 127 of
each alignment in `bgTab` (checked bit by bit against `eth`, `bgCheck_true`), one step is
$n \mapsto \big(H(n \oplus B_t) \oplus B_{t+1}\big) \bmod 2^{127}$ (`dstep`), exact while $n < 2^{126}$, because cell
$j \le 126$ of $H(x)$ reads only the cells $j - 1$, $j$ and $j + 1 \le 127$ (`enc_step`).

**Closed strips.** A strip is the 13 cells $c - 12, \dots, c$ of the defect, coded as a number below $2^{13}$
(`stripOf`). Its cells one step later, and the cell $c + 1$ above it, depend only on the strip, the cell $c - 13$
below it and the background, which is fixed by the phase and by $(c + o) \bmod 7$ (`newCell`, `strip_cell`); one
bit-parallel formula gives all 14 (`stripRaw`, `stripStep`, `stripRise`, matched cell by cell in
`stripRaw_testBit`). `closedTab` holds, for each phase, the strips at the cells with $(c + o) \bmod 7 = 5$ of the
greatest closed set that `defect_potential.closed_strips(13)` computes. The kernel checks that every one of them, with
either value of the cell below, steps to a strip of the set at the next phase and leaves cell $c + 1$ clear
(`closedOK_true`). So the property "clear above $c$, strip at $c$ closed" holds at step $t + 1$ when it holds at step
$t$ (`stripInv_step`), and by induction at every later step, whatever the cells below $c - 12$ hold
(`stripInv_forever`). The set plays the part, for the zero-boundary left half, that the kit's 109 wall states beside
the ether play for the right half (`Rule30Ether.wallOK_true`).

**The checker.** `runHead` follows one head from step 0 in rounds of four steps, so every check falls at a step
$t \equiv 0 \pmod 4$, where the phase is $a$ again. A round settles the head if the defect lies in a closed strip at
one of the three least cells $c \ge \max(\text{top}, 12)$ with $(c + o) \bmod 7 = 5$ and $c < 61$ (`closedAt`), or if
it equals the snapshot taken at the last of the steps $4, 8, 16, 32, \dots$; otherwise it takes four steps with
`dstep`, each of which must leave the defect below cell 61. Soundness (`runHead_sound`) is an induction on the
rounds that carries `Enc` at the current step and at the snapshot, and the bound up to the current step:

- a closed strip at $c < 61$ keeps the defect below $c$ from then on (`stripInv_of_cand`, `stripInv_forever`);
- a repeat at steps $t' < t$, both multiples of 4, means $H^{t}(u) = H^{t'}(u)$, since the defects and the
  backgrounds agree (`heldOrbit_eq_of_enc`), so every later step repeats one of the steps $t', \dots, t$, at the same
  phase, and the bound holds at all of them (`heldOrbit_repeat`, `clear_of_repeat`);
- otherwise the four steps are exact by `enc_step` and the induction goes on.

Written with the kernel's own operations on numbers, with each computed defect evaluated once (`letN`), the checker
runs in the kernel: `chunkOK` runs 1,024 heads, and `census` joins the 112 chunks, four for each of the 28
alignments, with `headsOK_append`. A head $u$ with an ether tail from cell $p \le 12$ has $D_0 < 2^{12}$, so it is one
of them (`clear_of_census`), and `ether_tail_clear` reads off the bound for $u$ itself after reducing the phase modulo
4 and the offset modulo 7.

**Bounded gives periodic.** If $D_t$ is clear from cell $L$ on at every step, the pairs $(D_t, t \bmod 4)$ take at
most $4 \cdot 2^L$ values, so two steps $m < n$ share one (`pigeonhole_gen` of the kit's
`Rule30ZeroBoundaryBarriers`). Then $H^m(u) = H^n(u)$, and the orbit is periodic from $m$ with period $n - m$
(`eventually_periodic_of_clear`); the itinerary, which reads bit 0 at the even steps, is periodic from $m$ with the
same period (`itinerary_of_eventually_periodic`). This is the direction "bounded top implies eventually periodic" of
item 5 of the shift model.

## The census

`python -m computations.ether_certificate` runs the same checker, step for step, on every head of 12 cells:

| heads | settled by a closed strip | settled by a repeat (top at most) | highest top | highest strip cell | last settling step |
|---|---|---|---|---|---|
| 114,688 | 106,289 | 8,399 (17) | 60 | 60 | 300 |

The counts by way of settling are those of the census entry, whose checker tests the strips at every step rather than
at every fourth; the last settling step is 300 here against 298 there for that reason. The kernel check of the 112
chunks takes about two and a half minutes of one core and under 2 GB of memory. The census to
heads of 20 cells in the census entry is a computation, not a proof. The rounds the checker runs grow by a factor of
about 4.2 from heads of 10 cells (442,640 rounds, `--bits 10`) to heads of 12 (1,841,076), so heads of 14 cells would
cost roughly ten minutes of kernel time; that is an estimate, not a run.

```bash
python -m computations.ether_certificate          # the census above
python -m computations.ether_certificate --lean   # bgTab, closedTab and the census section of the module
lake build Rule30Open.PeriodTwo.EtherCensus
```

`tests/test_ether_certificate.py` checks the defect step against the held map on whole integers, the closed strips
against `defect_potential.closed_strips` and against direct runs with random cells below, the checker against direct
runs, and the tables against the module.

## What it means

(R) holds for every 2-adic integer whose tail from cell 12 on is the ether, at any phase and offset, in $K$ or
not: its orbit under $H$ is eventually periodic, and its defect never reaches cell 61. Since the orbit of $u$ from step
$\tau$ on is the orbit of $H^\tau(u)$, the same holds for every $u$ with some $H^\tau(u)$ of that kind (a remark, not a
separate Lean statement). Like the census, it is a statement about finitely many heads; it says nothing about longer heads,
and the [census entry](../../findings/period-two/ether-defect-census.md) records why the two local routes to all
heads, a potential on the top window and a finite set of top words, fail. Nothing here uses $K$.

## The kit

The kit's `Rule30ZeroBoundary` works with the zero-boundary left half in its own encoding and proves (R)'s analogue
for stripe tails (`Rule30ZeroBoundaryStripe`); its `Rule30PeriodTwoCoupled.etherLeft_zbl` is the case of no head (the ether's left half is an orbit of the
zero-boundary left half), and it has no statement about a left half with an ether tail below a head. Its
`Rule30Ether` certifies the wall traps of the ether in the right half with a kernel closure check (`wallOK_true`), and
its `Rule30ZeroBoundaryLanes` runs a chunked census in the kernel (`check`, `q01_of_chunks`); this module does both for
the left half beside the ether. `eth_eq_kit_ether` identifies the ether here with the kit's.
