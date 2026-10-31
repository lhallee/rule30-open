---
title: The period-two condition is a full 2-shift whose periodic points are domains, and its rational points are preperiodic as far as tried
category: period-two
problems: [1]
status: computed
formalization: partial
evidence: [computations/held_shift.py, computations/held_shift_search.c]
---

# The period-two condition is a full 2-shift whose periodic points are domains, and its rational points are preperiodic as far as tried

Let $K$ be the set of 2-adic integers $U$ with $H^t(U)$ odd at every odd $t$, for the held map
$H(U) = (U \gg 1) \oplus (U \lor (U \ll 1))$ of [HeldColumn](../../Rule30Open/PeriodTwo/HeldColumn.md). The
[period-two question](../../Rule30Open/PeriodTwo/HeldColumn.md) is whether $K$ contains a positive integer. $K$ is
exactly the one-sided full 2-shift under $H^2$, a positive integer is a point of it with a vacuum tail, and the
points of $K$ that are rational 2-adic numbers, as far as searched, are exactly the preperiodic points of the shift:
domains and the defects that heal into them. A proof covers the rationals whose tail is a stripe. This restates the problem; it does not settle it.

## Result

1. **The conjugacy** (the bijection and the shift are proved in Lean for bit sequences,
   [ShiftModel](../../Rule30Open/PeriodTwo/ShiftModel.md); the kit's `Rule30ZeroBoundary` proves the same in its
   encoding of the zero-boundary left half, with `Theta_unique`, `Theta_inj` and `two_step_shift`, the count of
   residues as `count_constrained`, and continuity in both directions as `Theta_dep` and `Theta_inverse_dep`). Bit 0 of $H^t(U)$ is $u_t \oplus g_t(u_0, \dots, u_{t-1})$. The condition
   at an odd $t$ therefore fixes bit $t$ of $U$, and $K$ is the graph of a map from the free bits $u_0, u_2, u_4,
   \dots$: $2^{\lceil d/2 \rceil}$ residues modulo $2^d$. The itinerary of $U \in K$ is $\beta_s = $ bit 0 of
   $H^{2s}(U)$. It is triangular in the free bits, so $U \mapsto \beta$ is a bijection from $K$ onto $\{0, 1\}^{\mathbb N}$,
   and $H^2$ maps $K$ into $K$ and shifts the itinerary. Each $\beta_s$ depends on $u_0, \dots, u_{2s}$ only and
   each $u_k$ on $\beta_0, \dots, \beta_{\lfloor k/2 \rfloor}$ only, so the bijection is continuous both ways. So
   $(K, H^2)$ is the one-sided full 2-shift, and $H^2$ is exactly 2-to-1 on $K$.
2. **Periodic points are domains** (argument; that the half is eventually periodic in space, and that no periodic point has finite support, are proved in Lean, [ShiftModel](../../Rule30Open/PeriodTwo/ShiftModel.md); the table of spatial periods is computed). A point with itinerary of period $n$ has column 0
   periodic with period $2n$, and the columns left of it follow $Y_{k+1}(t) = Y_k(t + 1) \oplus (Y_k(t) \lor
   Y_{k-1}(t))$ with $Y_{-1} = 0$, on the finite set of cyclic words of length $2n$. So the sequence of columns is
   eventually periodic and $U$ is a 2-adic rational. The $2^n$ points of period dividing $n$ have these spatial
   periods (count in parentheses), computed for $n \le 12$:

   | $n$ | spatial periods |
   |---|---|
   | 1 | 2 (2): the stripes $A = 1010\dots$, $B = 0101\dots$ |
   | 2 | 2 (2), 7 (2): the ether |
   | 3 | 2 (2), 84 (6) |
   | 4 | 2 (2), 7 (14) |
   | 5 | 2 (2), 90 (5), 155 (25) |
   | 6 | 2 (2), 7 (2), 60 (12), 84 (6), 100 (6), 138 (36) |
   | 7 | 2 (2), 644 (14), 728 (84), 1316 (28) |
   | 8 | 2 (2), 7 (14), 325 (208), 2032 (32) |
   | 9 | 2 (2), 84 (6), 342 (18), 477 (9), 1962 (207), 4050 (90), 8370 (180) |
   | 10 | 2 (2), 7 (2), 90 (5), 155 (545), 400 (150), 25000 (320) |
   | 11 | 2 (2), 143 (11), 1012 (11), 5720 (187), 13123 (1837) |
   | 12 | 2 (2), 7 (14), 60 (12), 84 (6), 100 (6), 138 (36), 1608 (12), 2748 (144), 8136 (72), 14985 (2388), 38304 (1404) |

   For itinerary periods $n \le 12$ (temporal period $2n \le 24$), the only domains with a spatial period below 60 are the two stripes and the ether, with
   spatial period 7. No periodic point has a vacuum tail, since $H^{2n}$ raises the top bit of a nonzero finite $V$ by
   $2n$ and cannot fix it.
3. **Positive integers** (proved in Lean for the first sentence, [ShiftModel](../../Rule30Open/PeriodTwo/ShiftModel.md),
   and in the kit's encoding as `Rule30ZeroBoundary.free_not_eventuallyPeriodic`). If $U > 0$ is in $K$ its itinerary is not eventually periodic, since
   $H^{2s}(U)$ would then be a periodic point and finite. So the following would give the problem:
   **(R)** every rational 2-adic number in $K$ has an eventually periodic itinerary. (R) is stronger than the
   problem, and it is not proved.
4. **Rationality is preserved and reflected** (argument). If $H(U) = h$ then $u_{j+1} = h_j \oplus (u_j \lor u_{j-1})$,
   so $U$ is read off $h$ and $u_0$ by a transducer with four states (the kit's backward transducer
   `Rule30ZeroBoundary.back`, with `backward_det` and `back_fin_iff`, in its encoding). A 2-adic integer is therefore rational exactly
   when its image under $H$ is, and the two preimages of a rational point under $H^2$ in $K$ are rational. So every point
   of $K$ with an eventually periodic itinerary is rational, and **(R) says that these are all the rational points of
   $K$**: $K \cap \mathbb{Q}$ is the set of preperiodic points of the shift, the preimage tree of the domains. The
   counts agree: among the 896 points found with denominator 3, the itinerary is constant from reading $s$ on for 2, 2,
   4, 8, 16, 32, 64, 128 and 256 points at $s = 0, 1, \dots, 8$ ($2^s$ for $s \ge 1$, the preimage tree of the two
   stripes; the kit's `Rule30ZeroBoundaryStripe.agrees_pre` keeps preimages stripe-tailed; `--hits`, item 7). These 512 points leave 384 that settle at a reading $s \ge 9$, whose
   counts are not reported here. That the counts fall below $2^s$ from $s = 9$ on only because the heads of the deeper
   preimages outgrow the search is a heuristic: the heads of those preimages have not been computed.
5. **The defect and its top** (argument; the climb rule is tested). Let $U$ be rational with head of $p$ cells and
   tail word $w$ of period $q$ from cell $p$. Far from the low end the tail evolves as the held map on a ring of $q$
   cells, $r' = (r \gg 1) \oplus (r \lor (r \ll 1))$ cyclically, which is periodic in time after a transient
   (`ring_cycle`); call its space-time pattern $B_t(j)$, defined for all $j$ and periodic in $j$. Cells $j \ge p + t$ of
   $H^t(U)$ equal $B_t(j)$, because bit $j$ of $H^t(U)$ reads bits $j - t, \dots, j + t$ of $U$. Let the top $T_t$ be the
   highest cell where $H^t(U)$ differs from $B_t$. If $T_t \ge 0$, cells above $T_t + 1$ stay equal to $B$ one step
   later, and cell $T_t + 1$ becomes a defect exactly when $B_t(T_t + 1) = 0$, since the cell reads
   $B(T+2) \oplus (B(T+1) \lor \lnot B(T))$ against $B(T+2) \oplus (B(T+1) \lor B(T))$. So **the top rises by at most one
   cell per step, and only above a 0 of the background**. If the top is bounded the cells below it form a finite
   system driven by the periodic background, so the orbit of $U$ is eventually periodic and so is its itinerary.
   Conversely, if the itinerary of $U \in K$ is eventually periodic then $H^{2s}(U)$ is a periodic point for large $s$,
   so $H^t(U)$ is eventually periodic in $t$. The background $B_t$ is eventually periodic in $t$ as well, and each
   difference $H^t(U) \oplus B_t$ is finite, since the two agree at cells $j \ge p + t$. So the differences run through
   finitely many finite words, and the top is bounded. So for a rational point of $K$: **eventually periodic itinerary
   $\Leftrightarrow$ bounded top $\Leftrightarrow$ bounded preperiod of $H^t(U)$.** A positive integer has the vacuum
   for tail, where every cell is 0 and the top rises at every step.
6. **Stripe tails are confined** (proved in the kit, in a stronger form, in its encoding: `Rule30ZeroBoundaryStripe`
   has `stripe_confined`, a row equal to the stripe from an odd depth on stays so, `stripe_tail_trace_periodic`, the
   column next to the wall is then eventually periodic, and `stripe_absorb` and `stripe2_absorb`, the row becomes
   exactly the stripe, except for the even-phase stripe the cell next to the wall, which ends up alternating. So the
   itinerary of every point with a stripe tail is eventually constant, the itinerary period 1 of all 896 points of
   item 7. The translation from the kit's encoding to $H$ is not formalized here). A stripe is a fixed point of the ring map, since in $A$ or $B$ one
   of two adjacent cells is 1. It has a 1 in every other column, so the top can rise to cell $p$ and no further: it
   rises above a 0 only, and after rising onto a 0 the next cell is a 1. Hence for every head, cells above $p$ are the
   stripe at every step, cells $0, \dots, p$ follow a deterministic map on $\{0, 1\}^{p+1}$ driven by that fixed
   stripe, and the orbit and the itinerary of every $U$ with a stripe tail are eventually periodic, with or without the
   condition of $K$. This is (R) for every rational with denominator 3 (the tails $A$ and $B$ are exactly $-1/3$ and
   $-2/3$ with a finite head), and for every rational whose tail reaches a stripe on the ring. More precisely, a top on a 1 of the stripe rises onto the next cell, a 0, and a top on a 0 clears at the next
   step, because the cell above it is a 1 of the stripe and the OR reads that 1 in the cell itself. So the top two steps later is never
   higher: $T_{t+2} \le T_t$, and the preperiod of $H^{2s}(U)$ never grows with $s$ (the kit proves this inequality in
   its encoding as `Rule30ZeroBoundaryStripe.agrees_two_steps` and `agrees_run_even`). The kit's `stripe_absorb` and
   `stripe2_absorb` give more, for every head and with no use of $K$: every point with a stripe tail falls onto the
   stripe, except that on the tail $B$ cell 0 ends up alternating (the translation from the kit's encoding is not
   formalized here). So the only periodic points of $K$ with a stripe tail are the two stripes. An independent check:
   with the defect $E$ of the head from the stripe as the state at even steps, the points of $K$ with a stripe tail and
   a head of $\ell$ cells are the greatest invariant set of a finite map on $2^\ell$ states, which is computed exactly
   with no time horizon (`stripe_invariant`). For $\ell = 24$ and both stripes every one of them falls onto the stripe
   (`--invariant 24`: 18 states for $A$ and 8 for $B$, none stuck), as the kit's theorems require. Checked as well:
   over every head of up to 12 bits on both stripes the largest top minus $p$ is 0 (`--stripe 12`, `stripe_window`),
   and two steps never carry the top above the head, asserted in `stripe_invariant` for all $2^{24}$ heads.
7. **Rational points, tested** (computed). The tree of $K$ was walked to depth 64, $2^{32}$ leaves, and at each leaf the
   prefix was extended by every period $q \le 32$ and kept while the forced bits agreed, to 126 bits; the hits were
   extended and kept through 1200 steps in Python integers. This covers every rational point of $K$ with preperiod $p$
   and period $q \le 32$ with $p + q \le 64$: **2,592 points, every one preperiodic in readings 0 to 399** (92 further hits survived the search by chance and
   failed the check), with itinerary period 1, 2 or 4 readings (896, 120, 1,576 points). Their
   denominators are 3 (896 points), 127 (278), 381 (10), 5461 (278), 16383 (1,024), 89,478,485 (6) and 268,435,455 (100):
   tails of period 2, 7, 14 and 28, and no other period. No hit with period 1 survives the 1200-step check (no denominator 1), so no integer $0 \le U < 2^{63}$ is in
   $K$ (an integer in $K$ would be a hit). In Lean, the kit's `Rule30ZeroBoundaryWidth52.not_inX_of_width_le_52`
   constrains the even steps, so for $U \in K$ it applies to $H(U)$, which is one cell wider than $U$
   (`heldOrbit_topBit`); it excludes every $U < 2^{51}$, in the kit's encoding. **The
   ring attractor of every tail is a stripe (896 points) or the ether, the cycle of four states on seven cells
   (1,696 points).** The denominators are the divisors of $2^q - 1$ of the tails: 3 for the stripes, 127 for
   the ether's period 7, and the rest from period 14 and 28 tails that fall onto the ether on the ring. The smaller
   search of `--rational 40` (tails with $p + 2q \le 40$, 213 points) agrees. The other domains of the zoo have
   spatial period 60 or more, above the tail periods $q \le 32$ of the search, so it cannot find them or the points
   that fall onto them.
8. **The ether** (computed, not proved). The ether has no column of ones, and the greedy chase of the top (rise
   whenever the background above is 0) reaches cell 1,167 in 2,000 steps, so item 6 does not apply. Defects do stall: over every head of
   6 bits and all 28 tail words of the ether cycle (the four states, each rotated), the largest top minus $p$ is 27 in
   steps 0 to 299, 23 in steps 300 to 749 and 23 in steps 750 to 1499 (`--ether 6`). A front automaton that follows the top
   window of $w$ cells and treats the cells below as free, with the cells lost below the window as a jump of $w - 1$,
   has a longest path over 3,200 steps of rate 0.22 and 0.18 per step for $w = 8$ and 10 (`--front 8`,
   `--front 10`; `front_rate` counts a pass through the node for a lost top as a step). The automaton for $w = 8$ has
   a cycle of positive gain: its longest walk of 20,000 steps gains 4,381, and a walk with no positive cycle gains at
   most one less than the 3,588 nodes, since no edge gains more than 1 (`--front 8 --rounds 20000`). So does the automaton
   for $w = 10$: 90,000 steps gain 15,757 on 14,340 nodes (`--front 10 --rounds 90000`, about 40 s), and for
   $w = 12$: 400,000 steps gain 63,643 on 57,348 nodes (`--front 12 --rounds 400000`, about 12 minutes). So the bound allows the top to rise without limit, and the stall
   is a property of the cells below the window that this bound does not see.
   Two more facts limit this route ([ether fronts](../../negative-results/period-two/ether-front-windows.md)): no
   strip of 12 cells or fewer below the top is closed under every input from below, and the condition of $K$ removes
   no transition of a top-window automaton whose window lies above the lag at which it checks $K$. The ether is the only cycle besides the stripes that
   the tails of $K$ reach in the range of item 7, and bounding its defects is what remains of (R) there.
9. **The same for other blocks** (computed). With the center repeating a block $b$, the left half follows the kicked
   map $U \mapsto (U \gg 1) \oplus (U \lor (U \ll 1) \lor c'_t)$ with $c'_t = b(t) \land b(t + 1)$ and cell $-1$ fixed
   at the black phases ([LeftLatch](../../Rule30Open/Columns/LeftLatch.md), checks without the latch, which adds
   nothing for $011$). The same construction makes it the full shift on the white phases, and its periodic points
   are domains. The smallest has spatial period 12 for $011$ (two points, at $n = 1$), and for $001$ the stripe
   (period 2) and period 12 at $n = 1$:

   | block | $n$ | spatial periods (count) |
   |---|---|---|
   | $011$ | 1 | 12 (2) |
   | $011$ | 2 | 12 (2), 84 (2) |
   | $011$ | 3 | 12 (2), 135 (6) |
   | $011$ | 4 | 12 (2), 84 (2), 138 (12) |
   | $011$ | 5 | 12 (2), 540 (5), 795 (5), 2145 (20) |
   | $001$ | 1 | 2 (1), 12 (3) |
   | $001$ | 2 | 2 (1), 12 (3), 84 (12) |
   | $001$ | 3 | 2 (1), 12 (3), 135 (60) |
   | $001$ | 4 | 2 (1), 12 (3), 60 (68), 84 (16), 100 (24), 138 (144) |
   | $001$ | 5 | 2 (1), 12 (3), 64 (175), 85 (5), 105 (10), 540 (155), 795 (85), 2145 (590) |

   So the integer map for $011$ is the kicked map above with $c' = 0, 1, 0$ at the three phases, cell $-1$ equal to 0
   at the phase where the block reads $1, 1$ and 1 at the phase where it reads $1, 0$. It reduces to an integer
   map like $H$, and the counting is the same as for period two with one free reading in three: a Cantor set of
   dimension $1/3$ that is a full shift under three steps.

## What it means

The problem is a statement about which points of a full 2-shift are positive integers. The periodic points are
domains of growing spatial period, none of them a vacuum, and the rational points tried are all preperiodic: the
2-adic numbers of $K$ with a simple expansion are the ones that settle into a domain. A positive integer is a
rational with the simplest expansion there is, so (R) is the form of the question that treats all rationals alike.

In terms of the dynamics, (R) is a statement about a boundary between a fixed low-end condition (cell 0 reads 1 at
every odd step) and a far field that is periodic in space and, after a transient, in time. The far field enters from
the high end at speed 1 through the XOR, the low end acts upward at speed 1 through the OR, and the itinerary is the
low end's reading at even steps. The front between them rises only above a 0 of the background. Where the background
has a column of ones (the stripes) the front is stuck and the claim is a theorem for every head, with no use of $K$.
On the vacuum the front rises at every step, and that is the case of a positive integer; the ether is in between,
stalling in every trial. For a background where a front can run, the condition of $K$ would have to be what stops it,
and no point of $K$ with such a tail turned up in the range of item 7. So (R) is no easier than the problem it implies
for the vacuum, and it is proved for the stripes. Nothing here proves it in general or points to a proof: the forced
bits computed are dense polynomials ([the forced bits](../../negative-results/period-two/forced-bits-dense.md)).

## Reproduce

```bash
python -m computations.held_shift --zoo 12
python -m computations.held_shift --zoo 5 --block 011
python -m computations.held_shift --zoo 5 --block 001
python -m computations.held_shift --rational 40
python -m computations.held_shift --stripe 12
python -m computations.held_shift --invariant 24
python -m computations.held_shift --ether 6
python -m computations.held_shift --front 8 --rounds 20000
python -m computations.held_shift --front 10 --rounds 90000
gcc -O3 -mno-avx -fopenmp computations/held_shift_search.c -o search
./search 64 32 126 10 8 > hits.txt
python -m computations.held_shift --hits hits.txt --depth 64
```

The first takes a few minutes, the second and third seconds, the fourth about two minutes, `--stripe`
seconds, `--front 8` seconds, `--front 10` about 40 s, `--ether 6` about two minutes. The search takes about 30 minutes on 8 threads for depth 64 (about 70 s for depth 56
with $q \le 28$), and `--hits` about 30 s. `tests/test_held_shift.py` checks the tree against stepping
all integers below $2^{12}$, the itineraries as a shift, each periodic point against the kicked map on 400 bits for
the blocks $01$, $011$ and $001$, the degree profile against a Moebius transform, the climb rule of the top, the
stripe confinement, the attractors of the tails, the verification of hits, the stalling on the ether for 2-bit heads
and the front bound on the vacuum, a stripe and the ether.
