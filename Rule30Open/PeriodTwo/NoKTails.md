---
title: No point of K has a tail on the backgrounds with (L, P) = (4, 8), (5, 5), (10, 15) or (12, 3) from cell 12 on
category: period-two
problems: [1]
status: proved
lean: Rule30Open.PeriodTwo.NoKTails
headline: [no_k_tail_48, no_k_tail_55, no_k_tail_1015, no_k_tail_123, not_inK_of_tables, breakRun_sound, column_eq_of_agree, ringCell_step]
kit: new
kit_modules: [Rule30PeriodTwo, Rule30ZeroBoundary]
evidence: [computations/no_k_tails.py, computations/tail_census.py]
---

# No point of K has a tail on the backgrounds with (L, P) = (4, 8), (5, 5), (10, 15) or (12, 3) from cell 12 on

Let $H(U) = (U \gg 1) \oplus (U \lor (U \ll 1))$ be the held map and $K$ the set of 2-adic $U$ with $H^t(U)$ odd at
every odd $t$ ([the shift model](ShiftModel.md); `InK`). A rational point of $K$ has a head and a periodic tail, and far
from cell 0 the tail falls onto a *background*, a cycle of $P$ states of the held map on a ring of $L$ cells ([the tail
census](../../findings/period-two/tail-census.md)). Item 4 of the tail census finds that on every background other than
the stripes and the ether, every head of up to 16 cells breaks $K$. This module proves it in Lean for the heads of up to
12 cells on the four backgrounds of that census with the fewest alignments besides the vacuum, the stripes and the
ether.

## Statement

A background is given by its states $s_0, \dots, s_{P-1}$, words of $L$ cells. At the alignment $(a, o)$ its cell $j$
is $b_{a,o}(j)$ = bit $(j + o) \bmod L$ of $s_{a \bmod P}$ (`ringCell st L a (j + o)`).

- `no_k_tail_48`, `no_k_tail_55`, `no_k_tail_1015`, `no_k_tail_123`: for the backgrounds named by a state, cell 0
  first, $1000$ with $(L, P) = (4, 8)$, $11100$ with $(5, 5)$, $1110100000$ with $(10, 15)$ and $111110010000$ with
  $(12, 3)$: if $u(j) = b_{a,o}(j)$ for every $j \ge p$, with $p \le 12$ and any $a, o$, then $u \notin K$.
- `bgStep48` and its siblings, through `ringCell_step`: each list of states is a cycle of the held map on the ring,
  $s_{a+1}(j) = s_a(j + 1) \oplus (s_a(j) \lor s_a(j - 1))$ with the cells read modulo $L$, at every phase and cell.
- `column_eq_of_agree`: two halves that agree on the cells $0, \dots, t$ have the same bit 0 of $H^t$.
- `breakRun_sound`, `breakRun_start`: the checker below is sound.
- `not_inK_of_tables`: the reduction of a background to the finite tables the kernel checks.

## Argument

**A finite truncation decides.** Bit 0 of $H^t(u)$ is bit $t$ of $u$ plus a function of the bits below $t$
(`column_triangular` of the shift model), so it reads only the cells $0, \dots, t$, and two halves that agree there
have the same bit 0 at step $t$ (`column_eq_of_agree`). Let $N$ be the number whose bits $0, \dots, 63$ are the cells
$0, \dots, 63$ of $u$ and whose higher bits are 0: its head `natOf u 12` in the bits below 12, and the background in
the bits 12 to 63 (`tailWord`). A head of $p < 12$ cells is a head of 12 cells whose cells $p$ to 11 happen to be the
background's, so the case $p = 12$ covers it. For every odd $t < 64$, $u$ breaks $K$ at step $t$ exactly when
$H^t(N)$ is even, and $H^t(N)$ on numbers is the held orbit of the bits of $N$ (`heldNat_repeat_testBit`).

**The checker.** `breakRun R N` runs $R$ rounds of two steps of $H$ on $N$, written with the raw operations of
`Nat` that the kernel evaluates on numbers (`heldRaw`), and succeeds when the number is even after the first step of a
round. If it succeeds, $H^{2s+1}(N)$ is even for some $s < R$ (`breakRun_sound`, by induction on the rounds from
$N = H^{2k}(N)$ at $k = 0$; `breakRun_start`). With $R = 17$ the odd steps checked are $1, 3, \dots, 33$, all below 64.

**Tables.** The bits 12 to 63 of $N$ depend on the alignment only through the word read from cell $o$ of state $a$,
so the $PL$ alignments share few tail words. For each background the module lists the states, the distinct tail words
(`bgWords48` and its siblings) and, for each alignment $(a, o)$ with $a < P$ and $o < L$, the index of its word
(`bgIndex48`); `indexOK` checks every index against `tailWord`. `censusOK 17 W` runs the checker on every head
$h < 2^{12}$ with the tail word $W$, that is on $N = h \lor W$, as one kernel computation per word
(`kcensus48_0` and the rest). The states are checked to be a cycle of the ring map (`bgStates48_cycle`), which
`ringCell_step` extends to every phase and cell.

**The theorem.** For any alignment, `not_inK_of_tables` reduces $(a, o)$ to $(a \bmod P, o \bmod L)$, which gives the
same cells, finds its word in the table, reads the head off $u$, and applies the census to $N$: the break of $N$ at an
odd step below 34 is a break of $u$ there, so $u \notin K$.

## The census

`python -m computations.no_k_tails` runs the same checker on the same tables:

| background | $(L, P)$ | alignments $PL$ | distinct tail words | heads checked | latest break | rounds |
|---|---|---|---|---|---|---|
| $1000$ | (4, 8) | 32 | 8 | 32,768 | step 29 | 65,531 |
| $11100$ | (5, 5) | 25 | 5 | 20,480 | step 31 | 41,029 |
| $1110100000$ | (10, 15) | 150 | 30 | 122,880 | step 33 | 245,767 |
| $111110010000$ | (12, 3) | 36 | 12 | 49,152 | step 33 | 98,321 |

The 225,280 heads are the census of item 4 of the tail census on these four backgrounds at their distinct alignments,
and the latest breaks are the ones it reports for the heads of 12 cells. The kernel runs 450,648 rounds of two steps
on numbers below $2^{98}$, in 55 checks of 4,096 heads, a smaller computation than the census of
[EtherCensus](EtherCensus.md) (an estimate from the round counts, not a timing).

```bash
python -m computations.no_k_tails           # the census above, under a second
python -m computations.no_k_tails --lean    # the background section of the module
lake build Rule30Open.PeriodTwo.NoKTails
```

`tests/test_no_k_tails.py` checks the backgrounds against the cycles of `tail_census`, the tail words and their index
against the cells of the background, the checker against a direct run of the held map on whole integers that carry
the background over 160 cells, the latest breaks against `tail_census.in_k_steps`, and the background section against
the module.

## What it means

For these four backgrounds the route of the tail census closes in Lean as far as heads of 12 cells: (R) of the shift
model holds for every rational point of $K$ whose tail from cell 12 on is one of them, because there is none. As the
tail census notes, this covers a tail that reaches the background only after $\tau$ steps of the ring as well: for
$u \in K$ and $\tau'$ the even one of $\tau, \tau + 1$, $H^{\tau'}(u)$ is in $K$ (`inK_heldOrbit`) and has the
background for tail from cell $p + \tau'$ on, so no such point exists when $p + \tau' \le 12$; this corollary is not
stated in the module. Nothing here bounds longer heads: the share of heads still in $K$ after $t$ steps falls like
$2^{-t/2}$ on every background, as on the vacuum, where the question is the period-two question itself.

## The kit

The kit's `Rule30PeriodTwo` reduces period two to the held map on positive integers and checks every start of width
at most 52 (statement `Q01`), the vacuum background; its frozen-boundary equivalents prove the triangularity behind
`column_eq_of_agree` for their maps. It has no statement about 2-adic halves with a periodic tail on these
backgrounds.
