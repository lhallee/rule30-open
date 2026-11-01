---
title: No point of K has a tail from cell 16 on equal to a background of the tail census other than the stripes and the ether
category: period-two
problems: [1]
status: proved
lean: Rule30Open.PeriodTwo.NoKTails16
headline: [no_k_tail16_L1P1, no_k_tail16_L4P8, no_k_tail16_L5P5, no_k_tail16_L7P63, no_k_tail16_L8P40, no_k_tail16_L9P72, no_k_tail16_L9P171, no_k_tail16_L10P15, no_k_tail16_L11P17, no_k_tail16_L11P154, no_k_tail16_L12P3, no_k_tail16_L12P102, treeWith_sound, treeRun_sound, not_inK_of_tree, colRaw_eq, tabOK_spec]
kit: new
kit_modules: [Rule30PeriodTwo, Rule30ZeroBoundary]
evidence: [computations/no_k_tails16.py, computations/tail_census.py]
---

# No point of K has a tail from cell 16 on equal to a background of the tail census other than the stripes and the ether

Let $H(U) = (U \gg 1) \oplus (U \lor (U \ll 1))$ be the held map and $K$ the set of 2-adic $U$ with $H^t(U)$ odd at
every odd $t$ ([the shift model](ShiftModel.md); `InK`). A rational point of $K$ has a head and a periodic tail, and far
from cell 0 the tail falls onto a *background*, a cycle of $P$ states of the held map on a ring of $L$ cells ([the tail
census](../../findings/period-two/tail-census.md)). The periodic tails of up to 12 cells reach 14 backgrounds. On the
stripes (proved in the kit) and on the ether (heads of up to 16 cells, [EtherCensus16](EtherCensus16.md)) conjecture
(R) holds because every defect stays bounded. Item 4 of the tail census finds that on each of the other 12 (the vacuum
and the 11 that carry fronts) every head of up to 16 cells breaks $K$. This module proves that census in Lean, every
background and every head of up to 16 cells. [NoKTails](NoKTails.md) proves it for 4 of the 11 front backgrounds with
heads of up to 12 cells.

## Statement

A background is given by its states $s_0, \dots, s_{P-1}$, words of $L$ cells. At the alignment $(a, o)$ its cell $j$
is $b_{a,o}(j)$ = bit $(j + o) \bmod L$ of $s_{a \bmod P}$ (`ringCell st L a (j + o)`).

- `no_k_tail16_L1P1` through `no_k_tail16_L12P102`: for each of the 12 backgrounds, named by $(L, P)$ in the table
  below, if $u(j) = b_{a,o}(j)$ for every $j \ge p$, with $p \le 16$ and any $a, o$, then $u \notin K$. For the vacuum
  ($L = P = 1$) this says that no integer below $2^{16}$ is in $K$, which the kit's `Rule30ZeroBoundaryWidth52` and
  [the shift model](ShiftModel.md) already give for every integer below $2^{51}$; it is included so that the 12
  backgrounds of the census are covered alike.
- `colRaw_eq`: the kernel's bit 0 of $H^d(n)$ is bit 0 of `Nat.repeat heldNat d n`.
- `treeWith_sound`, `treeRun_sound`: the walk of the tree of $K$ below is sound, with any test at the leaves and with
  `breakRun` there.
- `not_inK_of_tree`: the reduction of a background to the finite tables the kernel checks.

The states of each background are checked to be a cycle of the held map on the ring (`states..._cycle` with
`ringStepOK` of NoKTails), and `ringCell_step` of NoKTails extends this to every phase and cell.

## Argument

**The tree of $K$.** Bit 0 of $H^d(u)$ is $u_d$ xor a function of $u_0, \dots, u_{d-1}$ (`column_triangular` of the
shift model), and it reads no cell above $d$. So at an odd step $d$, once the cells below $d$ are fixed, exactly one
value of cell $d$ keeps bit 0 of $H^d$ odd, whatever the cells above $d$ are; the other value breaks $K$ at step $d$.
The heads of 16 cells that do not break $K$ at an odd step below 16 therefore form a binary tree that branches at the
even cells $0, 2, \dots, 14$ and is forced at the odd cells: $2^8 = 256$ leaves among the $2^{16}$ heads, for any tail.
This is the count of residues of item 1 of the shift model.

**The checker.** `treeRun R 16 0 W` starts from the number $W$ that holds the background on the cells $16, \dots, 63$
and 0 below, and walks the cells $d = 0, \dots, 15$: at an even $d$ it tries both values, and at an odd $d$ it keeps the
value that makes bit 0 of $H^d$ odd (`colRaw`, evaluated on the number whose cells $d, \dots, 15$ are still 0, which
bit 0 of $H^d$ does not read above $d$). At each leaf it runs `breakRun R` of NoKTails, which succeeds when bit 0 of
$H^{2s+1}$ is 0 for some $s < R$. With $R = 24$ the odd steps checked are $1, 3, \dots, 47$, all below 64.

**Soundness** (`treeRun_sound`, by induction on the cells left). Let $u$ agree with the number $n$ of a node on the
cells below $d$ and on the cells $16, \dots, 63$. At an even $d$ the branch with $u_d$ continues. At an odd $d$, if
$u_d$ is the chosen value the walk continues; otherwise $u$ agrees with the chosen number below $d$ and differs from it
at $d$, so by `column_triangular` bit 0 of $H^d(u)$ is the complement of the chosen number's, which is 1: $u$ breaks $K$
at the odd step $d$. That the chosen number reads 1 comes from `colRaw_eq` and, when cell $d$ is set, from
`heldNat_triangular` of the shift model, since setting cell $d$ flips bit 0 of $H^d$. At a leaf $u$ agrees with the
number on the cells $0, \dots, 63$, and a break that `breakRun` finds at a step below 64 is a break of $u$
(`not_inK_of_breakRun`, with `column_eq_of_agree` of NoKTails).

**Tables.** The cells $16, \dots, 63$ depend on the alignment only through the ring word read from cell $o$ of state
$a$, so the $PL$ alignments share fewer tail words. For each background the module lists the distinct words in chunks of
at most 32 and, in row $a$ and place $o$, the index $e$ of the word of the alignment $(a, o)$: word $e \bmod 32$ of
chunk $\lfloor e / 32 \rfloor$. `tabOK` walks the list of states and the list of rows together by their recursors, so
that each list is read once, and checks that each row has $L$ entries and that the word each entry names exists and
holds the state on the cells $16, \dots, 63$, read from cell $o$, and 0 below (`tailEntryOK`, `wordOK`; `tabOK_spec`,
`rowOK_spec`, `wordOK_spec`). Reading the word of each alignment by its position in one long list, as NoKTails does,
took the kernel past 6 GB of memory on the background with 1,224 alignments in a trial, where it was stopped. `wordsOK`
runs the tree on every word of a chunk as one kernel computation (`ktree...`).

**The theorem.** For any alignment, `not_inK_of_tree` reduces $(a, o)$ to $(a \bmod P, o \bmod L)$, which gives the
same cells, finds its word in the table, and applies `treeRun_sound` at the root.

## The census

`python -m computations.no_k_tails16` runs the same walk on the same tables:

| background | $(L, P)$ | alignments $PL$ | distinct tail words | heads | leaves run | latest break | steps of $H$ |
|---|---|---|---|---|---|---|---|
| $0$ (the vacuum) | (1, 1) | 1 | 1 | 65,536 | 256 | step 31 | 11,580 |
| $1000$ | (4, 8) | 32 | 8 | 524,288 | 2,048 | step 37 | 92,112 |
| $11100$ | (5, 5) | 25 | 5 | 327,680 | 1,280 | step 37 | 57,744 |
| $1010000$ | (7, 63) | 441 | 63 | 4,128,768 | 16,128 | step 43 | 726,250 |
| $11100000$ | (8, 40) | 320 | 40 | 2,621,440 | 10,240 | step 37 | 461,150 |
| $111000000$ | (9, 72) | 648 | 72 | 4,718,592 | 18,432 | step 47 | 829,832 |
| $100100000$ | (9, 171) | 1,539 | 171 | 11,206,656 | 43,776 | step 41 | 1,970,358 |
| $1110100000$ | (10, 15) | 150 | 30 | 1,966,080 | 7,680 | step 43 | 345,488 |
| $10010100000$ | (11, 17) | 187 | 187 | 12,255,232 | 47,872 | step 43 | 2,155,166 |
| $10100000000$ | (11, 154) | 1,694 | 154 | 10,092,544 | 39,424 | step 43 | 1,775,554 |
| $111110010000$ | (12, 3) | 36 | 12 | 786,432 | 3,072 | step 39 | 138,582 |
| $100100000000$ | (12, 102) | 1,224 | 408 | 26,738,688 | 104,448 | step 45 | 4,702,950 |

The 1,151 tail words are the distinct alignments of the tail census, and the 75,431,936 heads and the latest breaks
are those of its item 4 for heads of 16 cells. The walk takes 13,266,766 steps of $H$ on numbers below $2^{112}$, about
11,500 per word. A run of `breakRun` on all $2^{16}$ heads of a word, as in NoKTails, takes about 17 times as many
(196,662 steps against 11,580 on the vacuum, and a ratio of 16.8 to 17.3 on the first word of each background,
`--compare`): a head off the tree breaks within its first 15 steps, but each of the 65,536 heads costs at least one.

`lake build Rule30Open.PeriodTwo.NoKTails16` took 327 s of wall time with its imports built, and its Lean process
stayed under 1.1 GB of resident memory (sampled every second), since the module elaborates its kernel checks one at a
time (`Elab.async false`); a measurement on one machine, not a cost model.

```bash
python -m computations.no_k_tails16           # the census above, a few seconds
python -m computations.no_k_tails16 --lean    # the background section of the module
python -m computations.no_k_tails16 --compare # the walk against breakRun on every head, about a second
lake build Rule30Open.PeriodTwo.NoKTails16
```

`tests/test_no_k_tails16.py` checks the backgrounds against `tail_census.ring_backgrounds`, the tail words against the
cells of the background and their number against `tail_census.alignments`, the tree at a head of 8 cells against a run
of every head on whole halves of 160 cells (the leaves are exactly the heads with no break up to step 7, and the latest
break is the latest over all heads), the leaves' breaks against `tail_census.in_k_steps`, the latest breaks of four
backgrounds against the tail census, and the background section against the module.

## What it means

For every background that a periodic tail of up to 12 cells reaches, (R) of the shift model now holds in Lean for every
2-adic integer whose tail from cell 16 on is that background at any alignment, except on the stripes, where the kit
proves it in its own encoding of the left half (the translation to $H$ is not formalized here): on the ether because
every defect stays bounded ([EtherCensus16](EtherCensus16.md)), and on the other 12 because no such point of $K$ exists.
As the tail census notes, this covers a tail that reaches the background only after $\tau$ steps of the ring as well:
for $u \in K$ and $\tau'$ the even one of $\tau, \tau + 1$, $H^{\tau'}(u)$ is in $K$ (`inK_heldOrbit`) and has the
background for tail from cell $p + \tau'$ on, so no such point exists when $p + \tau' \le 16$; this corollary is not
stated in the module.

The tree is what makes heads of 16 cells cheap: the condition of $K$ at the odd cells halves the heads at each of
them, so the kernel runs $2^{h/2}$ leaves for heads of $h$ cells instead of $2^h$ heads. It does not bound longer
heads. The 256 leaves of a word are the residues of $K$ with that tail, and the share of heads still in $K$ after $t$
steps is close to $2^{-t/2}$ on the vacuum and every front, as far as the tail census measures it (heads of 14 cells,
up to step 24, and step 32 on nine fronts); on the vacuum the question is the period-two question itself
([the tail census](../../findings/period-two/tail-census.md), item 4). Each further pair of cells doubles the leaves.

## The kit

The kit's `Rule30PeriodTwo` reduces period two to the held map on positive integers and checks every start of width at
most 52 (statement `Q01`), the vacuum background, and `Rule30ZeroBoundary` counts the residues of the constrained left
half (`count_constrained`), the same tree in its encoding. Neither the pinned kit nor its main branch has a statement
about 2-adic halves with a periodic tail on these backgrounds; its stripe modules (`Rule30ZeroBoundaryStripe` and the
stripe-prefix families) treat the stripes only.
