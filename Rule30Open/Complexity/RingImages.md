---
title: On a ring of W cells one step of Rule 30 misses exactly (p_W + 1)/2 - [3 | W] rows, p_W the power sums of the roots of x³ - x² - 2
category: complexity
problems: [3]
status: proved
lean: Rule30Open.Complexity.RingImages
headline: [ring_missed_rows, ring_missed_rows_div, ring_image_card, ring_preimages_le_three, ring_three_preimages, numWithPreds_zero_closed, numWithPreds_two_closed]
kit: refines
kit_modules: [Rule30Predecessors, Rule30PredecessorCounts]
evidence: [computations/ring_images.py]
---

# On a ring of W cells one step of Rule 30 misses exactly (p_W + 1)/2 - [3 | W] rows, p_W the power sums of the roots of x³ - x² - 2

A row of a ring of $W$ cells has cell $W - 1$ beside cell $0$, and one step of Rule 30 sends it to the row whose cell
$i$ is $x_{i-1} \oplus (x_i \lor x_{i+1})$, indices mod $W$. Let $p_W$ be the sum of the $W$-th powers of the three
roots of $x^3 - x^2 - 2$: $p_0 = 3$, $p_1 = p_2 = 1$ and $p_{n+3} = p_{n+2} + 2 p_n$. This module proves, for every
$W \ge 1$, that the rows the step does not reach number

$$m_W = \frac{p_W + 1}{2} - [3 \mid W],$$

that no row has more than three preimages, and that exactly one row has three when $3 \mid W$ and none otherwise. This
is the formula of the finding [ring images](../../findings/structure/ring-images.md), which states it for $W \ge 3$;
it holds for $W = 1$ and $2$ as well.

## Statement

A row is a list of $W$ booleans. `rows W` lists all of them, each once (`rows_count`), $2^W$ in all (`rows_length`);
`ringStep` is the step above (`ringStep_getD` checks it cell by cell); `preimages W z` is the number of rows that
`ringStep` maps to `z`; `missed W` is the number of rows `z` with `preimages W z = 0`; and `powerSum` is $p_W$.
For every $W \ge 1$:

- `ring_missed_rows`: $2\, m_W + 2 [3 \mid W] = p_W + 1$.
- `ring_missed_rows_div`: $m_W = (p_W + 1)/2 - [3 \mid W]$, in natural numbers.
- `ring_image_card`: the rows with a preimage and the rows without one number $2^W$ together (for every $W$).
- `ring_preimages_le_three`: every row has at most three preimages.
- `ring_three_preimages`: the rows with exactly three preimages number $[3 \mid W]$.
- `numWithPreds_zero_closed` and `numWithPreds_two_closed`: in the kit's terms, the registers of $N \ge 1$ cells with no
  predecessor number $c_0$ and those with two number $c_2$, where $2 c_0 + 2[3 \mid N] = p_N + 1$ and
  $2 c_2 + 6 [3 \mid N] = p_N + 1$.

The first values of $m_W$, for $W = 1, \dots, 8$, are $1, 1, 3, 5, 6, 12, 22, 33$; the module checks $W \le 6$ by
enumerating all rows, and `computations/ring_images.py` checks $W \le 24$.

## Argument

1. **Collisions are cyclic words.** Rule 30 is left permutive: $x_{i-1}$ is fixed by the new cell $i$ and by $x_i$,
   $x_{i+1}$. So two rows with one image that agree on two adjacent cells agree on the cell to their left, and going
   left around the ring, on every cell. Two distinct rows $x \ne y$ with one image therefore differ on every pair of
   adjacent cells. Read the pair as a word over the four letters $(x_i, y_i)$: the ordered pairs of distinct rows with
   one image are exactly the words whose every cyclic window of three letters passes one local test, "Rule 30 gives
   both rows the same cell here, and the rows do not agree on both of the last two cells". The same holds for ordered
   triples of pairwise distinct rows with one image, as words over eight letters that pass the test on each of the
   three pairs.
2. **Cyclic words are traces.** For any alphabet and any test on windows of three letters, let $M$ be the matrix on
   pairs of letters with an entry $1$ from $(a, b)$ to $(b, c)$ when $a, b, c$ passes. The words of length $W$ that pass
   on every cyclic window correspond to the closed walks of length $W$ in $M$, and number $\operatorname{tr} M^W$:
   the walk visits the pairs $(c_{W-1}, c_0), (c_0, c_1), \dots, (c_{W-1}, c_0)$.
3. **The traces satisfy recurrences.** For the 16 states of pairs, $M_2^2 (M_2 - 1)(M_2^3 - M_2^2 - 2) = 0$; for the 64
   states of triples, $M_3^5 = M_3^2$. Both are identities between entries of small powers, checked by evaluation.
   Since $M^{n+k} = M^n M^k$, an identity among $M^k, \dots, M^{k+j}$ holds among $M^{n+k}, \dots, M^{n+k+j}$, and so
   among their traces. The sequence $p_W + 1$ satisfies the pair recurrence, $6 [3 \mid W]$ the triple one, and both
   agree with the traces for the first few $W$; so the ordered pairs number $P_W = p_W + 1$ and the ordered triples
   $T_W = 6 [3 \mid W]$ for every $W \ge 1$.
4. **At most three preimages.** Distinct preimages of one row differ on the pair (cell $W - 1$, cell $0$) by step 1.
   One of the four values of that pair is impossible: $(0, 1)$ would make cell $0$ of the image black and $(1, 1)$
   would make it white. So a row has at most three preimages.
5. **Counting.** For a number $c \le 3$ of preimages,
   $6 [c = 0] + 6 c + c (c - 1)(c - 2) = 6 + 3 c (c - 1)$. Sum over all rows $z$, with $c = c(z)$: the $c(z)$ add up to
   $2^W$, $\sum_z c(z)(c(z) - 1) = P_W$ and $\sum_z c(z)(c(z) - 1)(c(z) - 2) = T_W$. So $6 m_W + T_W = 3 P_W$, which
   is $2 m_W + 2[3 \mid W] = p_W + 1$. With the same identity, $c(c - 1)(c - 2) = 6 [c = 3]$ gives one row with three
   preimages exactly when $3 \mid W$.

## In Lean

The module uses core Lean only. Sums are `lsum` over lists, and the words of length $n$ over an alphabet are
`words alph n`.

- Step 1 is `pair_collision_iff`: `diag_back` spreads agreement on the last two cells of a chain to every cell, and
  `diag_front` finds agreement at the start of a chain that fails the test somewhere. `lsum_words_pair` turns sums over
  pairs of rows into sums over words of pairs, and `pairs_eq_trace` and `triples_eq_trace` combine them with
  `cyc_count`.
- Step 2 is `cyc_count`, for any alphabet that lists each letter once (`Complete`), with `walk n a b c d` the entries
  of the $n$-th power (`walk_spec`).
- Step 3 is `walk_add` and `trace_rec`. The entry identities `recP` and `recT` are `decide +kernel` evaluations over all
  $16^2$ and $64^2$ entries; `recT` takes most of the module's build time, about 25 seconds. `pairTrace_eq` and
  `tripleTrace_eq` are the inductions.
- Step 4 is `eq_of_seam` (from `stepChain_inj`, left permutivity on a chain) and `preimages_le_three`.
- Step 5 is `pairs_total`, `triples_total` and `six_missed`.

`ringStep_eq_step` shows that `ringStep` is the kit's `Rule30.step`, `countP_rows_eq_regs` that counting over `rows W`
is counting over the kit's `Rule30.regs W`, and `missed_eq_numWithPreds` that $m_W$ is the kit's
`Rule30.numWithPreds 0 W`.

## Relation to the kit

[`Rule30Predecessors`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Predecessors.lean)
proves, for a cyclic register, that every register has at most three predecessors and characterizes the counts
three and one; [`Rule30PredecessorCounts`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30PredecessorCounts.lean)
proves that one register has three predecessors when $3 \mid N$ and none otherwise (`numWithPreds_three`), and
$c_0 = c_2 + 2 [3 \mid N]$ (`numWithPreds_zero`). It does not count $c_0$ or $c_2$. This module adds the closed form
of both; `ring_preimages_le_three` and `ring_three_preimages` are independent proofs of the kit's bound and count, by
transfer matrices instead of the kit's fixed points of transfer maps. On the line, the kit's
`Rule30Equivalents.Preimages.card_le_three` is the bound for every configuration. Counting rows without a preimage on
rings by transfer matrices is a standard method, and the closed form is not claimed new to the literature on preimages.
