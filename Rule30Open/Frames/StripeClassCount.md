---
title: The stripe relation at time 0 or 1 has exactly 2^(A+B) + 3 * 2^(A-1) classes on the box [-A, B]
category: frames
problems: [1]
status: proved
lean: Rule30Open.Frames.StripeClassCount
headline: [StripeClasses.s01_class_count, StripeClasses.joined_iff, StripeClasses.rep_of_S01, StripeClasses.tail_of_Phi_stripe]
kit: refines
kit_modules: [Rule30StripeMeeting]
evidence: [computations/stripe_classes.py]
---

# The stripe relation at time 0 or 1 has exactly 2^(A+B) + 3 * 2^(A-1) classes on the box [-A, B]

Join two rows supported in $[-A, B]$ when the kit's stripe relation holds between them, or between their images one
step later while their center cells agree. For $A, B \ge 1$ the classes number exactly
$2^{A+B} + 3 \cdot 2^{A-1}$, and they are described explicitly: two rows are joined iff they have the same
representative. With [StripeClasses](StripeClasses.md), this says the bound on center columns there is the best the
stripe relation can give.

## Statement

`S01 B x y` is `StripeRelated x y B`, or equal bit $B$ (cell 0) and `StripeRelated (Phi x) (Phi y) (B + 1)`.
`BoxS01 A B` is `S01` between rows below $2^{A+B+1}$, and `Joined` is the equivalence closure of a relation.

- `rep_of_S01`: the representative `rep B` of [StripeClasses](StripeClasses.md) (one move to a row with cell $B$
  black, or the row itself) is constant on `S01` pairs, for every $B \ge 1$ and all rows.
- `joined_iff`: two rows of the box are joined iff they have the same representative.
- `s01_class_count`: the $2^{A+B} + 3 \cdot 2^{A-1}$ rows `boxRep A B i` are rows of the box, every row of the box is
  joined to one of them, and no two of them are joined.

Per left part: the $2^B$ rows with a given left part form $2^{B-1} + 1$ classes, or $2^{B-1}$ when the left part ends
in $0\,1$ (cell $-1$ white, cell $0$ black); classes never mix left parts.

## Argument

Write words in cell order. The stripe words of length $n$ are $S_n = \{(10)^k 1 0^a, (10)^k 11 0^a\}$; there are $n$
of them, all start with 1, and exactly one, $s^*_n$, ends with 1. Let $T_n = \{1\,0^{n-1}\} \cup 0\,S_{n-1}$.

1. **The time-0 relation.** Rows are related through cut $j$ iff their cells $B - j, \dots, B$ are stripe words, the
   cell before is white in both and they agree to the left. Such a block is the last black cell and the stripe
   structure before it, so the representative replaces the block by $s^*_{j+1}$ whatever the block was
   (`rep_of_cut`, by induction on the kit's `StripeWord`; `rep_of_stripeRelated`).
2. **One step maps $T_n$ onto $S_n$.** One step of Rule 30 takes the cells $r, \dots, B$ (white beyond) to the cells
   $r + 1, \dots, B + 1$ bijectively, and computes $1\,0^{n-1} \mapsto 1\,0^{n-1}$,
   $0\,(10)^k 1 0^a \mapsto (10)^k 11 0^a$ and $0\,(10)^k 11 0^a \mapsto (10)^{k+1} 1 0^a$. In Lean the inverse
   direction is proved by induction on the `StripeWord` of the image, inverting the rule bit by bit with left
   permutivity (`tail_of_Phi_stripe`). So images are stripe-related through a cut iff the rows end in words of $T_n$
   after a common black cell and agree to the left (`agree_above`, `black_above_cut`).
3. **The time-1 relation fixes the representative** (`rep_of_stripeRelated_one`). A tail $1\,0^{n-1}$ after a black
   cell is a time-1 move; a tail $0\,s$ is a time-0 cut one cell further right. Both give the same representative.
   At the cuts through cell 0 or cell $-1$ the condition that cell 0 agrees forces both rows into the same kind of
   tail, which reduces to equality or to a time-0 cut.
4. **Counting** (`boxRep_index`, `boxRep_fixed`, `boxRep_inj`). The representatives of the box are the odd rows and
   the rows with an empty right half whose left part does not end in $0\,1$; each is its own representative, and
   `boxRep` lists them without repetition.

The classes are explicit: a nonempty right half is joined exactly to the right halves with the same representative.
The class sizes (paper, not in Lean; `class_sizes` checks them on every box of width at most 13): for each left
part, $2^{B-1-k}$ classes of size $k$ for $k < B$ and one of size $B$ among the nonempty right halves; the empty right
half joins the class of size $B$ when the left part ends in $0\,1$. For the single black cell that class is its stripe
seeds $(10)^k1$, $(10)^k11$ ([SeedExtensions](../Seeds/SeedExtensions.md)).

## What the kit has

The kit defines the stripe relation and proves its soundness and its early-meeting property; it does not count its
classes. Completeness, that rows with equal center columns are always joined, is open in the kit and here. With this
identity it becomes the counting statement "the box has at least $2^{A+B} + 3 \cdot 2^{A-1}$ center columns". On
every box of width at most 18 that count of distinct column prefixes is reached by time 768 (computed), so on those
boxes the center column classes are exactly the classes of this relation.
