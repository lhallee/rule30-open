---
title: A right half of B cells gives at most 2^(B-1) + 1 center columns to each left part
category: frames
problems: [1]
status: proved
lean: Rule30Open.Frames.StripeClasses
headline: [StripeClasses.right_half_center_columns, StripeClasses.box_center_columns, StripeClasses.right_half_columns, StripeClasses.box_columns, StripeClasses.center_eq_right_extension]
kit: refines
kit_modules: [Rule30StripeMeeting]
---

# A right half of B cells gives at most 2^(B-1) + 1 center columns to each left part

Fix the cells left of the center and fill the $B$ cells right of it in all $2^B$ ways. The center columns of these
rows take at most $2^{B-1} + 1$ values, and at most $2^{B-1}$ when cell $-1$ is white and cell $0$ black. So the rows
supported in $[-A, B]$ have at most $2^{A+B} + 3 \cdot 2^{A-1}$ center columns. The kit's stripe relation does all
the work: every row is one stripe step, at time 0 or at time 1, from a row whose cell $B$ is black.

## Statement

A row's *left part* is its restriction to the cells $\le 0$, its *right half* its restriction to the cells
$1, \dots, B$. The left part *ends in $0\,1$* when cell $-1$ is white and cell $0$ is black.

- `right_half_center_columns`: for every finite left part and $B \ge 1$, every nonempty right half, and the empty one
  when the left part ends in $0\,1$, gives the center column of a row with the same left part whose cell $B$ is black.
  Hence the $2^B$ rows with that left part have at most $2^{B-1} + 1$ center columns, and at most $2^{B-1}$ when the
  left part ends in $0\,1$.
- `box_center_columns`: for $A, B \ge 1$, every Rule 30 row supported in $[-A, B]$ has the center column of one of
  $2^{A+B} + 3 \cdot 2^{A-1}$ explicit rows `boxRep A B i`: the rows of the box whose cell $B$ is black, and the rows
  whose right half is empty and whose left part does not end in $0\,1$.
- `right_half_columns`, `box_columns`: the same in the kit's frame.
- `center_eq_right_extension`: the official form. The prize's column is the center column of the single black cell
  followed by a right half inside $[1, B]$ whose cell $B$ is black; [SeedExtensions](../Seeds/SeedExtensions.md) names
  these rows, $(10)^k1$ and $(10)^k11$.

## Argument

Work in the kit's frame with center index $B$ (`Rule30StripeMeeting`): a row white right of $B$ is the number whose
bit $k$ is cell $B - k$, one step is $\Phi(a) = a \oplus ((a \ll 1) \lor (a \ll 2))$, and the center cell at time $t$
is bit $B + t$ of $\Phi^t(a)$ (`evolve_eq_phiRows` checks the frame against `evolve`). The kit's `StripeRelated a b c`
lets two rows exchange their bits $0, \dots, j$ ($j \le c$) when both blocks are stripe words $0^a 1 (01)^k$ or
$0^a 11 (01)^k$ (read from bit 0), bit $j + 1$ is white in both and the rows agree above; its theorem
`stripe_related_same_trace` says such rows have the same center column.

1. **Time one** (`column_eq_of_stripe_one`). If two rows have the same cell 0 and their images under $\Phi$ are
   stripe-related at center index $B + 1$, the kit's theorem applied to the images gives equal center cells at every
   time $t \ge 1$.
2. **The two moves.** Let a row with a nonempty right half be $x = 2^{m+1} H + 2^m$, so bit $m \ge 1$ (cell $B - m$)
   is its last black cell. Let $W_n$ (`stripeLow n`) be the stripe word of length $n$ whose bit 0 is black: bit
   $i < n$ is black iff $i = 0$ or $i + n$ is odd.
   - If the cell before it is white ($H$ even) and $m \le B$: $0^m 1$ and $W_{m+1}$ are stripe words of the same
     length, so $x$ and $2^{m+1} H + W_{m+1}$ are stripe-related at time 0 with cut $j = m$ (`time_zero_move`).
   - If the cell before it is black ($H$ odd) and $m < B$: let $y = 2^{m+1} H + W_m$ (bit $m$ white). Bits
     $0, \dots, m$ of $\Phi(x)$ read $0^m 1$, those of $\Phi(y)$ read $W_{m+1}$, bit $m + 1$ is white in both images,
     and above it the images agree because bit $m + 1$ is black in both rows. So the images are stripe-related with
     cut $j = m$, and cell 0 agrees (`time_one_move`). This is the identity "one step of Rule 30 takes the cells
     $0\,s^*_m$ to $s^*_{m+1}$", read in bits.
3. **Representatives** (`exists_odd_rep`). The last black cell of a nonempty right half has $m < B$; an empty right
   half with a left part ending in $0\,1$ has $m = B$ and a white cell before it. Either way one move reaches a row
   with bit 0 (cell $B$) black and the same left part.
4. **Counting** (`right_half_columns`, `box_columns`). The rows with left part $\lambda$ and cell $B$ black are
   $2^B \lambda + 2i + 1$, $i < 2^{B-1}$. In the box, $\lambda < 2^{A+1}$; the odd rows number $2^{A+B}$, and the left
   parts not ending in $0\,1$ are $4q + r$ with $r \in \{0, 2, 3\}$ and $q < 2^{A-1}$: $3 \cdot 2^{A-1}$ more rows.

## In Lean

`column B x t` is `(phiRows x t).testBit (B + t)`. The moves are proved bit by bit from the kit's `Phi_testBit`, with
`StripeWord` built from its three constructors (`stripeWord_stripeLow`, `stripeWord_single_bit`). `rowOf B a` is the
row whose cell $B - j$ is bit $j$ of $a$ and `rowNat` encodes a row of the box as a number; `evolve_eq_phiRows` proves
the frame, so the headline results hold for `evolve`. `center_eq_right_extension` uses `evolve_single_center`.

## What the kit has

The kit proves that stripe-related rows have the same center column (`stripe_related_same_trace`), that a stripe
relation reached later with agreeing observations was already there at time 0 or 1 (`stripe_meeting_is_early`), and
that every stripe seed $1, 11, 101, 1011, \dots$ has the single cell's column (`TransformsSeeds`). It does not count
classes of rows or bound the number of center columns. [StripeClassCount](StripeClassCount.md) proves that the bound
is exactly the number of classes of the stripe relation at time 0 or 1, so the stripe relation can do no better; that
rows in different classes have different center columns (which would make the bound exact, and which by the edge
argument implies Problem 1) is open.
