---
title: An alternating left half fixes the center cell whatever the right half is
category: complexity
problems: [3]
status: proved
lean: Rule30Open.Complexity.ConeScreening
headline: [screening_odd, screening_even, stripe, pair_back, evo_local, front_xor, flip_center, center_decomp, decomp_local, four_words]
kit: refines
kit_modules: [Rule30ZeroBoundaryStripe]
---

# An alternating left half fixes the center cell whatever the right half is

A row is a map from the integers to colors, and one step of Rule 30 is $x'_j = x_{j-1} \oplus (x_j \lor x_{j+1})$.

## Statement

- `screening_odd`: if $x_{-j} = 1$ exactly for odd $j$, $1 \le j \le t$, and $t \ge 9$, the center after $t$ steps is
  white, for every other cell of the row.
- `screening_even`: if $x_{-j} = 1$ exactly for even $j$, $1 \le j \le t$, and $t \ge 8$, the center after $t$ steps is
  black, for every other cell of the row.
- `flip_center`: flipping cell $-t$ of any row flips the center after $t$ steps; `center_decomp`: the center after $t$
  steps is $x_{-t} \oplus g$, with $g$ a function of the cells $-t + 1, \ldots, t$ alone (`decomp_local`).
- `four_words`: for $t \ge 9$ the odd and even left halves, each also with cell $-t$ flipped, force the center to the
  two constants: white for the odd half and for the even half flipped, black for the even half and for the odd half
  flipped.

## Argument

The argument is the proof of [cone screening](../../findings/complexity/cone-screening.md). After $s \le t$ steps the
cells $-1, \ldots, -(t - s)$ still alternate, whatever lies right of the black end (`stripe`): a black cell between two
whites gives $0 \oplus 1 = 1$ and a white cell between two blacks gives $1 \oplus 1 = 0$. Next to that wall, the pair
$(a, b)$ of the two cells right of it follows $a' = \lnot(a \lor b)$, so a white pair at time $s + 2$ forces a white
pair at time $s$ (`pair_back`). For the odd pattern the center is $a$, so it is white at $t$ exactly when the pair at
$t - 1$ is not white, and the checks $c_9 = c_{10} = 0$ exclude a white pair at times 8 and 9, hence at every later
time before $t$. The even pattern is the odd one shifted by a cell (`evo_shift`), with the center the cell $b$, and the
checks $c_8 = c_9 = 1$ exclude a white pair at times 7 and 8. The base values are checked by `decide` over every right
half, $2^9$ to $2^{11}$ of them, on rows encoded as natural numbers (`base_of_check`), and `evo_local` carries them from
the cone to any row. If two rows agree right of cell $a$, their cells $a + s$ after $s$ steps differ by $x_a \oplus
y_a$ (`front_xor`), since the cells right of $a + s$ agree at every time by the cone; with $a = -t$ this gives
`flip_center`.

## What it means

This is a statement about all rows, not the single black cell. Since the four words of `four_words` are distinct and
give only two functions, the $2^t$ left halves of the cone give at most $2^t - 2$ functions of the right half for
$t \ge 9$ (a counting consequence, not a Lean statement), so a lower bound for Problem 3 cannot come from all left
halves being distinguishable.

The kit has the stripe as a fixed point in its zero boundary setting (`Rule30ZeroBoundaryStripe.stripe_confined`), and
its equivalent forms have `flip_center` and `center_decomp` for its own row type
(`Rule30Equivalents.Genericity.evol_flip`, `Rule30Equivalents.AlgebraicDegree.evol_update_left`); they are restated
here for this module's rows. The screening of the center is new.
