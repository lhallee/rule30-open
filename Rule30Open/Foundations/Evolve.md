---
title: Rule 30 from any row, and its one-step facts
category: foundations
problems: [1, 2, 3]
status: proved
lean: Rule30Open.Foundations.Evolve
headline: [left_cell, left_edge, left_of_one, left_of_alternating]
kit: refines
kit_modules: [Rule30Jen]
---

# Rule 30 from any row, and its one-step facts

The prize asks about one pattern, the orbit of a single black cell. Most arguments here are cleaner for an arbitrary
starting row, so the library defines Rule 30 from any row and specializes to the single cell at the end. This module
holds that definition and four facts about one step of the rule that every later module uses.

## Statement

Write $a_t(x)$ for cell $x$ at time $t$, with 1 for black and 0 for white. Rule 30 is

$$a_{t+1}(x) = a_t(x-1) \oplus \bigl(a_t(x) \lor a_t(x+1)\bigr).$$

For every starting row, every cell $x$, column $k$ and time $t$:

1. **Left permutivity** (`left_cell`): $a_t(x-1) = a_{t+1}(x) \oplus \bigl(a_t(x) \lor a_t(x+1)\bigr)$.
2. **The left edge** (`left_edge`): if the row is 1 at $m$ and 0 left of $m$, then at time $t$ it is 1 at $m - t$
   and 0 left of $m - t$.
3. **Left of a 1** (`left_of_one`): if $a_t(k) = 1$, then $a_t(k-1) = \lnot a_{t+1}(k)$.
4. **Left of a 1 then 0** (`left_of_alternating`): if $a_t(k) = 1$ and $a_{t+1}(k) = 0$, then $a_t(k-1) = 1$.

## Argument

1. XOR both sides of the rule at cell $x$ with $a_t(x) \lor a_t(x+1)$. The value is cancelled on the right and
   moves to the left side.
2. By induction on $t$. Every cell left of $m - t - 1$ sees three cells left of $m - t$, all 0, and
   $0 \oplus (0 \lor 0) = 0$. Cell $m - t - 1$ sees $0$, $0$ and the 1 at $m - t$, and $0 \oplus (0 \lor 1) = 1$.
3. When $a_t(k) = 1$ the OR in the update of cell $k$ is 1 whatever its right neighbor holds, so
   $a_{t+1}(k) = a_t(k-1) \oplus 1$.
4. Statement 3 with $a_{t+1}(k) = 0$.

Statement 1 is why a column can be rebuilt from the two columns to its right, which drives the adjacent-column
theorem. Statement 2 says that a row with a leftmost 1, a finite row in particular, keeps one, moving left at speed 1.
Statements 3 and 4 are the facts the period-two reduction runs on.

## In Lean

`rule30` is the rule, `evolve init t x` is $a_t(x)$ from the row `init`, `single` is the single black cell at 0, and
`leftOf init t k j` is the cell $j + 1$ places left of column $k$. Spot checks tie the definitions to independent
data: `rule30` is Wolfram's code 30, and the single cell's center column begins 1 1 0 1 1 1 0 0 1 1, as
[OEIS A051023](https://oeis.org/A051023) does. Each statement above is one theorem, proved by case analysis on the
cells involved and, for the edge, induction on $t$.

## Relation to the kit

The kit's
[`Rule30Jen`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/7d665044b904117af9e82328aeb90a30692b2b85/lean/Ruliology/CellularAutomata/Rule30Jen.lean)
defines Rule 30 for the single black cell only and uses left permutivity inside its proof of Jen's theorem. This
module states the same one-step facts for every starting row. [Official.md](Official.md) proves that the two
definitions agree on the single cell.
