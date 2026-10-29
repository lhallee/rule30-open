---
title: The bridge to the official definitions
category: foundations
problems: [1, 2, 3]
status: proved
lean: Rule30Open.Foundations.Official
headline: [evolve_single_eq_cell, evolve_single_center]
kit: bridge
kit_modules: [Rule30Jen, Rule30Prize]
---

# The bridge to the official definitions

A theorem about the prize is only as good as its definitions. The prize kit fixes them:
`Rule30Jen.cell t p` is the pattern grown from a single black cell, `Rule30Prize.center t` is its center column, and
`Rule30Prize.Problem1` and `Rule30Prize.Problem2` are stated with them. This library has its own definitions,
`evolve` and `single`, because its arguments start from arbitrary rows. This module proves that they give the official
pattern, so a reader can check every headline result against the kit's statements without trusting this library's
definitions.

## Statement

- `evolve_single_eq_cell`: for every $t$, the row `evolve single t` is the row `Rule30Jen.cell t`.
- `evolve_single_center`: for every $t$, `evolve single t 0 = Rule30Prize.center t`.

## Argument

Both definitions are the same recursion on $t$. At $t = 0$ both rows are 1 at cell 0 and 0 elsewhere. At $t + 1$ both
apply Rule 30 to the three cells above each cell, and the kit's `Rule30Jen.rule` and this library's `rule30` agree on
all eight neighborhoods. So the rows agree at every $t$, by induction, comparing them position by position. The
center column is `cell t 0` by the kit's definition, which gives the second statement.

## In Lean

The induction step rewrites with the hypothesis for $t$ and closes by unfolding both definitions (`rfl`). Every module
that has a headline result about the center column restates it with `Rule30Prize.center` through
`evolve_single_center`, for example `center_not_eventually_constant` in
[AdjacentColumns.md](../Columns/AdjacentColumns.md).

## Relation to the kit

This module only connects the two vocabularies. The official statements live in the kit's
[`Rule30Prize`](https://github.com/WolframInstitute/Rule30PrizeKit/blob/932cf8dde039b89b1dcbe9636867bb1b2057fef0/lean/Ruliology/CellularAutomata/Rule30Prize.lean).
