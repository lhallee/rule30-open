---
title: Four traps for 001, pairwise apart, so the kit's AbsorptionT t001 is false and so is entry into one of any three
category: columns
problems: [1]
status: proved
lean: Rule30Open.Columns.Traps001
headline: [not_absorptionT_t001, traps001_pair_not_absorption, t001W_not_absorption_some, traps001_excludes, absorption_any_excludes]
kit: new
kit_modules: [Rule30EtherThreeTrap, Rule30EtherThree]
evidence: [computations/lock_chain.py, computations/period_three.py]
---

# Four traps for 001, pairwise apart, so the kit's AbsorptionT t001 is false and so is entry into one of any three

The kit reduces the word $001$ of least period three to entry into its trap `t001`: 815 states of the first 47 cells
beside the center, with labels modulo 21, closed under both values of cell 48. If every finitely supported right half
driven by $001$, from any phase, enters `t001` (`AbsorptionT t001`), the center column is not eventually $001$
repeated; the kit states the entry as open, with every one of 18,258 tested halves entering. There are other traps for
$001$, sets of windows that no move leaves, with the cell beside the center a function of the label at the white
phases. Four of them are pairwise apart: no state of one, cut to the width of another, is a state of the other whose
label reads the same phase.

| trap | cells | labels modulo | states | where it comes from |
|---|---|---|---|---|
| `t001` | 47 | 21 | 815 | the kit; the lock of $0^5\,1\,0\,1^{12}\,0\,1$ carried 38 cells |
| `trap001fifteen` | 52 | 15 | 153 | [WordTraps](WordTraps.md); the lock of $0^4\,1\,0\,1^9$ carried 47 cells |
| `trap001b` | 144 | 21 | 879 | the lock of 9 cells of $0\,1\,0\,1^{14}\,0\,1^3$ carried 135 cells |
| `trap001c` | 304 | 21 | 258 | the lock of 5 cells of $0^6\,1\,0\,1^3\,0\,1^9$ carried 299 cells |

A right half that starts in one of them stays in it whatever the cells beyond do, so it never enters another. Entry
into any one of them alone is false, the kit's `AbsorptionT t001` among them, and so is entry into one of any three.

## Statement

1. **The kit's statement is false** (`not_absorptionT_t001`): $\lnot\,$`Rule30EtherThree.AbsorptionT t001`, the
   kit's own proposition about its own trap. The right half whose cells 1 to 52 are
   $$0101000110001001110111111110101000000111010011010000,$$
   cell 1 first, state 0 of `trap001fifteen` with label 0, white from cell 49 on, driven by $001$ from phase 0, never
   has its cells 1 to 47 in a state of `t001` whose label reads the drive's phase.
2. **Entry into one of any three is false** (`t001W_not_absorption_some`, `trap001fifteen_not_absorption_some`,
   `trap001b_not_absorption_some`, `trap001c_not_absorption_some`): for each of the four traps, the right half of its
   state 0, white beyond, driven from the phase of that state's label, enters none of the other three. In particular
   entry into `t001` or `trap001fifteen` is false (`traps001_pair_not_absorption`), and so is entry into
   `trap001fifteen` alone (`trap001fifteen_not_absorption`).
3. **A closed set refutes entry into one of a list** (`never_enters_fwd`, `not_absorption_some_fwd`). If $S$ is a set
   of windows that no move leaves and, for each trap $C$ of a list, a set of windows no wider than either holds the
   states of $C$ cut to it and no state of $S$, so cut, is in it at a label of the same phase, then the right half of
   state 0 of $S$ never enters any trap of the list.
4. **The reductions that remain** (`traps001_excludes`, `absorption_any_excludes`,
   `not_eventually_001_of_absorption_any`). If every finitely supported right half driven by $001$, from any phase,
   enters one of the four traps (`WTrap.AbsorptionSome traps001`), or enters some trap of $001$ that passes the check
   of WordTraps (`WTrap.AbsorptionAny`), the center column does not eventually repeat $001$. The second holds for any
   block in place of $001$.

## Argument

`t001W` is the kit's trap with the kit's packed tables, written as a trap of WordTraps; the kit's `AbsorptionT t001`
is `t001W.Absorption` by definition (`absorptionT_t001_iff`, `Iff.rfl`). For item 1 the kernel checks that
`trap001fifteen` is closed (`WTrap.closedCheck` of [MissedTraps](MissedTraps.md)) and that none of its states, cut to
its first 47 cells, is a state of `t001` whose label is congruent to it modulo 3, the drive's phase
(`fifteen_apart_t001`), 124,695 comparisons. A half that starts in `trap001fifteen` keeps its first 52 cells in it at
every step, the label advancing with the phase, so its first 47 cells are never a state of `t001` with the right
label; that is `not_absorption_wide` of MissedTraps.

For item 2, `not_absorption_some_fwd` runs the same argument for a list of traps. For each trap $C$ of the list, the
states of $C$ cut to the narrower of the two widths are written as a set of windows by label (`cert_<S>_<C>`, a
`WinSet` of [ReachRefuted](ReachRefuted.md)); the kernel checks that it holds every state of $C$ so cut (`_holds`) and
that no state of $S$, so cut, is in it at a label of the same phase (`_avoids`). The half of state 0 of $S$ stays in
$S$, and entry into $C$ at some step would put its first cells, cut to that width, into the set at the right label,
against `_avoids`; `never_enters_fwd` is that step for one half and one trap. The reductions are
`absorption_some_excludes` of [TrapPairs](TrapPairs.md) with all four traps checked, and, for `AbsorptionAny`, the
same step with the trap that entry provides (`entry_excludes`).

The separation is forced where the labels' moduli differ: on each trap the cell beside the center at the white phases
is a function of the label, with period 21 on `t001` and 15 on `trap001fifteen`, so on a common orbit it would repeat
with period 3, which the kit's function for `t001` does not. The three traps with labels modulo 21 have their walls at
different distances from the center.

The new traps come from the chains of [lock chains](../../findings/columns/lock-chains.md): a block whose column has a
locked window, carried leftward cell by cell through the columns the rule determines, until a column repeats $001$
(`scan001` in [computations/lock_chain.py](../../computations/lock_chain.py)). Over the blocks made of a run of at least
nine 1s and at most 12 other cells, of periods 15 to 33, with a locked window of 5 cells, and those with at most 15
other cells, of periods 15 to 24, with one of 9 cells, the chains reach $001$ from seven seeds: those of the four traps
and three more, which give traps of 359, 365 and 392 cells with labels modulo 21. None of these three has a part that no
move leaves apart from `trap001c` (`apart_closed`), so they do not refute entry into one of the four.

## What it means

The kit's route for $001$ needs more than one trap, and more than three. Small halves enter `t001`: every one of at most
ten cells, from each phase ([the census for 001](../../findings/columns/t001-census.md)), at the rate a fair coin beyond
the trap predicts, so none of them starts in another trap; the test of reach for `t001` passes in every game up to 26
cells ([reach of the kit's conjectures](../../findings/columns/kit-absorption-reach.md)), games too narrow to hold any
of the other three. Entry into one of the four traps is open, and a fifth trap apart from all four would refute it in
turn; the chains of other seeds may hold one. Entry into some trap of $001$, which no further trap can refute, is the
statement this route can rest on, and the weaker `Lock` that the kit's pull request #65 proposes follows from it ([the
kit's pull requests](../../literature/kit-pull-requests.md)).

## Relation to the kit

`Rule30EtherThreeTrap` defines `t001`, `AbsorptionT` and `not_eventually_001_of_absorption`, and calls the entry open.
This module refutes it with the kit's own definitions, refutes entry into one of any three of four traps, and proposes
entry into some trap in its place.

## Lean

`Rule30Open.Columns.Traps001`: `t001W`, `absorptionT_t001_iff`, the checks `t001W_check`, `t001W_closed`,
`trap001fifteen_closed`, `fifteen_apart_t001` and `t001_apart_fifteen`, the refutations `not_absorptionT_t001` and
`trap001fifteen_not_absorption`; `never_enters_fwd`, `not_absorption_some_fwd` and `WTrap.AbsorptionSome.mono`;
`trap001b` and `trap001c` with `_check` and `_closed`, the twelve sets `cert_<S>_<C>` with `_holds` and `_avoids`, the
four refutations `<S>_not_absorption_some` and `traps001_pair_not_absorption`; and `traps001`, `traps001_excludes`,
`WTrap.AbsorptionAny`, `absorption_any_excludes` and `not_eventually_001_of_absorption_any`. It builds in under two
minutes.

## Reproduce

```bash
python -m computations.lock_chain --scan001
```

```bash
python -m computations.lock_chain --lean-traps001
```

The scan of seeds whose chains reach $001$ takes about 11 minutes; the tables of `trap001b`, `trap001c` and the
twelve sets take a second. `test_traps001` checks that the four traps are pairwise apart and closed by the rule on
whole windows, that a half started in each, stepped under Rule 30 itself, stays in it and out of the other three, and
that the generated declarations are those of the module.
