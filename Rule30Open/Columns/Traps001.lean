module

public import Rule30Open.Columns.MissedTraps
public import Rule30Open.Columns.TrapPairs
public import Ruliology.CellularAutomata.Rule30EtherThreeTrap

/-!
# Two traps for `001`, and the kit's `AbsorptionT t001` is false

The kit reduces the word `001` to entry into its trap `t001` (`Rule30EtherThree.AbsorptionT`), 47 cells with labels
modulo 21, and states that entry as open. [WordTraps](WordTraps.md) has a second trap for `001`, `trap001fifteen`, 52
cells with labels modulo 15. Each is a set of windows that no move leaves, and no state of one, cut to the narrower
width, is a state of the other whose label reads the same phase. So a right half that starts in either one stays in
it and never enters the other: entry into each trap alone is false, the kit's among them. Entry into one of the two
still excludes `001`.

* `t001W`, `absorptionT_t001_iff`: the kit's trap with its own packed tables, read as a trap of WordTraps, and the
  kit's `AbsorptionT t001` as its `WTrap.Absorption`, by definition.
* `t001W_check`, `t001W_closed`, `trap001fifteen_closed`, `fifteen_apart_t001`, `t001_apart_fifteen`: the kernel's
  checks, the two traps and their separation in both directions.
* `not_absorptionT_t001`: the right half whose first 52 cells are state 0 of `trap001fifteen`, white beyond, driven
  from phase 0, never enters `t001`. `trap001fifteen_not_absorption`: the half of state 0 of `t001` never enters
  `trap001fifteen`.
* `traps001`, `traps001_excludes`: entry into one of the two excludes `001` as a tail of the center column.

The natural-language argument is `Traps001.md`, beside this file.
-/

@[expose] public section

-- Sequential elaboration: the kernel checks would otherwise run in parallel and stack their memory.
set_option Elab.async false

namespace Rule30Open

open Ruliology.CellularAutomata BitGame

/-- The kit's trap `t001` as a trap of WordTraps: the block `001`, 47 cells, labels modulo 21, and the kit's packed
tables of windows, labels and successors. -/
def t001W : WTrap :=
  { b := Rule30EtherThree.w001, K := 47, m := 21, n := Rule30EtherThree.t001_n, lb := Rule30EtherThree.t001_lb,
    ib := Rule30EtherThree.t001_ib, u := Rule30EtherThree.t001_u, R := Rule30EtherThree.t001_R,
    L := Rule30EtherThree.t001_L, S := Rule30EtherThree.t001_S }

/-- **The kit's statement is entry into `t001W`**, by definition. -/
theorem absorptionT_t001_iff : Rule30EtherThree.AbsorptionT Rule30EtherThree.t001 ↔ t001W.Absorption := Iff.rfl

theorem t001W_check : t001W.check = true := by decide +kernel

theorem t001W_closed : t001W.closedCheck = true := by decide +kernel

theorem trap001fifteen_closed : trap001fifteen.closedCheck = true := by decide +kernel

/-- No state of `trap001fifteen`, cut to 47 cells, is a state of `t001` whose label reads the same phase. -/
theorem fifteen_apart_t001 : trap001fifteen.apartWide t001W = true := by decide +kernel

/-- No state of `trap001fifteen`, cut to 47 cells, is a state of `t001` whose label reads the same phase: the same
separation in the form `not_absorption` takes, with `t001` the closed set. -/
theorem t001_apart_fifteen : t001W.apart trap001fifteen = true := by decide +kernel

/-- **The kit's `AbsorptionT t001` is false.** The right half whose first 52 cells are state 0 of `trap001fifteen`,
white beyond, driven by `001` from the phase of that state's label, keeps them in `trap001fifteen` and never has its
first 47 cells in a state of `t001`. -/
theorem not_absorptionT_t001 : ¬ Rule30EtherThree.AbsorptionT Rule30EtherThree.t001 := fun h =>
  not_absorption_wide t001W trap001fifteen trap001fifteen_closed rfl (by decide) fifteen_apart_t001 (by decide)
    (absorptionT_t001_iff.mp h)

/-- **Entry into `trap001fifteen` is false.** The right half whose first 47 cells are state 0 of `t001` never enters
it. -/
theorem trap001fifteen_not_absorption : ¬ trap001fifteen.Absorption :=
  not_absorption trap001fifteen t001W t001W_closed rfl (by decide) t001_apart_fifteen (by decide)

/-- The two traps for `001`. -/
def traps001 : List WTrap := [t001W, trap001fifteen]

/-- **`001` reduced to entry into one of the two traps.** -/
theorem traps001_excludes (hA : WTrap.AbsorptionSome traps001) :
    ¬ Rule30StripCertificates.EventuallyWord Rule30EtherThree.w001 := by
  refine absorption_some_excludes _ traps001 ?_ ?_ hA <;>
    simp only [traps001, List.mem_cons, List.not_mem_nil, or_false] <;> rintro C (rfl | rfl)
  · rfl
  · rfl
  · exact t001W_check
  · exact trap001fifteen_check

end Rule30Open
