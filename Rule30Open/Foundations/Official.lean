module

public import Rule30Open.Foundations.Evolve
public import Ruliology.CellularAutomata.Rule30Prize

/-!
# The official statements

The Rule 30 Prize kit fixes the official definitions: `Rule30Jen.cell t p` is the pattern from a single
black cell, `Rule30Prize.center` its center column, and `Rule30Prize.Problem1`, `Rule30Prize.Problem2`
the prize problems. This module proves that `evolve single` is `Rule30Jen.cell`, so every theorem of
this library about `evolve single` is a theorem about the official pattern, and the modules restate
their headline results with `Rule30Prize.center`.

The natural-language argument is `Official.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata

/-- Rule 30 from the single seed is the kit's pattern, row by row. -/
theorem evolve_single_eq_cell : ∀ t : Nat, evolve single t = Rule30Jen.cell t
  | 0 => by
    funext p
    rfl
  | t + 1 => by
    funext p
    show rule30 (evolve single t (p - 1)) (evolve single t p) (evolve single t (p + 1)) = Rule30Jen.cell (t + 1) p
    rw [evolve_single_eq_cell t]
    rfl

/-- The single seed's center column is the official one. -/
theorem evolve_single_center (t : Nat) : evolve single t 0 = Rule30Prize.center t := by
  rw [evolve_single_eq_cell]
  rfl

end Rule30Open
