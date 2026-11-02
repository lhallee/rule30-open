module

public import Rule30Open.Columns.ThreeRuns
public import Rule30Open.Foundations.Official
public import Ruliology.CellularAutomata.Rule30EtherThreeSkeleton

/-!
# For `001`, the kit's left-half statement with the free bits constrained by the right half

The kit reduces a center column that repeats `001` to `Rule30EtherThree.C3s001`: no finitely supported left half,
run with the white boundary, keeps column `-1` equal to `(0, *, 1)` at the phases `(0, 1, 2)` for all large times.
At phase 1 column `-1` is the complement of column `1` (`Rule30EtherThree.col_m1_001`), and `ThreeRuns` keeps
column `1` there free of `010`, `101` and `1001`. So the left half only has to fail for free bits whose complements
avoid those words: runs of 0s of length at least 2 and runs of 1s of length at least 3.

* `C3r001`: the left-only statement with the free bits constrained. It is weaker than the kit's `C3s001`
  (`c3r_of_c3s`), and it is open.
* `not_eventually_001_of_C3r`: `C3r001` excludes `001^∞` as a tail of the center column, for every transient;
  `center_not_eventually_001_of_C3r` is the official form with `Rule30Prize.center`.

The natural-language argument is `ConstrainedLeft001.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open

open Ruliology.CellularAutomata Rule30EtherThree Rule30DrivenLeft ThreeRuns

/-- **`C3r001`** (open). No finitely supported left half of the zero-boundary left half keeps column `-1` equal to
`(0, *, 1)` (phases `0, 1, 2`) for all large times with the complements of its free bits, the values at the steps
`3 i + 1`, eventually free of `010`, `101` and `1001`. -/
def C3r001 : Prop :=
  ∀ s : Int → Bool, (∃ M : Nat, ∀ p : Int, p < -(M : Int) → s p = false) →
    ¬ ∃ K, (∀ k, K ≤ k → fits3 colPattern001s (k % 3) (L (fun _ => false) s k (-1)) = true) ∧
      ∃ i0, NoShortRuns (fun i => !L (fun _ => false) s (3 * i + 1) (-1)) i0

/-- The kit's `C3s001` implies `C3r001`: the constrained statement asks less. -/
theorem c3r_of_c3s (h : C3s001) : C3r001 := by
  intro s hs ⟨K, hK, _⟩
  exact h s hs ⟨K, hK⟩

/-- **`C3r001` excludes `001^∞`** as a tail of the center column, for every transient. -/
theorem not_eventually_001_of_C3r (hC : C3r001) :
    ¬ ∃ T, ∀ t, T ≤ t → Rule30Jen.cell t 0 = wordAt3 w001 (t - T) := by
  rintro ⟨T, hT⟩
  obtain ⟨T', hT', hs⟩ := col_m1_001_skeleton T hT
  have hfun : (fun k => Rule30Prize.center (T + k) && Rule30Prize.center (T + k + 1)) = fun _ => false := by
    funext k
    show (Rule30Jen.cell (T + k) 0 && Rule30Jen.cell (T + k + 1) 0) = false
    rw [hT (T + k) (by omega), hT (T + k + 1) (by omega), wordAt3_001, wordAt3_001,
      show T + k - T = k by omega, show T + k + 1 - T = k + 1 by omega]
    have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases this with h | h | h
    · rw [h, show (k + 1) % 3 = 1 by omega]; rfl
    · rw [h, show (k + 1) % 3 = 2 by omega]; rfl
    · rw [h, show (k + 1) % 3 = 0 by omega]; rfl
  have hL : ∀ k, L (fun _ => false) (fun p => Rule30Jen.cell T p) k (-1) = Rule30Jen.cell (T + k) (-1) := by
    intro k
    have e := cell_eq_L_effective T k (-1) (by omega)
    rw [hfun] at e
    exact e
  have hrow : ∀ t, T ≤ t → evolve single t 0 = wordAt3 w001 (t - T) := by
    intro t ht
    rw [evolve_single_eq_cell]
    exact hT t ht
  refine hC (fun p => Rule30Jen.cell T p) ⟨T, fun p hp => Rule30Jen.cell_eq_false_of_lt T p hp⟩
    ⟨T' - T, fun k hk => ?_, 14, ?_⟩
  · rw [hL, fits3_001s]
    obtain ⟨s0, -, s2⟩ := hs (T + k) (by omega)
    have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases this with h | h | h
    · rw [ite_eq_left h, s0 (by omega)]; rfl
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_left h, s2 (by omega)]; rfl
  · have e : (fun i => !L (fun _ => false) (fun p => Rule30Jen.cell T p) (3 * i + 1) (-1)) =
        fun i => evolve single (T + 3 * i + 1) 1 := by
      funext i
      rw [hL, (col_m1_001 T hT (T + (3 * i + 1)) (by omega)).2.1 (by omega), Bool.not_not,
        evolve_single_eq_cell, show T + 3 * i + 1 = T + (3 * i + 1) by omega]
    rw [e]
    exact three_runs_evolve single T hrow

/-- **The official form.** If `C3r001` holds, the official center column does not repeat `001` from any time on. -/
theorem center_not_eventually_001_of_C3r (hC : C3r001) :
    ¬ ∃ T, ∀ t, T ≤ t → Rule30Prize.center t = wordAt3 w001 (t - T) := by
  rintro ⟨T, hT⟩
  refine not_eventually_001_of_C3r hC ⟨T, fun t ht => ?_⟩
  have := hT t ht
  rw [← evolve_single_center, evolve_single_eq_cell] at this
  exact this

end Rule30Open
