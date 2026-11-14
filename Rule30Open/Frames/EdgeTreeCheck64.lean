module

public import Rule30Open.Frames.EdgeTreeCheck

/-!
# The codes of period 64 of the right-edge map are the rain codes

* `period_64`: **a code with bit 0 black and `iter 64 c = c` is `rainA` or `rainB`**, from
  `EdgeTree.rain_or_branch`, `EdgeTreeCheck.dead_sound` and a kernel evaluation of the list checker
  `EdgeTreeCheck.dead` at the two branch states of length 64 (`dead_false_64`, `dead_true_64`).
* `rain_of_return_128`: **a row white right of a black cell `r` that returns after `L` steps moved `L` cells right,
  with `L % 128 ≠ 0`, has the code `rainA` or `rainB` at `r`.**

The natural-language argument is `EdgeTreeCheck64.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open.Frames.EdgeTreeCheck64

open Rule30Open.Frames.EdgeTree
open Rule30Open.Frames.EdgeTreeCheck
open Ruliology.CellularAutomata.Rule30FrozenRuler (iter)

theorem dead_false_64 : dead 106 (altList false 64) (altList false 64) = true := by decide +kernel

theorem dead_true_64 : dead 106 (altList true 64) (altList true 64) = true := by decide +kernel

theorem period_64 (c : Nat → Bool) (h0 : c 0 = true) (hp : iter 64 c = c) :
    c = Rule30Open.Frames.EdgePeriodFour.rainA ∨ c = Rule30Open.Frames.EdgePeriodFour.rainB := by
  rcases rain_or_branch c h0 with hr | ⟨j, _, ha, he⟩
  · exact hr
  · exfalso
    apply dead_sound c 64 hp 106 j
    rw [he, seg_alt _ ha]
    cases col c j 0
    · exact dead_false_64
    · exact dead_true_64

theorem rain_of_return_128 (init : Int → Bool) (r : Int) (hr : ∀ p, r < p → init p = false)
    (h0 : init r = true) (L : Nat) (hL : L % 128 ≠ 0)
    (h : ∀ x, evolve init L (x + (L : Int)) = init x) :
    LightReturnRows.codeAt init r = Rule30Open.Frames.EdgePeriodFour.rainA ∨
      LightReturnRows.codeAt init r = Rule30Open.Frames.EdgePeriodFour.rainB := by
  have fac : ∃ a q : Nat, a ≤ 6 ∧ q % 2 = 1 ∧ L = 2 ^ a * q := by
    by_cases h6 : L % 64 = 0
    · exact ⟨6, L / 64, by omega, by omega, by show L = 64 * (L / 64); omega⟩
    by_cases h5 : L % 32 = 0
    · exact ⟨5, L / 32, by omega, by omega, by show L = 32 * (L / 32); omega⟩
    · obtain ⟨a, q, ha, hq, e⟩ := LightReturnClassified.factor_of_mod L h5
      exact ⟨a, q, by omega, hq, e⟩
  obtain ⟨a, q, ha, hq, rfl⟩ := fac
  have hp := LightReturnRows.pow_two_return init r hr a q hq h
  have hi := LightReturnRows.iter_code_of_return init r hr (2 ^ a) hp
  have e64 : 2 ^ a * 2 ^ (6 - a) = 64 := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' ha]
  have h64 := LightReturnClassified.iter_mul_of (LightReturnRows.codeAt init r) (2 ^ a) hi (2 ^ (6 - a))
  rw [e64] at h64
  have hc0 : LightReturnRows.codeAt init r 0 = true := by
    show init (r - ((0 : Nat) : Int)) = true
    simpa using h0
  exact period_64 _ hc0 h64

end Rule30Open.Frames.EdgeTreeCheck64
