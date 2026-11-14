module

public import Rule30Open.Frames.LightReturnRows
public import Rule30Open.Frames.EdgePeriodSixteen

/-!
# The rows that come back at the speed of light after a time not divisible by 32

* `rain_of_return`: **a row white right of a black cell `r` that returns after `2 ^ a * q` steps moved
  `2 ^ a * q` cells right, with `q` odd and `a ≤ 4`, has the edge code `rainA` or `rainB` at `r`.** By
  `LightReturnRows.pow_two_return` it returns after `2 ^ a` steps, hence after 16, and
  `EdgePeriodSixteen.period_sixteen_iff` reads off the code.
* `frozen_T_eq`: the kit's edge map `Rule30FrozenRuler.T` is the map `EdgePeriodFour.T` restated there.

The natural-language argument is `LightReturnClassified.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open.Frames.LightReturnClassified

open Rule30Open
open Rule30Open.Frames.LightReturnRows
open Ruliology.CellularAutomata.Rule30FrozenRuler (iter iter_add)

theorem frozen_T_eq : Ruliology.CellularAutomata.Rule30FrozenRuler.T = Rule30Open.Frames.EdgePeriodFour.T := by
  funext c k
  match k with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

theorem iter_mul_of (c : Nat → Bool) (p : Nat) (h : iter p c = c) : ∀ m, iter (p * m) c = c := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Nat.mul_succ, iter_add c (p * m) p, ih, h]

theorem rain_of_return (init : Int → Bool) (r : Int) (hr : ∀ p, r < p → init p = false) (h0 : init r = true)
    (a q : Nat) (hq : q % 2 = 1) (ha : a ≤ 4)
    (h : ∀ x, evolve init (2 ^ a * q) (x + ((2 ^ a * q : Nat) : Int)) = init x) :
    codeAt init r = Rule30Open.Frames.EdgePeriodFour.rainA ∨
      codeAt init r = Rule30Open.Frames.EdgePeriodFour.rainB := by
  have hp := pow_two_return init r hr a q hq h
  have hi := iter_code_of_return init r hr (2 ^ a) hp
  have e16 : 2 ^ a * 2 ^ (4 - a) = 16 := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' ha]
  have h16 := iter_mul_of (codeAt init r) (2 ^ a) hi (2 ^ (4 - a))
  rw [e16] at h16
  have hc0 : codeAt init r 0 = true := by
    show init (r - ((0 : Nat) : Int)) = true
    simpa using h0
  apply (Rule30Open.Frames.EdgePeriodSixteen.period_sixteen_iff (codeAt init r) hc0).1
  rw [← frozen_T_eq]
  exact h16

end Rule30Open.Frames.LightReturnClassified
