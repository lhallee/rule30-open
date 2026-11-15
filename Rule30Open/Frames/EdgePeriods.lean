module

public import Rule30Open.Frames.EdgeOddPeriods
public import Rule30Open.Frames.EdgePeriodEight
public import Rule30Open.Frames.EdgePeriodSixteen

/-!
# The odd edge codes of every period not divisible by 32

On the kit's edge map `Rule30FrozenRuler.T` (rule 30 read from the right edge, the 2-adic map
`Φ(y) = y ⊕ (2y ∨ 4y)`) and its iterate `Rule30FrozenRuler.iter`:

* `period_iff`: **for an edge code `c` with bit `0` black and a period `L = 2^a * q`, `q` odd, `a ≤ 4`,
  `iter L c = c` holds exactly when `L` is even and `c` is `rainA` (`-1/3`) or `rainB` (`1/3`).** Every `L ≥ 1`
  not divisible by 32 has this form. So no row white to the right of its edge cell, other than the rain rows,
  comes back after `L` steps moved `L` cells to the right, for any such `L`.

The proof reduces to the period `2^a` (`EdgeOddPeriods.pow_two_period`), excludes `a = 0` by
`EdgeOddPeriods.fixed_point_eq_zero`, and takes `a = 1, 2` from `EdgePeriodFour.period_four_iff`, `a = 3` from
`EdgePeriodEight.period_eight_iff` and `a = 4` from `EdgePeriodSixteen.period_sixteen_iff`, whose map `T` is the
kit's (`T_eq`).
-/

@[expose] public section

namespace Rule30Open.Frames.EdgePeriods

/-- The edge map restated in `EdgePeriodFour` is the kit's. -/
theorem T_eq : Ruliology.CellularAutomata.Rule30FrozenRuler.T = Rule30Open.Frames.EdgePeriodFour.T := by
  funext c k
  match k with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

open Ruliology.CellularAutomata.Rule30FrozenRuler

theorem iter_add (m n : Nat) (c : Nat → Bool) : iter (m + n) c = iter m (iter n c) := by
  induction m with
  | zero => simp [iter]
  | succ m ih => rw [show m + 1 + n = (m + n) + 1 by omega]; simp only [iter, ih]

theorem iter_mul_of_period (p : Nat) (c : Nat → Bool) (h : iter p c = c) : ∀ m, iter (p * m) c = c
  | 0 => by simp [iter]
  | m + 1 => by rw [Nat.mul_succ, Nat.add_comm, iter_add, iter_mul_of_period p c h m, h]

theorem rain_two (c : Nat → Bool)
    (hc : c = Rule30Open.Frames.EdgePeriodFour.rainA ∨ c = Rule30Open.Frames.EdgePeriodFour.rainB) :
    iter 2 c = c := by
  show T (T c) = c
  rw [T_eq]
  rcases hc with rfl | rfl
  · rw [Rule30Open.Frames.EdgePeriodFour.T_rainA, Rule30Open.Frames.EdgePeriodFour.T_rainB]
  · rw [Rule30Open.Frames.EdgePeriodFour.T_rainB, Rule30Open.Frames.EdgePeriodFour.T_rainA]

/-- **The odd edge codes of every period `2^a * q`, `q` odd, `a ≤ 4`.** -/
theorem period_iff (c : Nat → Bool) (h0 : c 0 = true) (a q : Nat) (hq : q % 2 = 1) (ha : a ≤ 4) :
    iter (2 ^ a * q) c = c ↔
      (1 ≤ a ∧ (c = Rule30Open.Frames.EdgePeriodFour.rainA ∨ c = Rule30Open.Frames.EdgePeriodFour.rainB)) := by
  constructor
  · intro h
    have hp := Rule30Open.Frames.EdgeOddPeriods.pow_two_period c a q hq h
    have h4of2 : iter 2 c = c → iter 4 c = c := fun h2 => by
      rw [show 4 = 2 + 2 by rfl, iter_add, h2, h2]
    have four : iter 4 c = c →
        (c = Rule30Open.Frames.EdgePeriodFour.rainA ∨ c = Rule30Open.Frames.EdgePeriodFour.rainB) := by
      intro h4
      have h4' : T (T (T (T c))) = c := h4
      rw [T_eq] at h4'
      exact (Rule30Open.Frames.EdgePeriodFour.period_four_iff c h0).mp h4'
    match a, ha with
    | 0, _ =>
      have h1 : T c = c := hp
      have := Rule30Open.Frames.EdgeOddPeriods.fixed_point_eq_zero c h1 0
      rw [h0] at this; exact absurd this (by decide)
    | 1, _ => exact ⟨by decide, four (h4of2 hp)⟩
    | 2, _ => exact ⟨by decide, four hp⟩
    | 3, _ =>
      refine ⟨by decide, ?_⟩
      have h8 : T (T (T (T (T (T (T (T c))))))) = c := hp
      rw [T_eq] at h8
      exact (Rule30Open.Frames.EdgePeriodEight.period_eight_iff c h0).mp h8
    | 4, _ =>
      refine ⟨by decide, ?_⟩
      have h16 : T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T c))))))))))))))) = c := hp
      rw [T_eq] at h16
      exact (Rule30Open.Frames.EdgePeriodSixteen.period_sixteen_iff c h0).mp h16
  · rintro ⟨ha1, hc⟩
    have h2 := rain_two c hc
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ b) 2, Nat.mul_assoc]
    exact iter_mul_of_period 2 c h2 _

end Rule30Open.Frames.EdgePeriods
