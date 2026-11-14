module

public import Rule30Open.Frames.LightReturnRows
public import Rule30Open.Frames.EdgePeriodSixteen

/-!
# The rows that come back at the speed of light after a time not divisible by 32

* `rain_of_return`: **a row white right of a black cell `r` that returns after `2 ^ a * q` steps moved
  `2 ^ a * q` cells right, with `q` odd and `a ≤ 4`, has the edge code `rainA` or `rainB` at `r`.** By
  `LightReturnRows.pow_two_return` it returns after `2 ^ a` steps, hence after 16, and
  `EdgePeriodSixteen.period_sixteen_iff` reads off the code.
* `rain_of_return_mod`, `rain_rows_of_return`: the same for every `L` with `L % 32 ≠ 0` (`factor_of_mod`), and the
  rows written out cell by cell.
* `white_or_rain_of_return`: without a black edge cell, the row is white or a rain row at its rightmost black cell
  (`rightmost_black`).
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

theorem factor_of_mod (L : Nat) (hL : L % 32 ≠ 0) : ∃ a q : Nat, a ≤ 4 ∧ q % 2 = 1 ∧ L = 2 ^ a * q := by
  by_cases h1 : L % 2 = 1
  · exact ⟨0, L, by omega, h1, by omega⟩
  by_cases h2 : L % 4 = 2
  · exact ⟨1, L / 2, by omega, by omega, by show L = 2 * (L / 2); omega⟩
  by_cases h3 : L % 8 = 4
  · exact ⟨2, L / 4, by omega, by omega, by show L = 4 * (L / 4); omega⟩
  by_cases h4 : L % 16 = 8
  · exact ⟨3, L / 8, by omega, by omega, by show L = 8 * (L / 8); omega⟩
  · exact ⟨4, L / 16, by omega, by omega, by show L = 16 * (L / 16); omega⟩

theorem rain_of_return_mod (init : Int → Bool) (r : Int) (hr : ∀ p, r < p → init p = false)
    (h0 : init r = true) (L : Nat) (hL : L % 32 ≠ 0) (h : ∀ x, evolve init L (x + (L : Int)) = init x) :
    codeAt init r = Rule30Open.Frames.EdgePeriodFour.rainA ∨
      codeAt init r = Rule30Open.Frames.EdgePeriodFour.rainB := by
  obtain ⟨a, q, ha, hq, rfl⟩ := factor_of_mod L hL
  exact rain_of_return init r hr h0 a q hq ha h

theorem rain_rows_of_return (init : Int → Bool) (r : Int) (hr : ∀ p, r < p → init p = false)
    (h0 : init r = true) (L : Nat) (hL : L % 32 ≠ 0) (h : ∀ x, evolve init L (x + (L : Int)) = init x) :
    (∀ k : Nat, init (r - k) = (k % 2 == 0)) ∨ (∀ k : Nat, init (r - k) = (k == 0 || k % 2 == 1)) := by
  rcases rain_of_return_mod init r hr h0 L hL h with hA | hB
  · exact Or.inl fun k => congrFun hA k
  · exact Or.inr fun k => congrFun hB k

theorem rightmost_black (init : Int → Bool) :
    ∀ n : Nat, ∀ s : Int, (∀ x, s < x → init x = false) → init (s - n) = true →
      ∃ r', init r' = true ∧ ∀ x, r' < x → init x = false := by
  intro n
  induction n with
  | zero =>
    intro s hs h
    exact ⟨s, by simpa using h, hs⟩
  | succ n ih =>
    intro s hs h
    by_cases hb : init s = true
    · exact ⟨s, hb, hs⟩
    · apply ih (s - 1)
      · intro x hx
        by_cases e : x = s
        · subst e; cases hx' : init x <;> simp_all
        · exact hs x (by omega)
      · have e : s - 1 - (n : Int) = s - ((n + 1 : Nat) : Int) := by omega
        rw [e]; exact h

theorem white_or_rain_of_return (init : Int → Bool) (r : Int) (hr : ∀ p, r < p → init p = false)
    (L : Nat) (hL : L % 32 ≠ 0) (h : ∀ x, evolve init L (x + (L : Int)) = init x) :
    (∀ x, init x = false) ∨
      ∃ r', init r' = true ∧ (∀ p, r' < p → init p = false) ∧
        (codeAt init r' = Rule30Open.Frames.EdgePeriodFour.rainA ∨
          codeAt init r' = Rule30Open.Frames.EdgePeriodFour.rainB) := by
  by_cases hw : ∃ p, init p = true
  · obtain ⟨p, hp⟩ := hw
    have hpr : p ≤ r := by
      by_cases c : r < p
      · rw [hr p c] at hp; exact absurd hp (by decide)
      · omega
    have e : r - (((r - p).toNat : Nat) : Int) = p := by omega
    obtain ⟨r', h1, h2⟩ := rightmost_black init (r - p).toNat r hr (by rw [e]; exact hp)
    exact Or.inr ⟨r', h1, h2, rain_of_return_mod init r' h2 h1 L hL h⟩
  · refine Or.inl fun x => ?_
    cases hx : init x
    · rfl
    · exact absurd ⟨x, hx⟩ hw

end Rule30Open.Frames.LightReturnClassified
