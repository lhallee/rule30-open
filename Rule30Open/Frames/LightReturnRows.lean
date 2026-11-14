module

public import Rule30Open.Foundations.Evolve
public import Rule30Open.Frames.EdgeOddPeriods

/-!
# Rows that come back moved at the speed of light

A row `init` white right of a cell `r` keeps white right of `r + t` at time `t`, and its edge code read from `r + t`,
bit `k` the cell `k` places left, evolves by the kit's edge map `Rule30FrozenRuler.T` (`code_evolve`; the cell `r`
need not be black).

* `odd_return_white`: **if `evolve init L (x + L) = init x` for every `x` and `L` is odd, the row is white.**
* `pow_two_return`: **if `evolve init (2 ^ a * q) (x + 2 ^ a * q) = init x` for every `x` and `q` is odd, then
  already `evolve init (2 ^ a) (x + 2 ^ a) = init x` for every `x`.**

Both follow from `EdgeOddPeriods.odd_period_eq_zero` and `EdgeOddPeriods.pow_two_period` through `code_evolve`.

The natural-language argument is `LightReturnRows.md`, beside this file.
-/

@[expose] public section

namespace Rule30Open.Frames.LightReturnRows

open Rule30Open
open Ruliology.CellularAutomata.Rule30FrozenRuler

/-- The edge code of a row read from cell `r`: bit `k` is the cell `k` places left of `r`. -/
def codeAt (x : Int → Bool) (r : Int) : Nat → Bool := fun k => x (r - k)

theorem code_evolve (init : Int → Bool) (r : Int) (hr : ∀ p, r < p → init p = false) :
    ∀ t : Nat, (∀ p, r + t < p → evolve init t p = false) ∧
      codeAt (evolve init t) (r + t) = iter t (codeAt init r)
  | 0 => by
    refine ⟨fun p hp => by simpa [evolve] using hr p (by omega), ?_⟩
    funext k; simp [codeAt, evolve, iter]
  | t + 1 => by
    obtain ⟨h2, h3⟩ := code_evolve init r hr t
    refine ⟨?_, ?_⟩
    · intro p hp
      show rule30 (evolve init t (p - 1)) (evolve init t p) (evolve init t (p + 1)) = false
      rw [h2 (p - 1) (by omega), h2 p (by omega), h2 (p + 1) (by omega)]
      rfl
    · show codeAt (evolve init (t + 1)) (r + ((t + 1 : Nat) : Int)) = T (iter t (codeAt init r))
      rw [← h3]
      funext k
      show rule30 (evolve init t (r + ((t + 1 : Nat) : Int) - k - 1))
        (evolve init t (r + ((t + 1 : Nat) : Int) - k))
        (evolve init t (r + ((t + 1 : Nat) : Int) - k + 1)) = T (codeAt (evolve init t) (r + t)) k
      match k with
      | 0 =>
        have a1 : r + ((t + 1 : Nat) : Int) - ((0 : Nat) : Int) - 1 = r + t := by omega
        have a2 : r + ((t + 1 : Nat) : Int) - ((0 : Nat) : Int) + 1 = r + t + 2 := by omega
        have a3 : r + ((t + 1 : Nat) : Int) - ((0 : Nat) : Int) = r + t + 1 := by omega
        rw [a1, a2, a3, h2 (r + t + 1) (by omega), h2 (r + t + 2) (by omega)]
        simp [T, codeAt, rule30]
      | 1 =>
        have a1 : r + ((t + 1 : Nat) : Int) - ((1 : Nat) : Int) - 1 = r + t - ((1 : Nat) : Int) := by
          omega
        have a2 : r + ((t + 1 : Nat) : Int) - ((1 : Nat) : Int) + 1 = r + t + 1 := by omega
        have a3 : r + ((t + 1 : Nat) : Int) - ((1 : Nat) : Int) = r + t - ((0 : Nat) : Int) := by
          omega
        rw [a1, a2, a3, h2 (r + t + 1) (by omega)]
        simp [T, codeAt, rule30]
      | j + 2 =>
        have a1 : r + ((t + 1 : Nat) : Int) - ((j + 2 : Nat) : Int) - 1 =
            r + t - ((j + 2 : Nat) : Int) := by omega
        have a2 : r + ((t + 1 : Nat) : Int) - ((j + 2 : Nat) : Int) + 1 =
            r + t - ((j : Nat) : Int) := by omega
        have a3 : r + ((t + 1 : Nat) : Int) - ((j + 2 : Nat) : Int) =
            r + t - ((j + 1 : Nat) : Int) := by omega
        rw [a1, a2, a3]
        simp [T, codeAt, rule30]

/-- A return moved `L` cells right makes the edge code `L`-periodic. -/
theorem iter_code_of_return (init : Int → Bool) (r : Int) (hr : ∀ p, r < p → init p = false) (L : Nat)
    (h : ∀ x, evolve init L (x + L) = init x) : iter L (codeAt init r) = codeAt init r := by
  rw [← (code_evolve init r hr L).2]
  funext k
  show evolve init L (r + L - k) = init (r - k)
  have e : r + (L : Int) - k = (r - k) + L := by omega
  rw [e, h]

theorem odd_return_white (init : Int → Bool) (r : Int) (hr : ∀ p, r < p → init p = false) (L : Nat)
    (hL : L % 2 = 1) (h : ∀ x, evolve init L (x + L) = init x) : ∀ x, init x = false := by
  have hc := EdgeOddPeriods.odd_period_eq_zero (codeAt init r) L hL (iter_code_of_return init r hr L h)
  intro x
  by_cases hx : r < x
  · exact hr x hx
  · have := hc (r - x).toNat
    simp only [codeAt] at this
    have e : r - ((r - x).toNat : Int) = x := by omega
    rwa [e] at this

theorem pow_two_return (init : Int → Bool) (r : Int) (hr : ∀ p, r < p → init p = false) (a q : Nat)
    (hq : q % 2 = 1) (h : ∀ x, evolve init (2 ^ a * q) (x + ((2 ^ a * q : Nat) : Int)) = init x) :
    ∀ x, evolve init (2 ^ a) (x + ((2 ^ a : Nat) : Int)) = init x := by
  have hc := EdgeOddPeriods.pow_two_period (codeAt init r) a q hq
    (iter_code_of_return init r hr (2 ^ a * q) h)
  have hb := code_evolve init r hr (2 ^ a)
  rw [hc] at hb
  intro x
  by_cases hx : r < x
  · rw [hr x hx]
    exact hb.1 _ (by omega)
  · have := congrFun hb.2 (r - x).toNat
    simp only [codeAt] at this
    have e1 : r + ((2 ^ a : Nat) : Int) - ((r - x).toNat : Int) = x + ((2 ^ a : Nat) : Int) := by omega
    have e2 : r - ((r - x).toNat : Int) = x := by omega
    rwa [e1, e2] at this

end Rule30Open.Frames.LightReturnRows
